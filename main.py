import asyncio
import json
import os
import time
from typing import List, Optional, Tuple
from datetime import datetime
from urllib.parse import parse_qsl, urlparse

import httpx
from websockets.asyncio.client import connect

from astrbot.api import logger, AstrBotConfig
from astrbot.api.event import filter, AstrMessageEvent, MessageChain
from astrbot.api.star import Context, Star, StarTools


VERSION = "1.3.1"
USER_AGENT = f"astrbot-ret2shell/{VERSION}"

# 服务端 Event 枚举的 5 个外部标签，顺序需与 crates/event/src/events.rs 保持一致
EVENT_KINDS = ("challenge", "submission", "game", "chat", "devops")

DEFAULT_EVENTS = [
    "challenge_up", "challenge_down", "new_hint",
    "blood_1", "blood_2", "blood_3",
    "correct", "cheated", "too_quick", "chat_message",
    "new_notification", "freeze", "unfreeze",
    "cluster_overloaded", "cluster_recovered", "server_panic",
]

RECONNECT_BASE_DELAY = 1.0
RECONNECT_MAX_DELAY = 60.0
NOTIFICATION_RECONCILE_INTERVAL = 60.0
GAME_NAME_CACHE_TTL = 1800
NETWORK_ERROR = 0

STATE_FILE_NAME = "notification_state.json"

# 停机后重启时，待补通知超过这个数量就只重建基线、不补播，避免刷屏
MAX_STARTUP_COMPENSATION = 10

_state_file_path: Optional[str] = None
_state_file_resolved = False


def resolve_state_file() -> Optional[str]:
    """返回通知状态文件的绝对路径；拿不到官方数据目录时返回 None。

    持久化只允许写进 AstrBot 的插件数据目录（data/plugin_data/<plugin>）。
    它依赖 star_map 里的插件元数据，只能在插件加载之后调用、不能在导入期
    调用，因此这里惰性解析并缓存。解析失败就放弃落盘、退回纯内存状态：
    写到插件自身目录的数据会在更新/重装时丢失，也脱离 AstrBot 的统一备份。
    """
    global _state_file_path, _state_file_resolved
    if _state_file_resolved:
        return _state_file_path
    _state_file_resolved = True

    try:
        base = str(StarTools.get_data_dir() or "")
    except Exception as e:
        logger.error(f"❌ 获取 AstrBot 插件数据目录失败: {e}")
        base = ""

    if not base:
        logger.error(
            "❌ 没有可用的插件数据目录，通知状态只保存在内存中；"
            "重启后无法补播停机期间遗漏的通知"
        )
        return None

    _state_file_path = os.path.join(base, STATE_FILE_NAME)
    logger.info(f"📢 通知状态文件: {_state_file_path}")
    return _state_file_path


def mask_ws_url(url) -> str:
    """脱敏 WebSocket 链接，供日志与群消息输出。

    查询串里的 token 是赛事级凭据，拿到它就能伪造事件推送。除 game_id
    （状态命令本来就会单独展示、也算不上凭据）外，参数值一律替换为 ***。
    """
    if not isinstance(url, str) or not url:
        return "未配置"
    try:
        parsed = urlparse(url)
    except Exception:
        return "(无法解析的 WebSocket 链接)"
    if not parsed.query:
        return url
    query = "&".join(
        f"{key}={value}" if key == "game_id" else f"{key}=***"
        for key, value in parse_qsl(parsed.query, keep_blank_values=True)
    )
    return f"{url.split('?', 1)[0]}?{query}"


def describe_http_status(status: int) -> str:
    if status == NETWORK_ERROR:
        return "❌ 网络请求失败，请检查与 Ret2Shell 的连通性。"
    if status == 401:
        return (
            "❌ 该功能需要登录权限。请在插件配置中填写 ret2shell_account 与 "
            "ret2shell_password（办赛方账号）。"
        )
    if status == 403:
        return "❌ 权限不足：该功能需要办赛方账号，或比赛当前处于冻结 / 题目未发布状态。"
    if status == 412:
        return "❌ 比赛尚未开始。"
    if status == 404:
        return "❔ 未找到。"
    if status == 429:
        return "❌ 请求过于频繁，请稍后再试。"
    return f"❌ 请求失败（HTTP {status}）。"


class Ret2ShellPlugin(Star):
    """Ret2Shell 赛事事件播报插件。

    元数据（名称/作者/版本/仓库等）由 metadata.yaml 提供，Star.__init_subclass__
    会自动完成插件注册，因此这里不再使用已废弃的 @register 装饰器。
    """
    def __init__(self, context: Context, config: AstrBotConfig = None):
        super().__init__(context)

        self.config = config or {}
        self.ws_url = self.config.get("ret2shell_ws_link", "")
        self.public_umo = self._normalize_list(self.config.get("public_umo", []))
        self.admin_umo = self._normalize_list(self.config.get("admin_umo", []))
        self.ops_umo = self._normalize_list(self.config.get("ops_umo", []))

        self.account = self._normalize_scalar(self.config.get("ret2shell_account", ""))
        self.password = self._normalize_scalar(self.config.get("ret2shell_password", ""))

        self.enabled_events = self.config.get("enabled_events", DEFAULT_EVENTS)
        if not self.enabled_events:
            self.enabled_events = DEFAULT_EVENTS

        self.client: Optional[httpx.AsyncClient] = None
        self.api_base_url = ""
        self.game_id = ""
        self.authenticated = False

        self.ws_task = None
        self.watchdog_task = None
        self.running = False
        self._game_start_time = None
        self._game_end_time = None

        self._game_name_cache = None
        self._game_name_cache_time = 0

        self._disconnected_at: Optional[float] = None
        self._notify_lock: Optional[asyncio.Lock] = None
        self._seen_notification_ids = set()
        self._notification_baseline_ready = False

        logger.info(f"🔍 ws_url 已配置: {bool(self.ws_url)}")
        logger.info(f"📢 public_umo: {self.public_umo}")
        logger.info(f"🔔 admin_umo: {self.admin_umo}")
        logger.info(f"🔧 ops_umo: {self.ops_umo}")
        logger.info(f"🔘 已开启事件: {len(self.enabled_events)} 项")

    def _normalize_list(self, value) -> List[str]:
        if isinstance(value, str):
            if "," in value:
                return [v.strip() for v in value.split(",") if v.strip()]
            return [value] if value.strip() else []
        if isinstance(value, list):
            return [str(v).strip() for v in value if str(v).strip()]
        return []

    def _normalize_scalar(self, value) -> str:
        return value.strip() if isinstance(value, str) else ""

    async def initialize(self):
        logger.info("🚀 Ret2Shell 插件开始加载...")

        if not self.ws_url:
            logger.error("❌ ret2shell_ws_link 未配置，插件不会启动")
            return

        if not await self._init_http_api():
            return

        self._notify_lock = asyncio.Lock()

        # 通知基线必须早于 WebSocket 启动：基线未就绪时收到的通知只能直接播报，
        # 无法再参与去重。优先用落盘状态（上次运行的事实），拿不到才退回本次快照
        catch_up = False
        if self.authenticated:
            if self._load_notification_state():
                catch_up = True
            else:
                await self._seed_notification_baseline()

        await self._schedule_game_timers()

        self.running = True
        self.ws_task = asyncio.create_task(self._ws_loop())
        if self.authenticated:
            self.watchdog_task = asyncio.create_task(self._notification_watchdog())
            if catch_up:
                asyncio.create_task(self._startup_reconcile())
        logger.info("✅ WebSocket 任务已启动")

    # ============ HTTP API ============

    async def _init_http_api(self) -> bool:
        urlparsed = urlparse(self.ws_url)
        game_id = dict(parse_qsl(urlparsed.query)).get("game_id") or ""
        if not game_id.isdigit():
            logger.error(f"❌ 无法从 WebSocket 链接解析出 game_id: {mask_ws_url(self.ws_url)}")
            return False

        scheme = urlparsed.scheme
        self.game_id = game_id
        self.api_base_url = f'{"https" if scheme == "wss" else "http"}://{urlparsed.netloc}/api'

        if self.account and self.password:
            auth = (self.account, self.password)
        else:
            auth = None
            if self.account or self.password:
                logger.warning(
                    "⚠️ ret2shell_account 与 ret2shell_password 需同时填写才生效，"
                    "当前按匿名模式运行（/challenge 等需要登录的功能不可用）"
                )
        self.authenticated = auth is not None

        self.client = httpx.AsyncClient(
            base_url=self.api_base_url,
            headers={"User-Agent": USER_AGENT},
            auth=auth,
            timeout=httpx.Timeout(10.0),
        )

        logger.info(f"🎯 HTTP API: {self.api_base_url}, game_id: {self.game_id}")
        logger.info(f"🔐 平台鉴权: {'已启用' if self.authenticated else '未启用（匿名只读）'}")
        return True

    async def _http_get(self, path: str) -> Tuple[Optional[object], int]:
        """返回 (响应体, HTTP 状态码)。网络异常时状态码为 NETWORK_ERROR。"""
        if not self.client or not self.game_id:
            return None, NETWORK_ERROR
        try:
            resp = await self.client.get(path)
        except Exception as e:
            logger.error(f"HTTP 请求失败 {path}: {e}")
            return None, NETWORK_ERROR
        if resp.status_code != 200:
            logger.warning(f"HTTP {resp.status_code} for {path}")
            return None, resp.status_code
        try:
            return resp.json(), 200
        except Exception as e:
            logger.error(f"响应解析失败 {path}: {e}")
            return None, NETWORK_ERROR

    @staticmethod
    def _tag_name(challenge: dict) -> str:
        tags = challenge.get("tag") or []
        if tags and isinstance(tags[0], dict):
            return tags[0].get("name") or "未知"
        return "未知"

    # ============ 定时播报 ============

    async def _schedule_game_timers(self):
        """获取赛事起止时间，安排定时播报"""
        data, status = await self._http_get(f"/game/{self.game_id}")
        if status != 200 or not isinstance(data, dict):
            logger.error(f"❌ 获取赛事时间失败（HTTP {status}）")
            return
        start_at = data.get("start_at")
        end_at = data.get("end_at")
        if start_at:
            self._game_start_time = datetime.fromtimestamp(start_at)
            logger.info(f"📅 比赛开始时间: {self._game_start_time}")
            delay = start_at - time.time()
            if delay > 0:
                asyncio.create_task(self._delayed_game_start(delay))
        if end_at:
            self._game_end_time = datetime.fromtimestamp(end_at)
            logger.info(f"📅 比赛结束时间: {self._game_end_time}")
            delay = end_at - time.time()
            if delay > 0:
                asyncio.create_task(self._delayed_game_end(delay))

    async def _get_game_name(self) -> str:
        """获取赛事名称（带缓存，避免每条事件都请求 API）"""
        now = time.time()
        if self._game_name_cache and (now - self._game_name_cache_time) < GAME_NAME_CACHE_TTL:
            return self._game_name_cache
        data, status = await self._http_get(f"/game/{self.game_id}")
        if status == 200 and isinstance(data, dict) and data.get("name"):
            self._game_name_cache = data["name"]
            self._game_name_cache_time = now
            return self._game_name_cache
        return self._game_name_cache or "Ret2Shell 赛事"

    async def _delayed_game_start(self, delay: float):
        await asyncio.sleep(delay)
        await self._dispatch(f"🚀 【{await self._get_game_name()}】比赛已开始！", "public")

    async def _delayed_game_end(self, delay: float):
        await asyncio.sleep(delay)
        await self._dispatch(f"🏁 【{await self._get_game_name()}】比赛已结束！", "public")

    async def _dispatch(self, message: str, msg_type: str):
        if not message:
            return
        targets = {
            "public": self.public_umo,
            "admin": self.admin_umo,
            "ops": self.ops_umo,
        }.get(msg_type, [])
        for umo in targets:
            try:
                await self.context.send_message(umo, MessageChain().message(message))
                logger.info(f"✅ [{msg_type}] 消息已推送到 {umo}")
            except Exception as e:
                logger.error(f"❌ 推送到 {umo} 失败: {e}")

    # ============ 通知补偿 ============

    def _mark_notifications_seen(self, items):
        for item in items:
            if isinstance(item, dict) and item.get("id") is not None:
                self._seen_notification_ids.add(item["id"])

    def _compensation_status(self) -> str:
        if not self.authenticated:
            return "⚪ 不可用（未配置账号）"
        if not self._notification_baseline_ready:
            return "🟡 已启用，但基线未建立（当前直接播报，暂不去重）"
        return f"🟢 已启用（已记录 {len(self._seen_notification_ids)} 条）"

    def _load_notification_state(self) -> bool:
        """从状态文件恢复已见通知 id。

        恢复成功意味着我们参考的是「上次运行的事实」而不是「本次启动的快照」，
        因此停机期间新增的通知也能被补上，启动时也不存在需要「建基线」的窗口。
        """
        path = resolve_state_file()
        if path is None:
            logger.info("📢 通知状态无处落盘，按首次运行处理")
            return False
        try:
            with open(path, encoding="utf-8") as f:
                state = json.load(f)
        except FileNotFoundError:
            logger.info("📢 未找到通知状态文件，按首次运行处理")
            return False
        except Exception as e:
            logger.warning(f"⚠️ 通知状态文件不可读，按首次运行处理: {e}")
            return False

        if not isinstance(state, dict) or str(state.get("game_id")) != self.game_id:
            logger.info("📢 通知状态与本场比赛不匹配，按首次运行处理")
            return False

        ids = state.get("seen_ids")
        if not isinstance(ids, list):
            logger.warning("⚠️ 通知状态文件格式异常，按首次运行处理")
            return False

        self._seen_notification_ids = {i for i in ids if isinstance(i, int)}
        self._notification_baseline_ready = True
        logger.info(
            f"📢 已恢复通知状态（{len(self._seen_notification_ids)} 条，"
            f"上次保存 {state.get('saved_at', '未知')}），将补上停机期间的新通知"
        )
        return True

    def _save_notification_state(self):
        path = resolve_state_file()
        if path is None:
            # 原因已在 resolve_state_file 里说明过，这里静默跳过以免反复刷日志
            return
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            tmp = f"{path}.tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(
                    {
                        "game_id": self.game_id,
                        "saved_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                        "seen_ids": sorted(self._seen_notification_ids),
                    },
                    f,
                    ensure_ascii=False,
                )
            os.replace(tmp, path)
        except Exception as e:
            logger.error(f"❌ 通知状态保存失败（不影响本次播报）: {e}")

    async def _seed_notification_baseline(self) -> bool:
        """首次运行时建立通知基线。

        没有任何历史参照，只能以启动时刻的列表为界：这些视为历史、不播报。
        建立失败时退回「直接播报」模式，通知仍然不会漏，只是暂时没有去重能力。
        """
        for attempt, delay in enumerate((0, 2, 5)):
            if delay:
                await asyncio.sleep(delay)
            data, status = await self._http_get(f"/game/{self.game_id}/notification")
            if status == 200 and isinstance(data, list):
                self._mark_notifications_seen(data)
                self._notification_baseline_ready = True
                self._save_notification_state()
                logger.info(
                    f"📢 通知基线已建立（{len(self._seen_notification_ids)} 条历史通知不播报）"
                )
                return True
            logger.warning(f"⚠️ 建立通知基线失败（HTTP {status}），第 {attempt + 1}/3 次尝试")
        logger.error("❌ 通知基线建立失败；在补齐基线前，通知将直接播报且不做补偿")
        return False

    async def _startup_reconcile(self):
        """启动后补上停机期间遗漏的通知。"""
        try:
            await self._reconcile_notifications(startup=True)
        except Exception as e:
            logger.error(f"❌ 启动对账异常: {e}")

    async def _reconcile_notifications(self, startup: bool = False):
        """以 REST 通知列表为唯一事实来源，按 id 去重补播。

        服务端的 new_notification 事件只带标题、不带通知 id，无法靠事件本身
        去重，所以这里拉全量列表比对。
        """
        if not self.authenticated or not self.running or self._notify_lock is None:
            return
        async with self._notify_lock:
            data, status = await self._http_get(f"/game/{self.game_id}/notification")
            if status != 200 or not isinstance(data, list):
                logger.error(f"❌ 通知对账失败（HTTP {status}），将在下次对账时重试")
                return

            if not self._notification_baseline_ready:
                # 首次运行且启动快照没拿到：没有历史参照，只能全部记为既知，
                # 这一窗口内的通知已在 _handle_message 里直接播报过
                self._mark_notifications_seen(data)
                self._notification_baseline_ready = True
                self._save_notification_state()
                logger.info(f"📢 通知基线已补齐（{len(self._seen_notification_ids)} 条）")
                return

            pending = [
                item for item in data
                if isinstance(item, dict)
                and item.get("id") is not None
                and item["id"] not in self._seen_notification_ids

            ]
            pending.sort(key=lambda item: item.get("published_at") or 0)

            if startup and len(pending) > MAX_STARTUP_COMPENSATION:
                logger.warning(
                    f"⚠️ 停机时间较长（{len(pending)} 条待补通知），"
                    "为避免刷屏只重建基线、不补播"
                )
                self._mark_notifications_seen(data)
                self._save_notification_state()
                return

            if pending:
                logger.warning(f"🔁 补偿 {len(pending)} 条遗漏的通知")
            for item in pending:
                self._seen_notification_ids.add(item["id"])
                title = item.get("title") or ""
                if title:
                    game_name = await self._get_game_name()
                    await self._dispatch(f"【{game_name}】\n📢 新通知：{title}", "public")
            if pending:
                self._save_notification_state()

    async def _notification_watchdog(self):
        while self.running:
            await asyncio.sleep(NOTIFICATION_RECONCILE_INTERVAL)
            if not self.running:
                break
            try:
                await self._reconcile_notifications()
            except Exception as e:
                logger.error(f"❌ 通知对账异常: {e}")

    # ============ WebSocket ============

    async def _ws_loop(self):
        backoff = RECONNECT_BASE_DELAY
        first_connect = True
        while self.running:
            try:
                logger.info(f"🔌 正在连接 Ret2Shell: {mask_ws_url(self.ws_url)}")
                async with connect(self.ws_url) as websocket:
                    logger.info("✅ Ret2Shell WebSocket 连接成功！")
                    backoff = RECONNECT_BASE_DELAY

                    if not first_connect and self._disconnected_at is not None:
                        gap = time.time() - self._disconnected_at
                        logger.warning(
                            f"🔁 已重连，断线约 {gap:.1f} 秒；"
                            "该时段内除通知外的赛事事件无法补发"
                        )
                        await self._reconcile_notifications()
                    first_connect = False
                    self._disconnected_at = None

                    async for raw_message in websocket:
                        await self._handle_message(raw_message)
            except asyncio.CancelledError:
                logger.info("⏹️ WebSocket 任务被取消")
                break
            except Exception as e:
                logger.error(f"❌ WebSocket 连接断开: {e}")

            self._disconnected_at = time.time()
            if not self.running:
                break
            # 服务端关闭慢客户端时会正常结束连接而不抛异常，这里同样退避，
            # 否则会变成不断重连的紧密循环
            logger.info(f"⏳ {backoff:.0f} 秒后重连...")
            await asyncio.sleep(backoff)
            backoff = min(backoff * 2, RECONNECT_MAX_DELAY)

    async def _handle_message(self, raw_message: str):
        try:
            data = json.loads(raw_message)
        except json.JSONDecodeError:
            logger.warning(f"⚠️ 无法解析 JSON: {raw_message[:100]}")
            return
        if not isinstance(data, dict):
            return

        event_kind = next((kind for kind in EVENT_KINDS if kind in data), None)
        if event_kind is None:
            logger.warning(f"⚠️ 未知事件类型: {list(data.keys())}")
            return
        event_data = data[event_kind] or {}

        event_type_key = self._get_event_type(event_kind, event_data)
        if event_type_key not in self.enabled_events:
            logger.debug(f"⏭️ 事件 {event_type_key} 已关闭，跳过推送")
            return

        if event_kind == "game" and event_data.get("event_type") == "new_notification":
            # 基线建立后才交给对账，复用同一套 id 去重；基线未建立时
            # 直接播报，宁可暂时不能去重也不能漏
            if self.authenticated and self._notification_baseline_ready:
                await self._reconcile_notifications()
                return

        msg, msg_type = await self._format_event_message(event_kind, event_data)
        await self._dispatch(msg, msg_type)

    def _get_event_type(self, event_kind: str, event_data: dict) -> str:
        """提取事件类型标识符，用于开关判断"""
        event_type = event_data.get("event_type", "unknown")
        if event_kind == "challenge":
            return {
                "up": "challenge_up",
                "down": "challenge_down",
                "new_hint": "new_hint",
            }.get(event_type, event_type)
        if event_kind == "submission":
            if event_type == "correct":
                blood_state = event_data.get("blood_state")
                if blood_state in (1, 2, 3):
                    return f"blood_{blood_state}"
                return "correct"
            return event_type
        if event_kind == "chat":
            return f"chat_{event_type}"
        if event_kind in ("game", "devops"):
            return event_type
        return "unknown"

    async def _format_event_message(self, event_kind: str, event_data: dict):
        """格式化事件消息，返回 (消息内容, 消息类型)"""
        msg_type = "public"

        game_name = await self._get_game_name()

        lines = [f"【{game_name}】"]

        if event_kind == "challenge":
            challenge = event_data.get("challenge") or {}
            event_type = event_data.get("event_type", "unknown")
            tag_name = self._tag_name(challenge)
            challenge_name = challenge.get("name", "未知")

            if event_type == "up":
                lines.append(f"⬆️ [{tag_name}] 新题目上线：{challenge_name}")
            elif event_type == "down":
                lines.append(f"⬇️ [{tag_name}] 题目下线：{challenge_name}")
            elif event_type == "new_hint":
                lines.append(f"💡 [{tag_name}] {challenge_name} 发布了新提示")

        elif event_kind == "submission":
            team = event_data.get("team") or {}
            challenge = event_data.get("challenge") or {}
            event_type = event_data.get("event_type", "unknown")
            blood_state = event_data.get("blood_state")
            tag_name = self._tag_name(challenge)
            challenge_name = challenge.get("name", "未知")
            team_name = team.get("name", "未知")

            if event_type == "correct":
                if blood_state == 1:
                    lines.append(f"🎉 恭喜 {team_name} 获得 [{tag_name}] {challenge_name} 一血！🥇")
                elif blood_state == 2:
                    lines.append(f"🎉 恭喜 {team_name} 获得 [{tag_name}] {challenge_name} 二血！🥈")
                elif blood_state == 3:
                    lines.append(f"🎉 恭喜 {team_name} 获得 [{tag_name}] {challenge_name} 三血！🥉")
                else:
                    lines.append(f"✅ {team_name} 解出了 [{tag_name}] {challenge_name}")
                    msg_type = "admin"
                for milestone in event_data.get("milestones") or []:
                    milestone_name = (milestone or {}).get("name")
                    if milestone_name:
                        lines.append(f"🏅 {team_name} 达成里程碑：{milestone_name}")

            elif event_type == "cheated":
                peer_team = event_data.get("peer_team") or {}
                peer_team_name = peer_team.get("name", "未知队伍")
                lines = [f"🚨【{game_name}】检测到作弊行为！！!"]
                lines.append(f"🤥 {team_name} 提交了 {peer_team_name} 的 [{tag_name}] {challenge_name} 题目的 flag")
                msg_type = "admin"

            elif event_type == "too_quick":
                lines.append(f"💥 {team_name} 提交 [{tag_name}] {challenge_name} 过快！")
                msg_type = "admin"

        elif event_kind == "game":
            event_type = event_data.get("event_type", "unknown")
            if event_type == "new_notification":
                lines.append(f"📢 新通知：{event_data.get('message', '')}")
            elif event_type == "freeze":
                lines.append("🧊 比赛已冻结")
            elif event_type == "unfreeze":
                lines.append("🌊 比赛已解冻")

        elif event_kind == "chat":
            team = event_data.get("team") or {}
            challenge = event_data.get("challenge") or {}
            content = event_data.get("content", "")
            tag_name = self._tag_name(challenge)
            challenge_name = challenge.get("name", "未知")
            team_name = team.get("name", "未知")
            lines.append(f"✉️ {team_name} 对 [{tag_name}] {challenge_name} 发送了反馈：")
            lines.append(content[:200])
            msg_type = "admin"

        elif event_kind == "devops":
            event_type = event_data.get("event_type", "unknown")
            if event_type == "cluster_overloaded":
                lines.append("⚠️ 集群超载")
            elif event_type == "cluster_recovered":
                lines.append("✅ 集群恢复")
            elif event_type == "server_panic":
                lines.append("🔥 服务崩溃")
            msg_type = "ops"

        else:
            lines.append(f"📌 类型: {event_kind}")
            lines.append(json.dumps(event_data, ensure_ascii=False, indent=2)[:300])

        return "\n".join(lines), msg_type

    # ============ 指令 ============

    def _not_ready_message(self) -> Optional[str]:
        if not self.game_id:
            return "❌ 未配置有效的 WebSocket 链接"
        return None

    @filter.command("game")
    async def query_game(self, event: AstrMessageEvent):
        if msg := self._not_ready_message():
            yield event.plain_result(msg)
            return

        data, status = await self._http_get(f"/game/{self.game_id}")
        if status == 404:
            yield event.plain_result("❔ 找不到该赛事（可能未公开）。")
            return
        if status != 200 or not isinstance(data, dict):
            yield event.plain_result(describe_http_status(status))
            return

        name = data.get("name", "未知")
        brief = data.get("brief", "")
        start_at = data.get("start_at", 0)
        end_at = data.get("end_at", 0)
        start_str = time.strftime("%Y/%m/%d %H:%M", time.localtime(start_at)) if start_at else "未知"
        end_str = time.strftime("%Y/%m/%d %H:%M", time.localtime(end_at)) if end_at else "未知"

        msg = f"""🚩 赛事: {name}
📝 简介: {brief}
🕐 时间: {start_str} - {end_str}
🔗 链接: {self.api_base_url.replace('/api', '')}/games/{self.game_id}"""
        yield event.plain_result(msg)

    @filter.command("rank")
    async def query_rank(self, event: AstrMessageEvent):
        """查询积分排行前十"""
        if msg := self._not_ready_message():
            yield event.plain_result(msg)
            return

        data, status = await self._http_get(
            f"/game/{self.game_id}/team?page=1&page_size=10&order=score&asc=false&min_state=3"
        )
        if status != 200 or not isinstance(data, list):
            yield event.plain_result(describe_http_status(status))
            return

        teams = data[0] if data and isinstance(data[0], list) else []
        if not teams:
            yield event.plain_result("🏆 暂无队伍得分")
            return

        lines = ["🏆 积分板"]
        medals = ["🥇", "🥈", "🥉"]
        for i, t in enumerate(teams):
            medal = medals[i] if i < 3 else f"{i + 1}."
            lines.append(f"{medal} {t.get('name', '未知')}: {t.get('score', 0)} pts")

        yield event.plain_result("\n".join(lines))

    @filter.command("challenge")
    async def query_challenge(self, event: AstrMessageEvent):
        """查询题目详情：/challenge [题目ID]"""
        if msg := self._not_ready_message():
            yield event.plain_result(msg)
            return

        if not self.authenticated:
            yield event.plain_result(
                "❌ 该功能需要登录权限。请在插件配置中填写 ret2shell_account 与 "
                "ret2shell_password（办赛方账号）。"
            )
            return

        args = event.message_str.strip().split()
        if len(args) < 2:
            yield event.plain_result("❔ 请输入题目 ID，用法: /challenge 123")
            return

        try:
            challenge_id = int(args[1])
        except ValueError:
            yield event.plain_result("❌ 题目 ID 必须是数字")
            return

        data, status = await self._http_get(f"/game/{self.game_id}/challenge/{challenge_id}")
        if status == 404:
            yield event.plain_result("❔ 找不到该题目。")
            return
        if status == 403:
            yield event.plain_result("❌ 权限不足：比赛可能处于冻结状态，或该题目尚未发布。")
            return
        if status == 412:
            yield event.plain_result("❌ 比赛尚未开始。")
            return
        if status != 200 or not isinstance(data, dict):
            yield event.plain_result(describe_http_status(status))
            return

        if data.get("hidden"):
            yield event.plain_result("🏳️ 该题目未公开。")
            return

        name = data.get("name", "未知")
        tag_name = self._tag_name(data)
        score = data.get("score", 0)

        submit_data, submit_status = await self._http_get(
            f"/game/{self.game_id}/challenge/{challenge_id}/submit"
        )
        if submit_status == 200 and isinstance(submit_data, dict):
            solves = submit_data.get("solves", 0)
        else:
            solves = "未知"

        msg = f"""🎯 题目: [{name}]
🏷️ 方向: [{tag_name}]
📊 当前分数: {score} pts
👥 已解出数: {solves}"""
        yield event.plain_result(msg)

    @filter.command("team")
    async def query_team(self, event: AstrMessageEvent):
        """查询队伍详情：/team [队伍ID]"""
        if msg := self._not_ready_message():
            yield event.plain_result(msg)
            return

        args = event.message_str.strip().split()
        if len(args) < 2:
            yield event.plain_result("❔ 请输入队伍 ID，用法: /team 123")
            return

        try:
            team_id = int(args[1])
        except ValueError:
            yield event.plain_result("❌ 队伍 ID 必须是数字")
            return

        data, status = await self._http_get(f"/game/{self.game_id}/team/{team_id}")
        if status == 404:
            yield event.plain_result("❔ 找不到该队伍。")
            return
        if status != 200 or not isinstance(data, dict):
            yield event.plain_result(describe_http_status(status))
            return

        name = data.get("name", "未知")
        tag = data.get("tag")
        score = data.get("score", 0)

        rank_data, rank_status = await self._http_get(
            f"/game/{self.game_id}/team/{team_id}/rank"
        )
        rank = rank_data if rank_status == 200 else "未知"

        msg = f"""🧑‍💻 队伍: [{name}]
{'' if tag is None else f'🏷️ 标签: {tag}\n'}📊 当前分数: {score} pts
📈 当前排名: {rank}"""
        yield event.plain_result(msg)

    @filter.command("ret2shell_status")
    async def status(self, event: AstrMessageEvent):
        persist = '🟢 已启用' if resolve_state_file() else '🟡 不可用（仅内存）'
        status_msg = f"""
📊 Ret2Shell 插件状态:
- 版本: {VERSION}
- WebSocket 连接: {'🟢 运行中' if self.running else '🔴 已停止'}
- WS 地址: {mask_ws_url(self.ws_url)}
- Game ID: {self.game_id or '未解析'}
- 平台鉴权: {'🟢 已启用' if self.authenticated else '⚪ 未启用（匿名只读）'}
- 通知补偿: {self._compensation_status()}
- 状态落盘: {persist}
- 公开目标: {self.public_umo or '未配置'}
- 管理目标: {self.admin_umo or '未配置'}
- 运维目标: {self.ops_umo or '未配置'}
- 比赛开始: {self._game_start_time.strftime('%Y-%m-%d %H:%M') if self._game_start_time else '未获取'}
- 比赛结束: {self._game_end_time.strftime('%Y-%m-%d %H:%M') if self._game_end_time else '未获取'}
- 已开启事件: {len(self.enabled_events)} 项
        """.strip()
        yield event.plain_result(status_msg)

    async def terminate(self):
        self.running = False
        for task in (self.ws_task, self.watchdog_task):
            if task and not task.done():
                task.cancel()
                try:
                    await task
                except Exception:
                    pass
        if self.client:
            await self.client.aclose()
        logger.info("🔌 Ret2Shell 插件已清理")
