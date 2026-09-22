# -*- coding: utf-8 -*-
"""
祝尼魔桌面宠物 (Junimo Desktop Pet)
====================================
一只住在小屋里的星露谷祝尼魔：
  * 在小屋附近散步、发呆、头顶冒表情
  * 可以抓起来拖到屏幕任何地方（拖拽时=困扰）
  * 单击它会开心地蹦跳
  * 双击它会弹出「今日待办」：可添加/勾选/删除，到点用它头顶的感叹号提醒你
  * 三击小屋：祝尼魔立刻躲进去（直接消失）
  * 双击小屋：祝尼魔立刻从小屋里出来
  * 鼠标在它旁边停留，它会凑过来蹭一蹭，或者害羞地跑开
  * 拖动小屋搬家时，它会一路小跑跟着走过去
  * 电脑闲置太久 / 深夜它会走回小屋睡觉，有动静就醒

运行：双击「启动祝尼魔.bat」，或 python junimo_pet.py
退出：托盘图标右键 -> 退出
"""

import json
import math
import os
import random
import sys
import time
import traceback
from datetime import datetime, timedelta

from PySide6.QtCore import QPoint, QTime, Qt, QEvent, QLockFile, QTimer, QDate
from PySide6.QtGui import QAction, QCursor, QColor, QFont, QIcon, QImage, QImageReader, QPainter, QPen, QPixmap
from PySide6.QtWidgets import (QApplication, QCalendarWidget, QCheckBox, QFrame, QHBoxLayout, QLabel,
                               QLineEdit, QMenu, QMessageBox, QPushButton, QScrollArea,
                               QSystemTrayIcon, QTableView, QTimeEdit, QVBoxLayout, QWidget)

# ----------------------------------------------------------------------------
# 可调参数（改完保存重新运行即可生效）
# ----------------------------------------------------------------------------
SCALE = 2                    # 祝尼魔放大倍数，原图 48x48，2 倍 = 96px
PET_W = 48 * SCALE           # 窗口和身体一样大，点击区域就是祝尼魔本身
HUT_NATIVE = 100             # 小屋原图里单只小屋的宽度（400x113 四只一排）
EMOTE_SIZE = 46              # 头顶表情的显示尺寸
EMOTE_SECONDS = 2.2          # 表情停留时长

TICK_MS = 100                # 状态机心跳，毫秒
ANIM_MS = 150                # GIF 播放帧间隔
WALK_SPEED = 3               # 散步速度（像素/心跳）
SHY_SPEED = 6                # 害羞跑开速度
WANDER_RADIUS = 260          # 在小屋左右多大范围里散步

IDLE_DOZE_S = 600            # 鼠标键盘闲置多少秒后睡觉
IDLE_SAD_S = 300             # 闲置多少秒后先冒一个「无语」
NIGHT_START, NIGHT_END = 23, 8  # 晚上 23 点提醒休息并入睡，早上 8 点自动醒

CURSOR_NEAR_PX = 140         # 鼠标距离多近算「在旁边」
CURSOR_COOLDOWN_S = 15       # 凑近/害羞行为触发后多久内不再触发

RANDOM_BUBBLE_EVERY = (25, 70)   # 随机表情的间隔范围（秒）
# 随机表情池：名字 -> 权重
BUBBLE_POOL = {"开心": 3, "感叹": 2, "无语": 2, "困扰": 1, "错误": 1}

TODO_SECONDS = 15            # 待办提醒气泡停留时长（秒）

# 打包成 exe 后 __file__ 指向临时解压目录，一律以 exe 所在目录为家：
# 素材、配置、待办、日志都和 exe 放在一起（双击 exe 或跑 bat 都一样用）
if getattr(sys, "frozen", False):
    BASE_DIR = os.path.dirname(os.path.abspath(sys.executable))
else:
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))
ASSET_DIR = os.path.join(BASE_DIR, "素材")
CONFIG_PATH = os.path.join(BASE_DIR, "pet_config.json")
TODO_PATH = os.path.join(BASE_DIR, "todo.json")
SLEEP_CACHE = os.path.join(ASSET_DIR, "睡觉_已抠图.png")


def debug_log(msg: str):
    """轻量活动日志，方便确认互动行为；写入失败不影响运行。"""
    try:
        with open(os.path.join(BASE_DIR, "junimo_debug.log"), "a", encoding="utf-8") as f:
            f.write(f"{datetime.now().strftime('%H:%M:%S')} {msg}\n")
    except OSError:
        pass


# ----------------------------------------------------------------------------
# Windows 闲置检测（鼠标键盘多久没动过）+ 全屏前台检测
# ----------------------------------------------------------------------------
if sys.platform == "win32":
    from ctypes import (Structure, byref, c_long, c_uint, create_unicode_buffer,
                        sizeof, windll)

    class _LastInputInfo(Structure):
        _fields_ = [("cbSize", c_uint), ("dwTime", c_uint)]

    def idle_seconds() -> float:
        try:
            info = _LastInputInfo()
            info.cbSize = sizeof(info)
            if windll.user32.GetLastInputInfo(byref(info)):
                return max(0.0, (windll.kernel32.GetTickCount() - info.dwTime) / 1000.0)
        except Exception:
            pass
        return 0.0

    _WS_CAPTION = 0x00C00000
    _WS_THICKFRAME = 0x00040000

    class _RECT(Structure):
        _fields_ = [("left", c_long), ("top", c_long),
                    ("right", c_long), ("bottom", c_long)]

    class _MONITORINFO(Structure):
        _fields_ = [("cbSize", c_uint), ("rcMonitor", _RECT),
                    ("rcWork", _RECT), ("dwFlags", c_uint)]

    def fullscreen_active() -> bool:
        """前台是不是无边框全屏窗口（B 站客户端全屏、全屏视频、游戏等）。
        桌面和任务栏不算；带标题栏/可调边框的普通窗口不算。"""
        try:
            user32 = windll.user32
            hwnd = user32.GetForegroundWindow()
            if not hwnd:
                return False
            buf = create_unicode_buffer(64)
            user32.GetClassNameW(hwnd, buf, 64)
            if buf.value in ("Progman", "WorkerW", "Shell_TrayWnd"):
                return False
            if user32.GetWindowLongW(hwnd, -16) & (_WS_CAPTION | _WS_THICKFRAME):
                return False
            rect = _RECT()
            if not user32.GetWindowRect(hwnd, byref(rect)):
                return False
            mi = _MONITORINFO()
            mi.cbSize = sizeof(mi)
            mon = user32.MonitorFromWindow(hwnd, 2)   # MONITOR_DEFAULTTONEAREST
            if not mon or not user32.GetMonitorInfoW(mon, byref(mi)):
                return False
            return (rect.left <= mi.rcMonitor.left and rect.top <= mi.rcMonitor.top
                    and rect.right >= mi.rcMonitor.right
                    and rect.bottom >= mi.rcMonitor.bottom)
        except Exception:
            return False
else:
    _last_cursor = None
    _last_active = time.time()

    def idle_seconds() -> float:
        global _last_cursor, _last_active
        pos = QCursor.pos()
        if pos != _last_cursor:
            _last_cursor = pos
            _last_active = time.time()
        return time.time() - _last_active

    def fullscreen_active() -> bool:
        return False


def in_night() -> bool:
    h = datetime.now().hour
    if NIGHT_START <= NIGHT_END:
        return NIGHT_START <= h < NIGHT_END
    return h >= NIGHT_START or h < NIGHT_END      # 跨零点的作息（23 点-次日 8 点）


# ----------------------------------------------------------------------------
# 素材加载
# ----------------------------------------------------------------------------
def load_gif_frames(path: str):
    """逐帧读取 GIF，返回 (帧列表, 帧延迟列表)。"""
    reader = QImageReader(path)
    frames, delays = [], []
    while True:
        img = reader.read()
        if img.isNull():
            break
        pm = QPixmap.fromImage(img).scaled(
            PET_W, PET_W, Qt.IgnoreAspectRatio, Qt.FastTransformation)
        frames.append(pm)
        delays.append(max(reader.nextImageDelay() or ANIM_MS, 60))
    return frames, delays


def strip_sleep_background():
    """睡觉.png 是白底截图：最外 1px 只有描边/白色，精灵本体从第 2px 起。
    清掉最外圈后，从边缘向内洪泛清除白色背景（只做一次并缓存）。"""
    if os.path.exists(SLEEP_CACHE):
        return QPixmap(SLEEP_CACHE).scaled(
            PET_W, PET_W, Qt.IgnoreAspectRatio, Qt.FastTransformation)

    from collections import deque
    img = QImage(os.path.join(ASSET_DIR, "睡觉.png")).convertToFormat(QImage.Format_ARGB32)
    w, h = img.width(), img.height()

    def near_white(px):
        return (px >> 16 & 255) > 225 and (px >> 8 & 255) > 225 and (px & 255) > 225

    # 最外圈只有深色描边和白色背景（没有精灵像素），整圈清掉
    for x in range(w):
        img.setPixel(x, 0, 0x00000000)
        img.setPixel(x, h - 1, 0x00000000)
    for y in range(h):
        img.setPixel(0, y, 0x00000000)
        img.setPixel(w - 1, y, 0x00000000)

    # 从新的边界向内洪泛，清除与边缘连通的白色
    seen = bytearray(w * h)
    dq = deque()
    for x in range(1, w - 1):
        dq.append((x, 1))
        dq.append((x, h - 2))
    for y in range(1, h - 1):
        dq.append((1, y))
        dq.append((w - 2, y))
    while dq:
        x, y = dq.popleft()
        if seen[y * w + x]:
            continue
        seen[y * w + x] = 1
        if not near_white(img.pixel(x, y)):
            continue
        img.setPixel(x, y, 0x00000000)
        for nx, ny in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
            if 1 <= nx < w - 1 and 1 <= ny < h - 1 and not seen[ny * w + nx]:
                dq.append((nx, ny))
    img.save(SLEEP_CACHE, "PNG")
    return QPixmap.fromImage(img).scaled(
        PET_W, PET_W, Qt.IgnoreAspectRatio, Qt.FastTransformation)


def load_expressions():
    """加载头顶表情（表情脸气泡，已抠好透明底，见 素材/表情X_头像.png）。
    缓存文件缺失时退回用整张表情图。"""
    out = {}
    for name in BUBBLE_POOL:
        path = os.path.join(ASSET_DIR, f"表情{name}_头像.png")
        pm = QPixmap(path)
        if pm.isNull():
            pm = QPixmap(os.path.join(ASSET_DIR, f"表情{name}.png"))
        if not pm.isNull():
            out[name] = pm.scaled(EMOTE_SIZE, EMOTE_SIZE,
                                  Qt.KeepAspectRatio, Qt.FastTransformation)
    return out


# ----------------------------------------------------------------------------
# 小屋窗口（可以拖动安家；双击=祝尼魔出来，三击=祝尼魔躲进去）
# ----------------------------------------------------------------------------
class HutWindow(QWidget):
    def __init__(self, on_moved, on_dragging, on_double_click, on_triple_click, on_interact):
        super().__init__(None,
                         Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint
                         | Qt.Tool | Qt.NoDropShadowWindowHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.pixmap = QPixmap(os.path.join(ASSET_DIR, "祝尼魔小屋.png")).copy(0, 0, HUT_NATIVE, 113)
        self.label = QLabel(self)
        self.label.setPixmap(self.pixmap)
        self.label.setGeometry(0, 0, self.pixmap.width(), self.pixmap.height())
        self.setFixedSize(self.pixmap.size())
        self._press = None
        self._moved = False
        self._click_chain = 0
        self._last_press_t = 0.0
        self.on_moved = on_moved
        self.on_dragging = on_dragging
        self.on_double_click = on_double_click
        self.on_triple_click = on_triple_click
        self.on_interact = on_interact   # 每次被鼠标碰到后调用，让祝尼魔回到小屋图层之上

    def _register_press(self) -> bool:
        """连击计数（0.6 秒内）。Windows 把第二击合成 DblClick 事件，
        所以 press 和 dblclick 都要计数；数到三 = 三击小屋。"""
        now = time.time()
        self._click_chain = self._click_chain + 1 if now - self._last_press_t < 0.6 else 1
        self._last_press_t = now
        debug_log(f"hut press chain={self._click_chain}")
        if self._click_chain >= 3:
            self._click_chain = 0
            return True
        return False

    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton:
            if self._register_press():
                self.on_triple_click()
                self._press = None
            else:
                self._press = e.globalPosition().toPoint() - self.pos()
                self._moved = False
        self.on_interact()

    def mouseMoveEvent(self, e):
        if self._press is not None:
            new = e.globalPosition().toPoint() - self._press
            if (new - self.pos()).manhattanLength() > 6:
                self._moved = True
            self.move(new)
            self.on_dragging()
        self.on_interact()

    def mouseDoubleClickEvent(self, e):
        if e.button() != Qt.LeftButton:
            return
        if self._register_press():
            self.on_triple_click()
        else:
            self.on_double_click()
        self.on_interact()

    def mouseReleaseEvent(self, e):
        self._press = None
        if self._moved:
            self.on_moved()
        self.on_interact()


# ----------------------------------------------------------------------------
# 头顶表情小窗（不拦截鼠标，跟着祝尼魔移动）
# ----------------------------------------------------------------------------
class EmoteWindow(QWidget):
    def __init__(self):
        super().__init__(None,
                         Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint
                         | Qt.Tool | Qt.NoDropShadowWindowHint
                         | Qt.WindowTransparentForInput)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_ShowWithoutActivating)
        self.label = QLabel(self)
        self.label.setAlignment(Qt.AlignHCenter | Qt.AlignBottom)
        self.label.setGeometry(0, 0, EMOTE_SIZE + 8, EMOTE_SIZE + 8)
        self.setFixedSize(self.label.size())
        self._hide_timer = QTimer(self, singleShot=True)
        self._hide_timer.timeout.connect(self.hide)

    def show_emote(self, pixmap: QPixmap):
        self.label.setPixmap(pixmap)
        self.show()
        self.raise_()
        self._hide_timer.start(int(EMOTE_SECONDS * 1000))


# ----------------------------------------------------------------------------
# 文字提示气泡（不拦截鼠标）：待办提醒时显示在祝尼魔头顶
# ----------------------------------------------------------------------------
class ToastWindow(QWidget):
    def __init__(self):
        super().__init__(None,
                         Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint
                         | Qt.Tool | Qt.NoDropShadowWindowHint
                         | Qt.WindowTransparentForInput)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_ShowWithoutActivating)
        self.label = QLabel(self)
        self.label.setObjectName("toast")
        self.label.setStyleSheet(
            "#toast { background-color: rgba(24,24,30,238); color: #ffd94a;"
            " border: 1px solid #ffd94a; border-radius: 10px;"
            " padding: 7px 12px; font-size: 12px; }")
        self._hide_timer = QTimer(self, singleShot=True)
        self._hide_timer.timeout.connect(self.hide)

    def show_text(self, text: str, seconds: int = TODO_SECONDS):
        self.label.setText(text)
        self.label.adjustSize()
        self.setFixedSize(self.label.size())
        self.show()
        self.raise_()
        self._hide_timer.start(seconds * 1000)


# ----------------------------------------------------------------------------
# 日历样式（内嵌在待办面板里展开，避免独立弹窗的点击问题）
# ----------------------------------------------------------------------------
CAL_QSS = """
    QCalendarWidget QWidget#qt_calendar_navigationbar { background: #2a2a34; }
    QCalendarWidget QWidget { alternate-background-color: #2a2a34; }
    QCalendarWidget QToolButton { background: #3a3a46; color: #eee; border-radius: 4px;
                                  padding: 4px 8px; font-size: 12px; }
    QCalendarWidget QToolButton:hover { background: #4a4a58; }
    QCalendarWidget QToolButton:pressed { background: #55555f; }
    QCalendarWidget QToolButton::menu-indicator { image: none; }
    QCalendarWidget QMenu { background: #2a2a34; color: #eee; }
    QCalendarWidget QSpinBox { background: #1c1c22; color: #eee; }
    QCalendarWidget QWidget#qt_calendar_yearedit { background: #1c1c22; color: #eee; }
    QCalendarWidget #qt_calendar_calendarview { background: #1c1c22; color: #ddd;
                                                selection-background-color: #3f8a30; }
    QCalendarWidget QAbstractItemView:enabled { color: #ddd; }
    QCalendarWidget QAbstractItemView:disabled { color: #555; }
    QTimeEdit { background: #1c1c22; color: #8fc7ff; border: 1px solid #454550;
                border-radius: 6px; padding: 3px; font-size: 12px; }
    QPushButton { background: #3f8a30; color: white; border: none;
                  border-radius: 6px; padding: 4px 12px; font-size: 12px; }
    QPushButton:hover { background: #4da63c; }
"""


class HoverCalendar(QCalendarWidget):
    """给日期格子加悬停高亮框：鼠标放到哪天，哪天就描一个绿框。"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self._hover = None
        self.setMouseTracking(True)
        self._view = self.findChild(QTableView)
        if self._view:
            self._view.setMouseTracking(True)
            self._view.viewport().setMouseTracking(True)
            self._view.viewport().installEventFilter(self)

    def _cell_date(self, row: int, col: int):
        """以「本月 1 号所在格子」为锚点换算网格日期。锚点运行时实测
        （全网格第一个显示 1 的格子），不依赖 locale 的周起始设置。"""
        model = self._view.model()
        for r in range(model.rowCount()):
            for c in range(model.columnCount()):
                if model.index(r, c).data() in (1, "1"):
                    first = QDate(self.yearShown(), self.monthShown(), 1)
                    return first.addDays((row - r) * 7 + (col - c))
        return QDate()

    def _date_at(self, vx: float, vy: float):
        """由表格视口坐标算出对应日期。QCalendarWidget::dateAt 在 PySide6
        里没有绑定，改走内部表格的 indexAt + 锚点换算。"""
        view = self._view
        if view is None:
            return QDate()
        idx = view.indexAt(QPoint(int(vx), int(vy)))
        if not idx.isValid():
            return QDate()
        return self._cell_date(idx.row(), idx.column())

    def eventFilter(self, obj, ev):
        if self._view and obj is self._view.viewport():
            if ev.type() == QEvent.MouseMove:
                d = self._date_at(ev.position().x(), ev.position().y())
                if d != self._hover:
                    self._hover = d
                    self.updateCells()
            elif ev.type() == QEvent.Leave:
                if self._hover is not None:
                    self._hover = None
                    self.updateCells()
        return super().eventFilter(obj, ev)

    def paintCell(self, painter, rect, date):
        super().paintCell(painter, rect, date)
        if date.isValid() and self._hover is not None and date == self._hover:
            painter.save()
            painter.setRenderHint(QPainter.Antialiasing)
            painter.setPen(QPen(QColor("#7ddb58"), 2))
            painter.drawRoundedRect(rect.adjusted(1, 1, -2, -2), 4, 4)
            painter.restore()


# ----------------------------------------------------------------------------
# 今日待办面板：双击祝尼魔打开，可添加/勾选/删除，支持到点提醒
# ----------------------------------------------------------------------------
class TodoPanel(QWidget):
    def __init__(self):
        super().__init__(None,
                         Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint
                         | Qt.Tool | Qt.NoDropShadowWindowHint)
        self.setAttribute(Qt.WA_StyledBackground, True)
        self.items = self._load()
        self._drag_off = None
        self._build_ui()
        self.refresh()

    # ---- 数据 ----
    def _load(self):
        try:
            with open(TODO_PATH, encoding="utf-8") as f:
                data = json.load(f)
            items = data if isinstance(data, list) else []
        except Exception:
            return []
        # 兼容旧格式：纯 "HH:MM" 迁移成完整日期时间（已过就顺延到明天）
        now = datetime.now()
        for it in items:
            t = it.get("time")
            if t and len(t) == 5 and "-" not in t:
                try:
                    hh, mm = map(int, t.split(":"))
                    dt = now.replace(hour=hh, minute=mm, second=0, microsecond=0)
                    if dt <= now:
                        dt += timedelta(days=1)
                    it["time"] = dt.strftime("%Y-%m-%d %H:%M")
                    it.pop("reminded", None)
                except (ValueError, TypeError):
                    pass
        return items

    def _save(self):
        try:
            with open(TODO_PATH, "w", encoding="utf-8") as f:
                json.dump(self.items, f, ensure_ascii=False, indent=2)
        except OSError:
            pass

    def due_reminders(self) -> list:
        """找出到点未完成的待办。在设定时刻之后 2 分钟内触发，
        和电脑时钟严格对应；每条只提醒一次。"""
        now = datetime.now()
        due = []
        for it in self.items:
            if it.get("done") or it.get("fired") or not it.get("time"):
                continue
            try:
                t = datetime.strptime(it["time"], "%Y-%m-%d %H:%M")
            except (ValueError, TypeError):
                continue
            if now >= t and (now - t).total_seconds() < 120:
                it["fired"] = True
                due.append(it["text"])
        if due:
            self._save()
        return due

    # ---- 界面 ----
    def _build_ui(self):
        self.setFixedWidth(312)
        root = QVBoxLayout(self)
        root.setContentsMargins(14, 12, 14, 14)
        root.setSpacing(9)

        title_row = QHBoxLayout()
        title = QLabel("今日待办")
        title.setStyleSheet("color:#ffd94a; font-weight:bold; font-size:15px;")
        close = QPushButton("✕")
        close.setFixedSize(26, 26)
        close.setCursor(Qt.PointingHandCursor)
        close.setToolTip("关闭")
        close.setStyleSheet(
            "QPushButton{color:#ddd;border:1px solid #4a4a56;background:#2e2e38;"
            "border-radius:13px;font-size:13px;}"
            "QPushButton:hover{color:#fff;background:#7a3838;border-color:#9a4a4a;}")
        close.clicked.connect(self.hide)
        title_row.addWidget(title)
        title_row.addStretch(1)
        title_row.addWidget(close)
        root.addLayout(title_row)

        # 标题和内容之间的分隔线
        line = QFrame()
        line.setFrameShape(QFrame.HLine)
        line.setFixedHeight(1)
        line.setStyleSheet("background:#41414d; border:none;")
        root.addWidget(line)

        self.list_area = QScrollArea()
        self.list_area.setWidgetResizable(True)
        self.list_area.setFrameShape(QFrame.NoFrame)
        self.list_area.setStyleSheet("QScrollArea{background:transparent;}")
        self.list_host = QWidget()
        self.list_host.setStyleSheet("background:transparent;")
        self.list_layout = QVBoxLayout(self.list_host)
        self.list_layout.setContentsMargins(0, 0, 4, 0)
        self.list_layout.setSpacing(4)
        self.list_layout.addStretch(1)
        self.list_area.setWidget(self.list_host)
        self.list_area.setMinimumHeight(110)
        root.addWidget(self.list_area)

        add_row = QHBoxLayout()
        add_row.setSpacing(6)
        self.input = QLineEdit()
        self.input.setPlaceholderText("要做什么？回车也能添加")
        self.input.returnPressed.connect(self._add)
        self.picker_dt = datetime.now() + timedelta(minutes=30)
        self.time_check = QCheckBox("提醒")
        self.time_btn = QPushButton()
        self.time_btn.setFixedWidth(122)
        self.time_btn.setCursor(Qt.PointingHandCursor)
        self.time_btn.clicked.connect(self._toggle_calendar)
        self._update_time_btn()
        self.time_btn.setStyleSheet(
            "QPushButton{background:#1c1c22;color:#8fc7ff;border:1px solid #454550;"
            "border-radius:6px;padding:3px;font-size:12px;}"
            "QPushButton:hover{border-color:#6a6a7a;}")
        # 没勾「提醒」时时间按钮直接隐藏，勾了才出现（避免一行里常驻一块灰按钮）
        self.time_btn.setVisible(False)
        self.time_check.toggled.connect(self.time_btn.setVisible)
        add_btn = QPushButton("添加")
        add_btn.setCursor(Qt.PointingHandCursor)
        add_btn.clicked.connect(self._add)
        add_row.addWidget(self.input, 1)
        add_row.addWidget(self.time_check)
        add_row.addWidget(self.time_btn)
        add_row.addWidget(add_btn)
        root.addLayout(add_row)

        # 内嵌日历（点时间按钮展开 / 收起）
        self.cal_box = QWidget()
        self.cal_box.setStyleSheet(CAL_QSS + " QWidget { font-size: 12px; }")
        cv = QVBoxLayout(self.cal_box)
        cv.setContentsMargins(4, 4, 4, 6)
        cv.setSpacing(6)
        self.cal = HoverCalendar()
        self.cal.setVerticalHeaderFormat(QCalendarWidget.NoVerticalHeader)
        self.cal.setGridVisible(True)
        cv.addWidget(self.cal)
        cal_row = QHBoxLayout()
        cal_row.setSpacing(8)
        self.cal_time = QTimeEdit()
        self.cal_time.setDisplayFormat("HH:mm")
        self.cal_time.setAlignment(Qt.AlignCenter)
        cal_ok = QPushButton("确定时间")
        cal_ok.setCursor(Qt.PointingHandCursor)
        cal_ok.clicked.connect(self._confirm_calendar)
        cal_row.addWidget(self.cal_time, 1)
        cal_row.addWidget(cal_ok)
        cv.addLayout(cal_row)
        self.cal_box.setVisible(False)
        root.addWidget(self.cal_box)

        self.setStyleSheet("""
            TodoPanel { background-color: rgba(32,32,40,244); border-radius: 12px; }
            QLabel { color: #eee; font-size: 12px; background: transparent; }
            QLineEdit { background: #1c1c22; color: #eee; border: 1px solid #454550;
                        border-radius: 6px; padding: 4px 6px; font-size: 12px; }
            QCheckBox { color: #bbb; font-size: 11px; background: transparent; }
            QPushButton { background: #3f8a30; color: white; border: none;
                          border-radius: 6px; padding: 4px 10px; font-size: 12px; }
            QPushButton:hover { background: #4da63c; }
            QPushButton:disabled { background: #2c2c33; color: #666; }
            QScrollArea { background: transparent; }
        """)

    def refresh(self):
        while self.list_layout.count() > 1:
            item = self.list_layout.takeAt(0)
            w = item.widget()
            if w is not None:
                w.deleteLater()
        for idx, it in enumerate(self.items):
            row = QWidget()
            row.setStyleSheet("background: rgba(255,255,255,10); border-radius: 6px;")
            h = QHBoxLayout(row)
            h.setContentsMargins(8, 6, 6, 6)
            h.setSpacing(6)

            cb = QCheckBox()
            cb.setChecked(it["done"])
            cb.toggled.connect(lambda checked, i=idx: self._set_done(i, checked))
            h.addWidget(cb)

            lbl = QLabel(it["text"])
            font = QFont()
            font.setStrikeOut(it["done"])
            lbl.setFont(font)
            lbl.setStyleSheet("color:%s; font-size:12px;" % ("#777" if it["done"] else "#eee"))
            h.addWidget(lbl, 1)

            if it.get("time"):
                disp = it["time"]
                try:
                    dt = datetime.strptime(it["time"], "%Y-%m-%d %H:%M")
                    disp = f"{dt.month}/{dt.day} {dt:%H:%M}"
                except ValueError:
                    pass
                t_lbl = QLabel(disp + (" 提醒" if not it["done"] else ""))
                t_lbl.setStyleSheet("color:#8fc7ff; font-size:11px;")
                h.addWidget(t_lbl)

            del_btn = QPushButton("删")
            del_btn.setFixedSize(26, 20)
            del_btn.setCursor(Qt.PointingHandCursor)
            del_btn.setStyleSheet(
                "QPushButton{background:#5a3030;color:#eaa;border-radius:5px;"
                "font-size:11px;padding:0;} QPushButton:hover{background:#7a3838;color:#fff;}")
            del_btn.clicked.connect(lambda _, i=idx: self._delete(i))
            h.addWidget(del_btn)
            self.list_layout.insertWidget(self.list_layout.count() - 1, row)

        self.list_area.setFixedHeight(max(110, min(240, self.list_host.sizeHint().height() + 6)))
        self._save()
        self._resize_to_content()

    def _add(self):
        text = self.input.text().strip()
        if not text:
            return
        t = self.picker_dt.strftime("%Y-%m-%d %H:%M") if self.time_check.isChecked() else None
        self.items.append({"text": text, "time": t, "done": False, "fired": False})
        self.input.clear()
        self.refresh()

    def _update_time_btn(self):
        self.time_btn.setText(f"{self.picker_dt.month}/{self.picker_dt.day} {self.picker_dt:%H:%M}")

    def _resize_to_content(self):
        """按当前内容收放面板高度。日历收起后若面板仍保持展开时的高度，
        中间会空出一大块，非常难看；增删待办时也要跟着长高/变矮。"""
        self.setMinimumHeight(0)
        self.setMaximumHeight(16777215)
        self.adjustSize()
        if self.isVisible():
            self._ensure_on_screen()

    def _toggle_calendar(self):
        show = not self.cal_box.isVisible()
        self.cal_box.setVisible(show)
        if show:
            self.cal.setSelectedDate(QDate(self.picker_dt.year, self.picker_dt.month, self.picker_dt.day))
            self.cal_time.setTime(QTime(self.picker_dt.hour, self.picker_dt.minute))
        self._resize_to_content()

    def _confirm_calendar(self):
        d = self.cal.selectedDate()
        t = self.cal_time.time()
        self.picker_dt = datetime(d.year(), d.month(), d.day(), t.hour(), t.minute())
        self._update_time_btn()
        self.cal_box.setVisible(False)
        self._resize_to_content()

    def _ensure_on_screen(self):
        """展开日历后面板会变高，保证整体都在屏幕内。"""
        geo = self.screen().availableGeometry()
        g = self.geometry()
        x = min(max(geo.left(), g.x()), geo.right() - g.width())
        y = min(max(geo.top(), g.y()), geo.bottom() - g.height())
        if (x, y) != (g.x(), g.y()):
            self.move(x, y)

    def _set_done(self, idx: int, done: bool):
        if 0 <= idx < len(self.items):
            self.items[idx]["done"] = done
            self.refresh()

    def _delete(self, idx: int):
        if 0 <= idx < len(self.items):
            del self.items[idx]
            self.refresh()

    def toggle_near(self, anchor: QPoint):
        if self.isVisible():
            self.hide()
            return
        geo = QApplication.primaryScreen().availableGeometry()
        x = anchor.x() + PET_W + 12
        y = anchor.y() - 30
        self.move(max(geo.left(), min(x, geo.right() - self.width())),
                  max(geo.top(), min(y, geo.bottom() - self.height())))
        self.show()
        self.raise_()
        self.activateWindow()
        self.input.setFocus()

    # 面板拖动（按住标题/空白处拖）
    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton:
            self._drag_off = e.globalPosition().toPoint() - self.pos()

    def mouseMoveEvent(self, e):
        if self._drag_off is not None:
            self.move(e.globalPosition().toPoint() - self._drag_off)

    def mouseReleaseEvent(self, e):
        self._drag_off = None


# ----------------------------------------------------------------------------
# 祝尼魔本体
# ----------------------------------------------------------------------------
class PetWindow(QWidget):
    def __init__(self):
        super().__init__(None,
                         Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint
                         | Qt.Tool | Qt.NoDropShadowWindowHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setFixedSize(PET_W, PET_W)

        self.frames, _ = load_gif_frames(os.path.join(ASSET_DIR, "Junimo.gif"))
        self.frames_left = [QPixmap.fromImage(f.toImage().mirrored(True, False))
                            for f in self.frames]
        self.sleep_pm = strip_sleep_background()
        self.expressions = load_expressions()

        self.hut = HutWindow(self._on_hut_moved, self.follow_hut, self.come_out,
                             self.hide_into_hut, self._raise_stack)

        # 状态机：idle / drag / jump / go_home / follow_home / sleep / hidden
        self.state = "idle"
        self.facing = 1
        self.frame_idx = 0
        self.bounce_step = 0          # 走路时的小跳步数
        self.jump_t0 = 0.0            # 蹦跳开始时间
        self.jump_dur = 0.0
        self.jump_amp = 0.0
        self.walk_target_x = None
        self.walk_speed = WALK_SPEED
        self.next_decide = time.time() + 2
        self.next_random_bubble = time.time() + random.uniform(*RANDOM_BUBBLE_EVERY)
        self.cursor_cooldown = 0.0
        self.sad_shown = False
        self.force_sleep = False      # 托盘菜单手动要求睡觉
        self._night_sleep = False     # 这次睡觉是因为夜间作息（到点要自动醒）
        self._rest_said = None        # 最近一次说「该休息了」的日期（每晚只说一次）
        self._fs_hidden = False       # 当前因全屏应用而临时隐藏
        self._fs_restore = {}         # 全屏前各窗口的可见状态，退出后恢复
        self._error_cooldown = 0.0
        self._came_out_at = 0.0       # 刚从小屋出来的时间（防止连击误触又藏回去）
        self.emote_win = EmoteWindow()
        self.toast = ToastWindow()
        self.todo = TodoPanel()

        self._base = QPoint(100, 100)  # 逻辑位置（落地基准），蹦跳/走路起伏通过抬升窗口实现

        self._press = None
        self._press_global = None
        self._drag_moved = False
        self._drag_bubbled = False

        self.anim_timer = QTimer(self, interval=ANIM_MS)
        self.anim_timer.timeout.connect(self._next_frame)
        self.anim_timer.start()

        self.tick_timer = QTimer(self, interval=TICK_MS)
        self.tick_timer.timeout.connect(self.on_tick)
        self.tick_timer.start()

        # 每秒检查一次有没有到点的待办 + 夜间作息 + 是否在全屏看视频
        self.remind_timer = QTimer(self, interval=1000)
        self.remind_timer.timeout.connect(self._check_reminders)
        self.remind_timer.timeout.connect(self._check_night_rest)
        self.remind_timer.timeout.connect(self._check_fullscreen)
        self.remind_timer.start()

    def _check_reminders(self):
        try:
            due = self.todo.due_reminders()
        except Exception:
            return
        if not due:
            return
        debug_log(f"待办提醒: {due}")
        if self._fs_hidden:
            return        # 全屏看视频/游戏中：只记录已提醒，不弹窗打扰
        if self.state == "hidden":
            self.come_out()
        elif self.state == "sleep":
            self._wake()
        self.show_bubble("感叹")
        self.toast.show_text("待办提醒：" + "、".join(due))
        self._sync_emote()

    def _check_night_rest(self):
        """晚上 23 点（NIGHT_START）提醒一次休息；之后作息自动让它走去睡觉。"""
        now = datetime.now()
        if now.hour != NIGHT_START or self._rest_said == now.date():
            return
        self._rest_said = now.date()
        if self.state in ("hidden", "sleep") or self._fs_hidden:
            return
        debug_log("夜间休息提醒")
        self.show_bubble("感叹")
        self.toast.show_text(f"{NIGHT_START} 点啦，该休息了，晚安~")
        self._sync_emote()

    def _fs_windows(self):
        # 固定列表：隐藏前记录各窗口可见性，恢复时才不会漏掉已藏起来的面板
        return [self, self.hut, self.emote_win, self.toast, self.todo]

    def _check_fullscreen(self):
        """看全屏视频/游戏时宠物和小屋自动让位，退出全屏自动回来。
        恢复时只把全屏前可见的窗口请回来，用户自己藏的不会被吵醒。"""
        fs = fullscreen_active()
        if fs and not self._fs_hidden:
            self._fs_hidden = True
            self._fs_restore = {id(w): w.isVisible() for w in self._fs_windows()}
            for w in self._fs_windows():
                w.hide()
            debug_log("全屏中 -> 暂时隐藏宠物和小屋")
        elif not fs and self._fs_hidden:
            self._fs_hidden = False
            debug_log("全屏结束 -> 恢复显示")
            for w in self._fs_windows():
                if self._fs_restore.get(id(w)):
                    w.show()
            self._raise_stack()

    # ---------------- 基础小工具 ----------------
    def _raise_stack(self):
        """小屋被碰到时 Windows 会把它顶到祝尼魔上面；
        立刻把图层顺序恢复为：表情/提醒 > 祝尼魔 > 小屋。"""
        if self.state == "hidden" or not self.isVisible():
            return
        self.raise_()
        if self.emote_win.isVisible():
            self.emote_win.raise_()
        if self.toast.isVisible():
            self.toast.raise_()

    def set_base(self, pos: QPoint):
        """设置逻辑位置（拖拽落点、安家、出场都用它）。"""
        self._base = QPoint(pos)
        self._render()

    def _render(self):
        """按基准位置摆放窗口：蹦跳/走路的起伏通过抬升窗口实现。"""
        off = round(self._jump_y())
        if self.walk_target_x is not None and self.state != "sleep":
            off += round(abs(math.sin(self.bounce_step * 0.45)) * 6)
        pos = QPoint(self._base.x(), self._base.y() - off)
        if pos != self.pos():
            self.move(pos)
        self._sync_emote()

    def _sync_emote(self):
        """表情小窗 / 提醒气泡跟着脑袋走。"""
        if self.toast.isVisible():
            geo = self.screen().geometry()
            extra = self.emote_win.height() if self.emote_win.isVisible() else 0
            x = self.x() + (PET_W - self.toast.width()) // 2
            y = self.y() - self.toast.height() - extra + 6
            self.toast.move(max(geo.left(), min(x, geo.right() - self.toast.width())),
                            max(geo.top(), min(y, geo.bottom() - self.toast.height())))
        if not self.emote_win.isVisible():
            return
        geo = self.screen().geometry()
        x = self.x() + (PET_W - self.emote_win.width()) // 2
        y = self.y() - self.emote_win.height() + 12
        self.emote_win.move(max(geo.left(), min(x, geo.right() - self.emote_win.width())),
                            max(geo.top(), min(y, geo.bottom() - self.emote_win.height())))

    def _ground_y_for(self, pet_x: int) -> int:
        """祝尼魔的脚落在小屋底部同一条地面上。"""
        return self.hut.y() + self.hut.height() - PET_W

    def _wander_bounds(self):
        geo = self.screen().availableGeometry()
        center = self.hut.x() + self.hut.width() // 2
        left = max(geo.left(), center - WANDER_RADIUS)
        right = min(geo.right() - PET_W, center + WANDER_RADIUS)
        return left, right

    def _clamp_on_screen(self):
        geo = self.screen().availableGeometry()
        x = max(geo.left(), min(self._base.x(), geo.right() - self.width()))
        y = max(geo.top(), min(self._base.y(), geo.bottom() - self.height()))
        if (x, y) != (self._base.x(), self._base.y()):
            self.set_base(QPoint(x, y))

    def show_bubble(self, name: str):
        pm = self.expressions.get(name)
        if pm is not None:
            debug_log(f"表情: {name} (state={self.state})")
            self.emote_win.show_emote(pm)
            self._sync_emote()

    def _roll_bubble(self) -> str | None:
        names, weights = zip(*BUBBLE_POOL.items())
        return random.choices(names, weights=weights, k=1)[0]

    # ---------------- 绘制与动画 ----------------
    def _next_frame(self):
        self.frame_idx = (self.frame_idx + 1) % len(self.frames)
        self.update()

    def _jump_y(self) -> int:
        if self.jump_t0 <= 0:
            return 0
        t = time.time() - self.jump_t0
        if t >= self.jump_dur:
            self.jump_t0 = 0
            return 0
        return round(-self.jump_amp * abs(math.sin(math.pi * t / self.jump_dur)))

    def paintEvent(self, e):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.SmoothPixmapTransform, False)
        if self.state == "sleep":
            painter.drawPixmap(0, 0, self.sleep_pm)
            return
        frames = self.frames_left if self.facing < 0 else self.frames
        painter.drawPixmap(0, 0, frames[self.frame_idx % len(frames)])

    def start_jump(self, amp=30, dur=0.65):
        self.jump_t0 = time.time()
        self.jump_amp = amp
        self.jump_dur = dur
        self.state = "jump"

    # ---------------- 状态机 ----------------
    def on_tick(self):
        try:
            self._tick()
        except Exception:
            if time.time() > self._error_cooldown:
                self._error_cooldown = time.time() + 60
                self.show_bubble("错误")
                with open(os.path.join(BASE_DIR, "junimo_error.log"), "a", encoding="utf-8") as f:
                    f.write(traceback.format_exc() + "\n")

    def _tick(self):
        now = time.time()
        idle = idle_seconds()

        if self.state == "drag":
            return

        if self.state == "hidden":
            return

        if self.state == "follow_home":
            self._walk_step()
            if self.walk_target_x is None:      # 跟到小屋跟前了
                if self.force_sleep or in_night():
                    self._doze()
                else:
                    self.state = "idle"
                    self.next_decide = now + 2
            return

        if self.state == "sleep":
            if self.force_sleep and not self._night_sleep:
                return                        # 手动要求睡的，只等主人唤醒
            if self._night_sleep:
                if not in_night():            # 夜间作息：早上到点自动醒，不用等鼠标动
                    self._wake()
            elif idle < 3:                    # 闲置打盹：有动静就醒
                self._wake()
            return

        if self.state == "go_home":
            if self._night_sleep and not in_night():
                self.state = "idle"           # 走回去的路上跨过了早上醒来的点
                self.walk_target_x = None
                return
            if not self.force_sleep and not in_night() and idle < 3:
                self.state = "idle"
                self.walk_target_x = None
                return
            self._walk_step()
            if self.walk_target_x is None:      # 走到了，睡觉
                self._doze()
            return

        # —— 以下都是醒着的状态 ——
        if in_night() or idle > IDLE_DOZE_S:
            self._start_go_home()
            return

        if idle > IDLE_SAD_S and not self.sad_shown:
            self.sad_shown = True
            self.show_bubble("无语")

        if self.state == "jump":
            if self.jump_t0 == 0:
                self.state = "idle"
            self._render()
            return

        self._maybe_cursor_react(now)

        if self.walk_target_x is not None:
            self._walk_step()
        elif now >= self.next_decide:
            self._decide(now)

        if now >= self.next_random_bubble:
            self.next_random_bubble = now + random.uniform(*RANDOM_BUBBLE_EVERY)
            self.show_bubble(self._roll_bubble())

        self._clamp_on_screen()
        self._render()

    def _decide(self, now):
        self.next_decide = now + random.uniform(2.0, 6.0)
        roll = random.random()
        if roll < 0.45:                        # 随便走走
            left, right = self._wander_bounds()
            here = self.x()
            span = random.uniform(40, 180)
            direction = random.choice((-1, 1))
            target = int(here + direction * span)
            if not (left <= target <= right):
                target = int(here - direction * span)
            self.walk_target_x = max(left, min(right, target))
            self.walk_speed = WALK_SPEED
        elif roll < 0.70:                      # 原地发呆
            pass
        elif roll < 0.82:                      # 小蹦一下
            self.start_jump(amp=14, dur=0.4)
        elif roll < 0.92:                      # 转个身
            self.facing *= -1
            self.update()

    def _maybe_cursor_react(self, now):
        if now < self.cursor_cooldown or self.walk_target_x is not None:
            return
        cursor = QCursor.pos()
        center = self.mapToGlobal(QPoint(self.width() // 2, self.height() // 2))
        gx, gy = center.x(), center.y()
        if abs(cursor.x() - gx) > CURSOR_NEAR_PX or abs(cursor.y() - gy) > CURSOR_NEAR_PX + 40:
            return
        self.cursor_cooldown = now + CURSOR_COOLDOWN_S
        roll = random.random()
        if roll < 0.5:                          # 凑过来蹭蹭
            side = 1 if gx <= cursor.x() else -1
            target = cursor.x() - side * int(PET_W * 0.8)
            left, right = self._wander_bounds()
            geo = self.screen().availableGeometry()
            self.walk_target_x = max(min(target, geo.right() - PET_W), geo.left())
            self.walk_speed = WALK_SPEED + 1
            if random.random() < 0.35:
                self.show_bubble("困扰")
        elif roll < 0.85:                       # 害羞地跑开
            away = 1 if self.x() <= cursor.x() else -1
            left, right = self._wander_bounds()
            geo = self.screen().availableGeometry()
            self.walk_target_x = max(min(self.x() + away * random.randint(150, 230),
                                         geo.right() - PET_W), geo.left())
            self.walk_speed = SHY_SPEED
            if random.random() < 0.25:
                self.show_bubble("困扰")

    def _walk_step(self):
        if self.walk_target_x is None:
            return
        dx = self.walk_target_x - self._base.x()
        if abs(dx) <= self.walk_speed:
            self._base.setX(self.walk_target_x)
            self.walk_target_x = None
            self.bounce_step = 0
            self._render()
            return
        self.facing = 1 if dx > 0 else -1
        self._base.setX(self._base.x() + self.facing * self.walk_speed)
        # 回家/跟随时斜着走向小屋的地面线：高度平滑过渡，半空里也能落回地面
        if self.state in ("go_home", "follow_home"):
            ground = self._ground_y_for(self._base.x())
            dy = ground - self._base.y()
            step = self.walk_speed * 2
            if abs(dy) <= step:
                self._base.setY(ground)
            else:
                self._base.setY(self._base.y() + (step if dy > 0 else -step))
        self.bounce_step += 1
        self._render()

    # ---------------- 睡觉相关 ----------------
    def _beside_hut_x(self) -> int:
        """小屋墙边的位置（睡觉/出场用），把小屋正面留出来方便双击/三击。"""
        if random.random() < 0.5:
            return self.hut.x() - PET_W + 18
        return self.hut.x() + self.hut.width() - 18

    def hide_into_hut(self):
        """三击小屋：祝尼魔直接消失，躲进小屋里。"""
        if self.state == "hidden":
            return
        if time.time() - self._came_out_at < 1.0:
            debug_log("三击忽略（刚出来）")
            return
        debug_log("三击 -> 立即隐藏")
        self.state = "hidden"
        self.force_sleep = False
        self.sad_shown = False
        self.walk_target_x = None
        self.jump_t0 = 0.0
        self.emote_win.hide()
        self.hide()

    def come_out(self):
        """双击小屋：祝尼魔直接从小屋里出来。"""
        debug_log("双击小屋 -> come_out")
        if self.state != "hidden":
            return
        x = self._beside_hut_x()
        self.set_base(QPoint(x, self._ground_y_for(x)))
        self.show()
        self.raise_()
        self.state = "idle"
        self.force_sleep = False
        self.sad_shown = False
        self.next_decide = time.time() + 2
        self.next_random_bubble = time.time() + random.uniform(*RANDOM_BUBBLE_EVERY)
        self._came_out_at = time.time()
        self.start_jump(amp=22, dur=0.5)
        self.show_bubble("感叹")

    def follow_hut(self):
        """小屋被拖动时一路小跑跟过去，不瞬移。目标也是小屋墙边，不站到小屋顶上。"""
        if self.state in ("drag", "hidden"):
            return
        debug_log(f"小屋拖动 -> follow_hut (hut_x={self.hut.x()})")
        was_asleep = self.state in ("sleep", "go_home")
        self.state = "follow_home"
        front = self._beside_hut_x()
        virtual = QApplication.primaryScreen().virtualGeometry()
        self.walk_target_x = max(min(front, virtual.right() - PET_W), virtual.left())
        self.walk_speed = WALK_SPEED + 2
        self.sad_shown = False
        if was_asleep:
            self.show_bubble("感叹")
        self.update()

    def _start_go_home(self):
        was_forced = self.force_sleep
        self.force_sleep = self.force_sleep or in_night()
        # 夜间作息引起的回家要记上标记，早上到点自动醒；手动睡觉不算
        self._night_sleep = in_night() and not was_forced
        self.state = "go_home"
        # 走到小屋墙边睡，小屋正面留出来方便双击/三击
        front = self._beside_hut_x()
        # 用整个虚拟桌面做范围，这样在副屏时也能走回主屏的小屋
        virtual = QApplication.primaryScreen().virtualGeometry()
        self.walk_target_x = max(min(front, virtual.right() - PET_W), virtual.left())
        self.walk_speed = WALK_SPEED

    def _doze(self):
        self.state = "sleep"
        self.walk_target_x = None
        self.bounce_step = 0
        self._base.setY(self._ground_y_for(self._base.x()))
        self._render()
        self.update()

    def _wake(self):
        self.state = "idle"
        self.force_sleep = False
        self._night_sleep = False
        self.sad_shown = False
        self.next_decide = time.time() + 2
        self.next_random_bubble = time.time() + random.uniform(*RANDOM_BUBBLE_EVERY)
        self.show_bubble("感叹")
        self.update()

    def toggle_sleep(self):
        if self.state == "hidden":
            self.come_out()
            return
        if self.state == "sleep":
            self.force_sleep = False
            self._wake()
        else:
            self.force_sleep = True
            self.sad_shown = False
            if self.state in ("go_home",):
                return
            self._start_go_home()

    # ---------------- 鼠标互动 ----------------
    def mousePressEvent(self, e):
        if e.button() != Qt.LeftButton:
            return
        if self.state == "hidden":
            return
        if self.state in ("sleep", "go_home"):
            self.force_sleep = False
            self._night_sleep = False
            if self.state == "sleep":
                self._wake()
            else:
                self.state = "idle"
                self.walk_target_x = None
        self._press = e.globalPosition().toPoint() - self.pos()
        self._press_global = e.globalPosition().toPoint()
        self._drag_moved = False
        self._drag_bubbled = False
        self.state = "drag"
        self.walk_target_x = None
        self.jump_t0 = 0.0

    def mouseMoveEvent(self, e):
        if self._press is None:
            return
        gp = e.globalPosition().toPoint()
        if not self._drag_moved and (gp - self._press_global).manhattanLength() > 8:
            self._drag_moved = True
        if self._drag_moved:
            if not self._drag_bubbled:
                self._drag_bubbled = True
                self.show_bubble("感叹")
            self._base = gp - self._press
            self.move(self._base)
            self._sync_emote()

    def mouseDoubleClickEvent(self, e):
        # 双击祝尼魔：打开 / 收起今日待办
        if e.button() == Qt.LeftButton and self.state != "hidden":
            debug_log("双击祝尼魔 -> 待办面板")
            self.todo.toggle_near(self._base)

    def mouseReleaseEvent(self, e):
        if self._press is None:
            return
        moved = self._drag_moved
        self._press = None
        if not moved:
            # 单击：开心地蹦一下
            self.start_jump(amp=30, dur=0.65)
            self.show_bubble("开心")
        else:
            self._clamp_on_screen()
            save_config(self)
        self.state = "idle"
        self.next_decide = time.time() + 2

    def _on_hut_moved(self):
        if clamp_into_virtual(self.hut):
            debug_log(f"小屋拖动落点钳回屏幕内 -> ({self.hut.x()},{self.hut.y()})")
        save_config(self)
        self.follow_hut()


# ----------------------------------------------------------------------------
# 配置持久化
# ----------------------------------------------------------------------------
def save_config(pet: PetWindow):
    try:
        cfg = {
            "hut": [pet.hut.x(), pet.hut.y()],
            "pet": [pet.x(), pet.y()],
        }
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def load_config():
    try:
        with open(CONFIG_PATH, encoding="utf-8") as f:
            cfg = json.load(f)
        return cfg.get("hut"), cfg.get("pet")
    except Exception:
        return None, None


def clamp_into_virtual(widget):
    """把窗口拉回虚拟桌面内。显示缩放/显示器变化后，旧坐标可能落在屏幕外
    （表现为窗口「可见」却永远看不到），所以在启动/显示/拖动落点都要钳一次。"""
    vg = QApplication.primaryScreen().virtualGeometry()
    x = max(vg.left(), min(widget.x(), vg.right() - widget.width() + 1))
    y = max(vg.top(), min(widget.y(), vg.bottom() - widget.height() + 1))
    if (x, y) != (widget.x(), widget.y()):
        widget.move(x, y)
        return True
    return False


# ----------------------------------------------------------------------------
# 程序入口
# ----------------------------------------------------------------------------
def main():
    app = QApplication(sys.argv)
    app.setApplicationName("祝尼魔桌面宠物")
    app.setQuitOnLastWindowClosed(False)

    lock = QLockFile(os.path.join(os.environ.get("TEMP", "."), "junimo_pet.lock"))
    if not lock.tryLock(100):
        box = QMessageBox()
        box.setWindowTitle("祝尼魔")
        box.setText("祝尼魔已经在桌面上啦，不要重复召唤～")
        box.exec()
        return 0

    pet = PetWindow()

    hut_cfg, pet_cfg = load_config()
    screen = app.primaryScreen().availableGeometry()
    hut_w, hut_h = pet.hut.width(), pet.hut.height()
    if hut_cfg:
        hut_x, hut_y = hut_cfg
    else:
        hut_x = screen.right() - hut_w - 80
        hut_y = screen.bottom() - hut_h - 10
    pet.hut.move(hut_x, hut_y)
    if clamp_into_virtual(pet.hut):
        debug_log(f"启动时小屋坐标在屏幕外，已钳回 ({pet.hut.x()},{pet.hut.y()})")

    if pet_cfg:
        pet_x, pet_y = pet_cfg
    else:
        pet_x = hut_x + hut_w // 2 - PET_W // 2
        pet_y = hut_y + hut_h - PET_W
    pet.set_base(QPoint(pet_x, pet_y))
    pet._clamp_on_screen()

    # 托盘
    tray = QSystemTrayIcon(QIcon(pet.frames[0]), app)
    tray.setToolTip("祝尼魔桌面宠物")
    menu = QMenu()

    act_sleep = QAction("睡觉 / 唤醒", menu)
    act_sleep.triggered.connect(pet.toggle_sleep)
    act_todo = QAction("今日待办", menu)
    act_todo.triggered.connect(lambda: pet.todo.toggle_near(pet._base))
    act_show_hut = QAction("隐藏小屋", menu)
    act_hut_visible = [True]

    def toggle_hut():
        act_hut_visible[0] = not act_hut_visible[0]
        visible = act_hut_visible[0]
        hut = pet.hut
        hut.setVisible(visible)
        if visible:
            # 防御：旧坐标/缩放变化可能把小屋留在屏幕外，显示前先钳回来再置顶
            if clamp_into_virtual(hut):
                debug_log(f"显示小屋时钳回屏幕内 -> ({hut.x()},{hut.y()})")
            hut.show()
            hut.raise_()
            pet.raise_()          # 祝尼魔始终在小屋之上
        debug_log(f"托盘切换小屋 -> {'显示' if visible else '隐藏'} (pos={hut.x()},{hut.y()})")
        if pet._fs_hidden:
            pet._fs_restore[id(hut)] = visible   # 全屏期间手动切换，别让恢复逻辑覆盖
        act_show_hut.setText("显示小屋" if not visible else "隐藏小屋")
        pet._raise_stack()

    act_show_hut.triggered.connect(toggle_hut)
    act_quit = QAction("退出", menu)
    act_quit.triggered.connect(app.quit)

    menu.addAction(act_sleep)
    menu.addAction(act_todo)
    menu.addAction(act_show_hut)
    menu.addSeparator()
    menu.addAction(act_quit)
    tray.setContextMenu(menu)
    tray.show()

    def on_quit():
        save_config(pet)

    app.aboutToQuit.connect(on_quit)

    pet.hut.show()
    pet.show()
    return app.exec()


if __name__ == "__main__":
    sys.exit(main())
