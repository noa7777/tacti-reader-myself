import sys
import fitz  # PyMuPDF
import json
import os
import re
import io
import hashlib
import zipfile
import subprocess
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed


import markdown
from PyQt5.QtWidgets import (
    QApplication,
    QMainWindow,
    QLabel,
    QWidget,
    QHBoxLayout,
    QVBoxLayout,
    QFrame,
    QFileDialog,
    QMenuBar,
    QAction,
    QInputDialog,
    QMessageBox,
    QPushButton,
    QColorDialog,
    QDialog,
    QLineEdit,
    QTextEdit,
    QDialogButtonBox,
    QToolBar,
    QComboBox,
    QScrollArea,
    QSizePolicy,
    QLayout,
    QListWidget,
    QListWidgetItem,
    QGroupBox,
    QSplitter,
    QAbstractItemView,
    QTextBrowser,
    QTreeWidget,
    QTreeWidgetItem,
    QTabBar,
    QMenu,
    QShortcut,
    QSpinBox,
    QDoubleSpinBox,
    QCheckBox,
    QFormLayout,
)
from PyQt5.QtCore import (
    Qt,
    QMimeData,
    QPointF,
    QEvent,
    QPoint,
    QRect,
    QRectF,
    pyqtSignal,
    pyqtSlot,
    QUrl,
    QTimer,
    QSize,
)
from PyQt5.QtGui import (
    QPixmap,
    QPainter,
    QImage,
    QDragEnterEvent,
    QDropEvent,
    QPen,
    QBrush,
    QPainterPath,
    QColor,
    QFont,
    QFontDatabase,
    QCursor,
    QLinearGradient,
    QIcon,
    QFontMetrics,
    QTransform,
    QKeyEvent,
    QKeySequence,
)

from tacti_reader.constants import (
    CONFIG_DIR,
    GLOBAL_CONFIG_FILE,
    PEN_COLOR_NAMES,
    PEN_COLOR_PRESETS,
    RECT_COLOR_NAMES,
    RECT_COLOR_PRESETS,
    RENDER_SCALE,
    TEXT_COLOR_NAMES,
    TEXT_COLOR_PRESETS,
)
from tacti_reader.config import ConfigManager
from tacti_reader.utils import get_config_path, resource_path, serialize_annotations


# ==================== 主题系统 ====================

def _hex_to_rgb(hex_color):
    """将 #RRGGBB 转为 (R, G, B) 元组。"""
    hex_color = hex_color.lstrip("#")
    return tuple(int(hex_color[i:i + 2], 16) for i in (0, 2, 4))


def _rgb_to_hex(rgb_tuple):
    """将 (R, G, B) 转回 #RRGGBB 字符串。"""
    return "#{:02x}{:02x}{:02x}".format(
        max(0, min(255, int(round(rgb_tuple[0])))),
        max(0, min(255, int(round(rgb_tuple[1])))),
        max(0, min(255, int(round(rgb_tuple[2])))),
    )


def transform_color(hex_color, W_hex, B_hex):
    """
    根据主题白色 W 和黑色 B，对基础颜色 hex_color 做逐通道线性映射。
    V_out = B_channel + (W_channel - B_channel) * (V_in / 255)
    """
    rgb_in = _hex_to_rgb(hex_color)
    W = _hex_to_rgb(W_hex)
    B = _hex_to_rgb(B_hex)
    out = []
    for v_in, w, b in zip(rgb_in, W, B):
        v_out = b + (w - b) * (v_in / 255.0)
        v_out = round(v_out)
        v_out = max(0, min(255, v_out))
        out.append(v_out)
    return _rgb_to_hex(tuple(out))


def _map_channel(v_in, b, w):
    """单通道线性映射。"""
    return max(0, min(255, round(b + (w - b) * (v_in / 255.0))))


def transform_pixmap(pixmap, W_hex, B_hex, white_threshold=200, grayscale=False, invert=False):
    """
    对 QPixmap 中接近白色的像素逐通道应用主题映射。
    使用 Pillow 的 C 级查表/合成操作，避免 Python 逐像素循环。

    grayscale=False  : 普通主题映射（维持原色，仅替换白/黑端点）
    grayscale='eink' : 电纸书模式 → BT.601灰度 + gamma=1.15 + 中性白映射
    grayscale='night': 黑夜模式   → BT.601灰度 + gamma=0.55 + 颜色反转
    invert=True      : 反色模式 → 颜色完全反转 + 亮度85% + 6500K色温
    """

    # --- 纯 numpy 版（用于测试，不依赖 PyQt/PIL）---
    # 输入：arr (H,W,3) uint8 RGB
    # 输出：处理后的数组
    #
    # gamma_dict = {'eink': 1.15, 'night': 0.55}
    #
    # img = arr.astype(np.float32)
    # Y = 0.299*img[:,:,0] + 0.587*img[:,:,1] + 0.114*img[:,:,2]
    # gamma = gamma_dict.get(grayscale, 1.0)  # grayscale='eink' or 'night'
    # t = (Y / 255.0) ** gamma
    # out = np.empty_like(img)
    # # 统一公式: out = text_color * (1-t) + bg_color * t
    # #         = B_ch + (W_ch - B_ch) * t
    # # 对 eink: B=(0,0,0), W=(255,255,255) → out = W * t
    # # 对 night: B=(232,232,232), W=(42,42,42) → out = 232 - 190*t
    # R = B[0] + (W[0] - B[0]) * t
    # G = B[1] + (W[1] - B[1]) * t
    # B = B[2] + (W[2] - B[2]) * t
    # out[:,:,0] = R; out[:,:,1] = G; out[:,:,2] = B
    # return out.round().astype(np.uint8)
    if pixmap.isNull() or not W_hex or not B_hex:
        return pixmap

    try:
        from io import BytesIO
        from PIL import Image, ImageChops
        from PyQt5.QtCore import QBuffer

        # QPixmap -> BMP bytes -> PIL Image（避免直接操作 QImage 内存，BMP 比 PNG 快）
        buffer = QBuffer()
        buffer.open(QBuffer.ReadWrite)
        pixmap.save(buffer, "BMP")
        bmp_data = bytes(buffer.data().data())
        buffer.close()

        pil_img = Image.open(BytesIO(bmp_data)).convert('RGB')

        W = _hex_to_rgb(W_hex)
        B = _hex_to_rgb(B_hex)

        if grayscale:
            # === 统一灰度映射框架：支持 eink(电纸书)和night(黑夜)两种模式 ===
            #   共同点：BT.601灰度化 → 伽马校正 → 端点色温映射
            #   区别：
            #     * eink:  B=(0,0,0)纯黑, W=(255,255,255)中性白, gamma=1.15
            #       纯黑不变，纯白不变；文字深灰，背景纯白
            #     * night: B=(232,232,232)浅字, W=(42,42,42)深底, gamma=0.55
            #       颜色反转 + 6500K冷白；文字亮灰，背景深灰
            #
            #   统一公式：LUT[v] = B_ch + (W_ch - B_ch) × (v/255)^gamma
            #
            #   v=0(原黑色)时：LUT=B → eink:纯黑, night:浅色文字
            #   v=255(原白色)时：LUT=W → eink:纯白, night:深色背景
            #   中间灰度按伽马曲线在B和W之间插值

            gamma = 1.15 if grayscale == 'eink' else 0.55

            # 预计算 LUT：统一一张表搞定灰度+伽马+色温映射
            lut_r = [int(B[0] + (W[0] - B[0]) * ((v / 255.0) ** gamma)) for v in range(256)]
            lut_g = [int(B[1] + (W[1] - B[1]) * ((v / 255.0) ** gamma)) for v in range(256)]
            lut_b = [int(B[2] + (W[2] - B[2]) * ((v / 255.0) ** gamma)) for v in range(256)]

            gray = pil_img.convert('L')
            r = gray.point(lut_r)
            g = gray.point(lut_g)
            b = gray.point(lut_b)
            result = Image.merge('RGB', (r, g, b))
            print(f"[{grayscale}] gamma={gamma}, B=#{B[0]:02X}{B[1]:02X}{B[2]:02X}, W=#{W[0]:02X}{W[1]:02X}{W[2]:02X}")
        elif invert:
            # 反色模式：颜色完全反转 + 亮度降至85% + 6500K中性白
            # 深灰背景 #2A2A2A，白字 #FFFFFF，避免纯黑背景过刺眼
            r, g, b = pil_img.split()

            # 反转：255 - v，然后乘以0.85降低亮度
            def invert_lut(v):
                return max(0, min(255, round((255 - v) * 0.85)))

            r_inv = r.point(invert_lut)
            g_inv = g.point(invert_lut)
            b_inv = b.point(invert_lut)

            result = Image.merge('RGB', (r_inv, g_inv, b_inv))
        else:
            # 普通主题模式
            # 查找表
            lut_r = [_map_channel(i, B[0], W[0]) for i in range(256)]
            lut_g = [_map_channel(i, B[1], W[1]) for i in range(256)]
            lut_b = [_map_channel(i, B[2], W[2]) for i in range(256)]

            # 分离通道
            r, g, b = pil_img.split()

            # 构建白色背景 mask：RGB 均 >= white_threshold 的像素
            def _mask_band(band):
                return band.point(lambda v: 255 if v >= white_threshold else 0, '1')

            mask = ImageChops.logical_and(_mask_band(r), _mask_band(g))
            mask = ImageChops.logical_and(mask, _mask_band(b))

            # 应用查找表
            r_mapped = r.point(lut_r)
            g_mapped = g.point(lut_g)
            b_mapped = b.point(lut_b)

            # 只在 mask 区域使用映射后的通道，其余保持原样
            r_result = Image.composite(r_mapped, r, mask)
            g_result = Image.composite(g_mapped, g, mask)
            b_result = Image.composite(b_mapped, b, mask)

            result = Image.merge('RGB', (r_result, g_result, b_result))

        # PIL Image -> PNG bytes -> QPixmap
        output = BytesIO()
        result.save(output, format='PNG')
        output.seek(0)
        new_pixmap = QPixmap()
        new_pixmap.loadFromData(output.getvalue())
        return new_pixmap
    except Exception as e:
        import traceback
        print(f"transform_pixmap error: {e}\n{traceback.format_exc()}")
        return pixmap


THEMES = {
    'light': ('#FFFFFF', '#141414'),
    'yellow': ('#F5EFD7', '#141412'),
    'green': ('#C7EDCC', '#101310'),
    'heguang': ('#E0E0E0', '#141414'),
    'eink': ('#F5F0E1', '#1A1A1A'),
    'night': ('#2A2A2A', '#E8E8E8'),
    'invert': ('#FFFFFF', '#2A2A2A'),
}

# 基础调色板
THEME_PALETTE = {
    'bg': '#F5F5F5',
    'fg': '#1A1A1A',
    'button_bg': '#4A90D9',
    'button_fg': '#FFFFFF',
    'entry_bg': '#FFFFFF',
    'entry_fg': '#1A1A1A',
    'label_bg': '#F5F5F5',
    'label_fg': '#1A1A1A',
    'border': '#D9D9D9',
    'menu_bg': '#F5F5F5',
    'menu_fg': '#1A1A1A',
    'highlight': '#4A90D9',
}

THEME_NAMES = {
    'light': '浅色',
    'yellow': '黄色',
    'green': '绿色',
    'heguang': '和光',
    'eink': '电纸书',
    'night': '黑夜',
    'invert': '反色',
}


class BookmarkButton(QLabel):
    bookmarkClicked = pyqtSignal(str)

    def __init__(self, key, page, name, parent=None):
        super().__init__(parent)
        self.key = key
        self.page = page

        display_name = name.strip() or f"P.{page}"
        full_text = f"[{key}] {display_name} (P.{page})"
        self.setText(full_text)
        # 设置字体：中英分离
        font = QFont()
        font.setFamily("Microsoft YaHei, Consolas, Courier New, monospace")
        font.setPointSize(9)
        self.setFont(font)
        # === 支持自动换行 ===
        self.setWordWrap(True)
        self.setAlignment(Qt.AlignLeft | Qt.AlignTop)
        # ==================

        # === 按钮样式 ===
        self.setStyleSheet("""
            QLabel {
                background-color: #f0f0f0;
                border: 1px solid #ccc;
                border-radius: 4px;
                padding: 6px;
                margin: 2px;
            }
            QLabel:hover {
                background-color: #e0e0e0;
                border: 1px solid #999;
            }
        """)
        self.setCursor(Qt.PointingHandCursor)
        # ==============

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            self.bookmarkClicked.emit(self.key)
        super().mousePressEvent(event)


class InlineTextEdit(QTextEdit):
    """内联文本编辑器"""

    textConfirmed = pyqtSignal(str)
    editingCancelled = pyqtSignal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptRichText(False)
        self.setLineWrapMode(QTextEdit.WidgetWidth)
        self.setWordWrapMode(True)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Escape:
            self.editingCancelled.emit()
        elif event.key() == Qt.Key_Return and event.modifiers() == Qt.ControlModifier:
            # Ctrl+Enter 确认
            self.textConfirmed.emit(self.toPlainText())
        elif event.key() == Qt.Key_Return and event.modifiers() == Qt.NoModifier:
            # Enter 键换行
            self.insertPlainText("\n")
        elif event.key() == Qt.Key_Enter and event.modifiers() == Qt.NoModifier:
            # 小键盘 Enter 键换行
            self.insertPlainText("\n")
        else:
            super().keyPressEvent(event)

    def focusOutEvent(self, event):
        # 不自动确认/取消，由父窗格主动管理
        super().focusOutEvent(event)


# === 首次运行语言选择对话框 ===
class LanguageSelectDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("TactiReader - Choose Language")
        self.setFixedSize(320, 130)
        layout = QVBoxLayout(self)
        layout.addWidget(QLabel("Please choose your language:\n请选择您的语言："))
        self.btn_en = QPushButton("English")
        self.btn_zh = QPushButton("简体中文")
        layout.addWidget(self.btn_en)
        layout.addWidget(self.btn_zh)

        self.selected_lang = "en"
        self.btn_en.clicked.connect(lambda: self.accept_with("en"))
        self.btn_zh.clicked.connect(lambda: self.accept_with("zh"))

    def accept_with(self, lang):
        self.selected_lang = lang
        self.accept()


# ==============================
class SearchDialog(QDialog):
    """增强的搜索对话框"""

    searchResultSelected = pyqtSignal(int, str)  # page_num, matched_text

    def __init__(self, parent=None, pdf_doc=None):
        super().__init__(parent)
        self.doc = pdf_doc
        self.results = []
        self.current_search_index = 0

        self.setWindowTitle(QApplication.instance().activeWindow().tr("Search in PDF"))

        # 窗口大小：宽占屏幕 3/5，高占屏幕 7/10
        screen = QApplication.primaryScreen().geometry()
        self.resize(int(screen.width() * 3 / 5), int(screen.height() * 7 / 10))

        # 全局字体 21pt
        font = QFont()
        font.setPointSize(21)
        self.setFont(font)

        layout = QVBoxLayout(self)

        # 搜索框
        search_layout = QHBoxLayout()
        search_label = QLabel(QApplication.instance().activeWindow().tr("Search:"))
        search_label.setFont(font)
        search_layout.addWidget(search_label)
        self.search_input = QLineEdit()
        self.search_input.setFont(font)
        self.search_input.setPlaceholderText(
            QApplication.instance().activeWindow().tr("Enter search term...")
        )
        self.search_input.returnPressed.connect(self.perform_search)
        search_layout.addWidget(self.search_input)

        self.search_button = QPushButton(
            QApplication.instance().activeWindow().tr("Search")
        )
        self.search_button.setFont(font)
        self.search_button.clicked.connect(self.perform_search)
        search_layout.addWidget(self.search_button)

        self.case_sensitive_check = QPushButton("Aa")
        self.case_sensitive_check.setFont(font)
        self.case_sensitive_check.setCheckable(True)
        self.case_sensitive_check.setToolTip("Case Sensitive")
        search_layout.addWidget(self.case_sensitive_check)

        layout.addLayout(search_layout)

        # 结果统计
        self.result_count_label = QLabel(
            QApplication.instance().activeWindow().tr("No results")
        )
        self.result_count_label.setFont(font)
        layout.addWidget(self.result_count_label)

        # 结果列表
        self.results_list = QListWidget()
        self.results_list.setFont(font)
        self.results_list.itemClicked.connect(self.on_result_clicked)
        self.results_list.itemDoubleClicked.connect(self.on_result_double_clicked)
        layout.addWidget(self.results_list)

        # 导航按钮
        nav_layout = QHBoxLayout()
        self.prev_button = QPushButton(
            QApplication.instance().activeWindow().tr("◀ Previous")
        )
        self.prev_button.setFont(font)
        self.prev_button.clicked.connect(self.go_to_previous)
        self.prev_button.setEnabled(False)
        nav_layout.addWidget(self.prev_button)

        self.next_button = QPushButton(
            QApplication.instance().activeWindow().tr("Next ▶")
        )
        self.next_button.setFont(font)
        self.next_button.clicked.connect(self.go_to_next)
        self.next_button.setEnabled(False)
        nav_layout.addWidget(self.next_button)

        nav_layout.addStretch()

        self.close_button = QPushButton(
            QApplication.instance().activeWindow().tr("Close")
        )
        self.close_button.setFont(font)
        self.close_button.clicked.connect(self.close)
        nav_layout.addWidget(self.close_button)

        layout.addLayout(nav_layout)

    def perform_search(self):
        """执行搜索"""
        if not self.doc:
            return

        search_term = self.search_input.text().strip()
        if not search_term:
            return

        self.results_list.clear()
        self.results = []
        self.current_search_index = 0

        # 搜索所有页面
        for page_num in range(len(self.doc)):
            page = self.doc[page_num]
            try:
                # 获取页面文本
                text = page.get_text()

                # 搜索
                if self.case_sensitive_check.isChecked():
                    indices = []
                    start = 0
                    while True:
                        idx = text.find(search_term, start)
                        if idx == -1:
                            break
                        indices.append(idx)
                        start = idx + 1
                else:
                    search_term_lower = search_term.lower()
                    text_lower = text.lower()
                    indices = []
                    start = 0
                    while True:
                        idx = text_lower.find(search_term_lower, start)
                        if idx == -1:
                            break
                        indices.append(idx)
                        start = idx + 1

                # 为每个匹配创建结果
                for idx in indices:
                    # 获取上下文
                    context_start = max(0, idx - 40)
                    context_end = min(len(text), idx + len(search_term) + 40)
                    context = text[context_start:context_end]

                    # 高亮搜索词
                    highlight_start = idx - context_start
                    highlight_end = highlight_start + len(search_term)
                    context = (
                        context[:highlight_start]
                        + "**"
                        + context[highlight_start:highlight_end]
                        + "**"
                        + context[highlight_end:]
                    )

                    result = {
                        "page": page_num + 1,
                        "context": context.strip(),
                        "position": idx,
                    }
                    self.results.append(result)

            except Exception as e:
                print(f"Error searching page {page_num}: {e}")

        # 更新UI
        self.update_results_list()
        # === 新增：通知主窗口执行高亮 ===
        if hasattr(self.parent(), "search_text_with_highlight"):
            self.parent().search_text_with_highlight(
                search_term, self.case_sensitive_check.isChecked()
            )
        # =================================

    def on_result_clicked(self, item):
        """单击：仅跳转"""
        index = item.data(Qt.UserRole)
        if 0 <= index < len(self.results):
            result = self.results[index]
            self.searchResultSelected.emit(result["page"], result["context"])
            # 注意：这里不调用 self.accept()

    def on_result_double_clicked(self, item):
        """双击：跳转并关闭对话框"""
        index = item.data(Qt.UserRole)
        if 0 <= index < len(self.results):
            result = self.results[index]
            self.searchResultSelected.emit(result["page"], result["context"])
            self.accept()  # 关闭对话框

    def update_results_list(self):
        """更新结果列表"""
        self.results_list.clear()

        for i, result in enumerate(self.results):
            item_text = f"Page {result['page']}: {result['context']}"
            item = QListWidgetItem(item_text)
            item.setData(Qt.UserRole, i)  # 存储索引
            self.results_list.addItem(item)

        # 更新统计
        count = len(self.results)
        self.result_count_label.setText(
            QApplication.instance().activeWindow().tr("Found {count} result(s)")
        )

        # 更新按钮状态
        self.prev_button.setEnabled(count > 0)
        self.next_button.setEnabled(count > 0)

    def go_to_previous(self):
        """跳转到上一个结果"""
        if not self.results:
            return

        self.current_search_index = (self.current_search_index - 1) % len(self.results)
        result = self.results[self.current_search_index]
        self.searchResultSelected.emit(result["page"], result["context"])

        # 高亮当前项
        for i in range(self.results_list.count()):
            if self.results_list.item(i).data(Qt.UserRole) == self.current_search_index:
                self.results_list.setCurrentRow(i)
                break

    def go_to_next(self):
        """跳转到下一个结果"""
        if not self.results:
            return

        self.current_search_index = (self.current_search_index + 1) % len(self.results)
        result = self.results[self.current_search_index]
        self.searchResultSelected.emit(result["page"], result["context"])

        # 高亮当前项
        for i in range(self.results_list.count()):
            if self.results_list.item(i).data(Qt.UserRole) == self.current_search_index:
                self.results_list.setCurrentRow(i)
                break


class TocTreeNode:
    """PDF TOC tree node"""

    _counter = 0

    def __init__(self, level, title, page, depth=1):
        self.level = level
        self.title = title
        self.page = page
        self.depth = depth
        self.children = []
        TocTreeNode._counter += 1
        self.node_id = f"{depth}-{TocTreeNode._counter}-{title}"
        self.is_leaf = True

    def add_child(self, child):
        self.children.append(child)
        self.is_leaf = False


class FlowLayout(QLayout):
    """Flow layout that wraps items horizontally when width is exceeded."""

    def __init__(self, parent=None, margin=0, spacing=-1):
        super().__init__(parent)
        if margin >= 0:
            self.setContentsMargins(margin, margin, margin, margin)
        self.setSpacing(spacing if spacing >= 0 else 4)
        self._items = []

    def __del__(self):
        item = self.takeAt(0)
        while item:
            item = self.takeAt(0)

    def addItem(self, item):
        self._items.append(item)

    def count(self):
        return len(self._items)

    def itemAt(self, index):
        if 0 <= index < len(self._items):
            return self._items[index]
        return None

    def takeAt(self, index):
        if 0 <= index < len(self._items):
            return self._items.pop(index)
        return None

    def expandingDirections(self):
        return Qt.Orientations(Qt.Orientation(0))

    def hasHeightForWidth(self):
        return True

    def heightForWidth(self, width):
        return self._doLayout(QRect(0, 0, width, 0), True)

    def setGeometry(self, rect):
        super().setGeometry(rect)
        self._doLayout(rect, False)

    def sizeHint(self):
        return self.minimumSize()

    def minimumSize(self):
        size = QSize()
        for item in self._items:
            size = size.expandedTo(item.minimumSize())
        margin = self.contentsMargins()
        size += QSize(margin.left() + margin.right(), margin.top() + margin.bottom())
        return size

    def _doLayout(self, rect, testOnly):
        x = rect.x()
        y = rect.y()
        lineHeight = 0
        spaceX = self.spacing()
        spaceY = self.spacing()
        for item in self._items:
            widget = item.widget()
            nextX = x + item.sizeHint().width() + spaceX
            if nextX - spaceX > rect.right() and lineHeight > 0:
                x = rect.x()
                y += lineHeight + spaceY
                nextX = x + item.sizeHint().width() + spaceX
                lineHeight = 0
            if not testOnly:
                item.setGeometry(QRect(QPoint(x, y), item.sizeHint()))
            x = nextX
            lineHeight = max(lineHeight, item.sizeHint().height())
        return y + lineHeight - rect.y()


class TocDialog(QDialog):
    """PDF TOC navigation dialog with layer-by-layer button display"""

    nodeSelected = pyqtSignal(int)  # page number

    def __init__(self, pdf_toc, parent=None, theme_name='light', colors=None, bookmarks=None):
        super().__init__(parent)
        self.raw_toc = pdf_toc
        self.tree_root = []
        self.all_nodes = {}  # node_id -> node mapping for depth calculation
        self.selectedId = ""  # 当前选中的节点 ID（持久化）
        self.search_mode = False  # 是否处于搜索模式
        self.theme_name = theme_name
        self.bookmarks = bookmarks or {}  # {"Q": {"page": 1, "name": "..."}, ...}
        if colors is None:
            W_hex, B_hex = THEMES.get(theme_name, THEMES['light'])
            self.colors = {key: transform_color(value, W_hex, B_hex) for key, value in THEME_PALETTE.items()}
        else:
            self.colors = colors

        self.setWindowTitle("目录导航")
        # 窗口大小：占屏幕的 3/5，并居中
        screen_geo = QApplication.primaryScreen().availableGeometry()
        w = int(screen_geo.width() * 0.6)
        h = int(screen_geo.height() * 0.6)
        self.setGeometry(
            screen_geo.x() + (screen_geo.width() - w) // 2,
            screen_geo.y() + (screen_geo.height() - h) // 2,
            w,
            h,
        )

        # Restore state from parent if available
        if hasattr(parent, "toc_state"):
            self.selectedId = parent.toc_state[1]  # 只恢复 selectedId，深度由选中节点决定

        self._build_tree()
        self._setup_ui()
        self._render()

    def _setup_ui(self):
        self.setStyleSheet(f"QDialog {{ background-color: {self.colors['bg']}; }}")
        main_layout = QVBoxLayout(self)

        # 搜索栏
        search_layout = QHBoxLayout()
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("搜索目录...")
        self.search_input.setStyleSheet(f"""
            QLineEdit {{
                padding: 6px 10px;
                font-size: 12pt;
                border: 1px solid {self.colors['border']};
                border-radius: 4px;
                background-color: {self.colors['entry_bg']};
                color: {self.colors['entry_fg']};
            }}
        """)
        self.search_input.returnPressed.connect(self._perform_search)
        search_layout.addWidget(self.search_input, 1)

        search_btn = QPushButton("搜索")
        search_btn.clicked.connect(self._perform_search)
        search_layout.addWidget(search_btn)
        main_layout.addLayout(search_layout)

        self.scroll_area = QScrollArea()
        self.scroll_area.setWidgetResizable(True)
        self.scroll_content = QWidget()
        self.scroll_layout = QVBoxLayout(self.scroll_content)
        self.scroll_layout.setSpacing(8)
        self.scroll_layout.setContentsMargins(8, 8, 8, 8)
        self.scroll_area.setWidget(self.scroll_content)
        main_layout.addWidget(self.scroll_area)

        button_box = QHBoxLayout()
        button_box.addStretch()
        self.back_btn = QPushButton("返回")
        self.back_btn.clicked.connect(self._back_to_navigation)
        self.back_btn.setVisible(False)
        button_box.addWidget(self.back_btn)
        close_btn = QPushButton("关闭")
        close_btn.clicked.connect(self.reject)
        button_box.addWidget(close_btn)
        main_layout.addLayout(button_box)

    def _build_tree(self):
        """Convert flat (level, title, page) list to nested tree structure."""
        if not self.raw_toc:
            return

        # 重置计数器，确保每次打开对话框生成的 node_id 一致（持久化 selectedId 才能匹配）
        TocTreeNode._counter = 0

        self.tree_root = []
        self.all_nodes = {}
        node_stack = []  # (node, level)

        for lvl, title, page in self.raw_toc:
            node = TocTreeNode(lvl, title, page)
            self.all_nodes[node.node_id] = node

            if not node_stack:
                self.tree_root.append(node)
                node_stack.append((node, lvl))
                continue

            # Find proper parent
            while node_stack and node_stack[-1][1] >= lvl:
                node_stack.pop()

            if node_stack:
                node.depth = node_stack[-1][0].depth + 1
                TocTreeNode._counter += 1
                node.node_id = f"{node.depth}-{TocTreeNode._counter}-{title}"
                self.all_nodes[node.node_id] = node
                node_stack[-1][0].add_child(node)
            else:
                self.tree_root.append(node)

            node_stack.append((node, lvl))

    def _render(self):
        """Clear and rebuild UI based on selectedId.
        
        显示规则：
        - 从第1层到选中节点的深度（如果选中节点有子节点则多显示一层）
        - 高亮：选中节点本身 + 所有祖先节点
        """
        while self.scroll_layout.count():
            item = self.scroll_layout.takeAt(0)
            if item.widget():
                item.widget().deleteLater()

        if not self.tree_root:
            label = QLabel("该 PDF 没有目录")
            label.setAlignment(Qt.AlignCenter)
            label.setStyleSheet(f"color: {self.colors['fg']}; font-size: 14px;")
            self.scroll_layout.addWidget(label)
            return

        # 书签区块（标签）—— 无书签时不显示
        has_bookmarks = bool(self.bookmarks)
        if has_bookmarks:
            bookmark_container = self._create_bookmark_container()
            if bookmark_container:
                self.scroll_layout.addWidget(bookmark_container)

        # 找到选中节点和祖先链路
        selected_node = self.all_nodes.get(self.selectedId)
        ancestor_chain = []  # [root, ..., parent, selected]
        ancestor_ids = set()
        if selected_node:
            ancestor_chain = self._get_ancestor_chain(selected_node)
            ancestor_ids = {n.node_id for n in ancestor_chain}

        # 计算显示范围：从第1层到 max_depth
        if selected_node:
            max_depth = selected_node.depth
            # 如果选中的是父节点（有子节点），多显示一层子节点
            if not selected_node.is_leaf:
                max_depth += 1
        else:
            # 无选中节点，只显示第1层
            max_depth = 1

        # 构建每层要显示的节点
        nodes_by_depth = {}
        nodes_by_depth[1] = self.tree_root

        current_level_nodes = self.tree_root
        for d in range(2, max_depth + 1):
            # 在当前层的候选节点中，找到祖先链上的那个节点
            found_parent = None
            for n in current_level_nodes:
                if n.node_id in ancestor_ids:
                    found_parent = n
                    break
            
            if found_parent and found_parent.children:
                nodes_by_depth[d] = found_parent.children
                current_level_nodes = found_parent.children
            else:
                # 祖先链上该层无节点或无子节点，停止展开
                break

        # 高亮集合 = 祖先链上所有节点 + 选中节点本身
        highlighted_ids = ancestor_ids.copy()
        if self.selectedId:
            highlighted_ids.add(self.selectedId)

        # 标签与第1层之间有标签按钮且第1层有按钮时，显示粗分割线
        has_level1 = bool(nodes_by_depth.get(1))
        if has_bookmarks and has_level1:
            separator = QWidget()
            separator.setFixedHeight(4)
            separator.setStyleSheet(f"background-color: {self.colors['border']}; border: none; margin: 4px 0;")
            self.scroll_layout.addWidget(separator)

        actual_max = max(nodes_by_depth.keys()) if nodes_by_depth else 1
        for d in range(1, actual_max + 1):
            nodes = nodes_by_depth.get(d, [])
            if not nodes:
                continue
            container = self._create_level_container(d, nodes, highlighted_ids)
            self.scroll_layout.addWidget(container)

        self.scroll_layout.addStretch()

    def _get_ancestor_chain(self, target_node):
        """获取从根节点到目标节点的完整祖先链路（含目标节点本身）。"""
        chain = []
        self._collect_ancestors(self.tree_root, target_node.node_id, chain)
        return chain

    def _collect_ancestors(self, nodes, target_id, chain):
        """递归收集祖先节点。返回是否找到目标。"""
        for node in nodes:
            if node.node_id == target_id:
                chain.append(node)
                return True
            if node.children:
                if self._collect_ancestors(node.children, target_id, chain):
                    chain.insert(0, node)  # 祖先插在前面
                    return True
        return False

    def _trace_ancestors(self, nodes, target_id, result_set):
        """Trace ancestors of target_id and add them to result_set."""
        for node in nodes:
            if node.node_id == target_id:
                return True
            if node.children:
                if self._trace_ancestors(node.children, target_id, result_set):
                    result_set.add(node.node_id)
                    return True
        return False

    def _create_bookmark_container(self):
        """创建书签区块，样式与目录层级容器一致。无书签返回 None。"""
        if not self.bookmarks:
            return None

        container = QFrame()
        container.setFrameShape(QFrame.StyledPanel)
        container.setStyleSheet(f"""
            QFrame {{
                background-color: {self.colors['bg']};
                border: 1px solid {self.colors['border']};
                border-radius: 4px;
            }}
        """)

        layout = QVBoxLayout(container)
        layout.setContentsMargins(6, 4, 6, 4)
        layout.setSpacing(4)

        label = QLabel("标签")
        label.setStyleSheet(f"color: {self.colors['fg']}; font-size: 11px;")
        layout.addWidget(label)

        buttons_widget = QWidget()
        buttons_layout = FlowLayout(buttons_widget, margin=0, spacing=8)

        for char in ["Q", "W", "E", "R", "T", "Y", "U", "I", "O", "P"]:
            if char not in self.bookmarks:
                continue
            bm = self.bookmarks[char]
            page = bm["page"]
            name = bm.get("name", "").strip() or f"P.{page}"
            btn_text = f"[{char}] {name}"
            btn = QPushButton(btn_text)
            btn.setFlat(True)
            btn.setSizePolicy(QSizePolicy.Minimum, QSizePolicy.Fixed)
            btn.setStyleSheet(f"""
                QPushButton {{
                    background-color: #F0F0F0;
                    color: #000000;
                    border: 1px solid #CCC;
                    border-radius: 3px;
                    padding: 6px 10px;
                    font-size: 12pt;
                }}
                QPushButton:hover {{
                    background-color: #E0E0E0;
                }}
            """)
            btn.clicked.connect(lambda checked, p=page: self._on_bookmark_click(p))
            buttons_layout.addWidget(btn)

        layout.addWidget(buttons_widget)
        return container

    def _on_bookmark_click(self, page):
        """点击书签按钮：跳转页码 + 关闭对话框。"""
        self.nodeSelected.emit(page)
        self.accept()

    def _create_level_container(self, depth, nodes, highlighted_ids):
        """Create a bordered container with label and buttons for one depth level."""
        container = QFrame()
        container.setFrameShape(QFrame.StyledPanel)
        container.setStyleSheet(f"""
            QFrame {{
                background-color: {self.colors['bg']};
                border: 1px solid {self.colors['border']};
                border-radius: 4px;
            }}
        """)

        layout = QVBoxLayout(container)
        layout.setContentsMargins(6, 4, 6, 4)
        layout.setSpacing(4)

        # Label
        label = QLabel(f"第{depth}层")
        label.setStyleSheet(f"color: {self.colors['fg']}; font-size: 11px;")
        layout.addWidget(label)

        # Buttons wrapper with flow layout
        buttons_widget = QWidget()
        buttons_layout = FlowLayout(buttons_widget, margin=0, spacing=8)

        for node in nodes:
            btn = self._create_button(node, highlighted_ids)
            buttons_layout.addWidget(btn)

        layout.addWidget(buttons_widget)
        return container

    def _create_button(self, node, highlighted_ids):
        """Create a button for a TOC node."""
        btn = QPushButton(node.title)
        btn.setFlat(True)
        btn.setSizePolicy(QSizePolicy.Minimum, QSizePolicy.Fixed)
        btn.setProperty("toc_node_id", node.node_id)

        is_selected = (node.node_id in highlighted_ids)

        if is_selected:
            btn.setStyleSheet(f"""
                QPushButton {{
                    background-color: {self.colors['highlight']};
                    color: {self.colors['button_fg']};
                    border: 1px solid {self.colors['highlight']};
                    border-radius: 3px;
                    padding: 6px 10px;
                    font-size: 12pt;
                }}
                QPushButton:hover {{
                    background-color: {self.colors['button_bg']};
                }}
            """)
        else:
            btn.setStyleSheet("""
                QPushButton {
                    background-color: #F0F0F0;
                    color: #000000;
                    border: 1px solid #CCC;
                    border-radius: 3px;
                    padding: 6px 10px;
                    font-size: 12pt;
                }
                QPushButton:hover {
                    background-color: #E0E0E0;
                }
            """)

        btn.clicked.connect(lambda checked, n=node: self._on_node_click(n))
        return btn

    def _on_node_click(self, node):
        """Handle node click event.
        
        规则：
        1. 任何节点点击后都先高亮（设置 selectedId）
        2. 叶子节点（无子节点）→ 跳转到页码 + 关闭对话框
        3. 父节点（有子节点）→ 高亮 + 展开子节点
        """
        # 先高亮
        self.selectedId = node.node_id

        if node.is_leaf:
            # 叶子节点：跳转 + 关闭对话框
            self.nodeSelected.emit(node.page)
            self.accept()
        else:
            # 有子节点：重新渲染以展开下一层
            self._render()
            # 滚动到底部显示新展开的层
            QTimer.singleShot(50, lambda: self.scroll_area.verticalScrollBar().setValue(
                self.scroll_area.verticalScrollBar().maximum()
            ))

    def _collect_nodes_at_depth(self, target_depth):
        """Collect all nodes at a specific depth level."""
        result = []
        self._collect_recursive(self.tree_root, target_depth, result)
        return result

    def _collect_recursive(self, nodes, target_depth, result):
        for node in nodes:
            if node.depth == target_depth:
                result.append(node)
            if node.depth < target_depth:
                self._collect_recursive(node.children, target_depth, result)

    def _get_max_depth(self):
        """Get the maximum depth in the tree."""
        max_d = 0
        for node in self.all_nodes.values():
            if node.depth > max_d:
                max_d = node.depth
        return max_d

    def get_state(self):
        """Return current state for persistence.
        
        返回值：(maxVisibleDepth, selectedId)
        maxVisibleDepth 已废弃（由选中节点深度自动计算），
        保留兼容性；selectedId 是核心持久化数据。
        """
        return (0, self.selectedId)  # maxVisibleDepth 设为 0 表示"自动"

    def set_state(self, max_visible_depth, selected_id):
        """Restore state."""
        if selected_id and selected_id in self.all_nodes:
            self.selectedId = selected_id
        else:
            self.selectedId = ""
        self._render()

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Escape:
            if self.search_mode:
                self._back_to_navigation()
                event.accept()
            else:
                super().keyPressEvent(event)
        else:
            super().keyPressEvent(event)

    def _perform_search(self):
        """执行目录搜索，每个结果附带完整路径"""
        keyword = self.search_input.text().strip()
        if not keyword or not self.all_nodes:
            return
        results = []  # [(node, path_string), ...]
        for node in self.all_nodes.values():
            if keyword.lower() in node.title.lower():
                ancestors = self._get_ancestor_chain(node)
                path_parts = [n.title for n in ancestors]
                path_str = "/".join(path_parts)
                results.append((node, path_str))
        if not results:
            return
        results.sort(key=lambda x: (x[0].depth, x[0].page))
        self.search_mode = True
        self._show_search_results(results)

    def _show_search_results(self, results):
        """显示搜索结果界面（紧凑列表，行间距1.3倍字高）"""
        while self.scroll_layout.count():
            item = self.scroll_layout.takeAt(0)
            if item.widget():
                item.widget().deleteLater()

        # 搜索结果标题
        title_label = QLabel(f"找到 {len(results)} 个匹配项")
        title_label.setStyleSheet(
            f"color: {self.colors['fg']}; font-size: 12px; padding: 4px 0;"
        )
        title_label.setAlignment(Qt.AlignCenter)
        self.scroll_layout.addWidget(title_label)

        for node, path_str in results:
            btn = QPushButton(path_str)
            btn.setFlat(True)
            btn.setCursor(Qt.PointingHandCursor)
            btn.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
            btn.setStyleSheet(f"""
                QPushButton {{
                    background-color: transparent;
                    color: {self.colors['fg']};
                    border: none;
                    border-radius: 2px;
                    padding: 2px 8px;
                    font-size: 12pt;
                    text-align: left;
                }}
                QPushButton:hover {{
                    background-color: {self.colors['highlight']}40;
                }}
            """)
            btn.clicked.connect(lambda checked, n=node: self._on_search_result_click(n))
            self.scroll_layout.addWidget(btn)

        self.scroll_layout.addStretch()
        self.back_btn.setVisible(True)

    def _on_search_result_click(self, node):
        """点击搜索结果：跳转到对应页面 + 持久化选中高亮"""
        self.selectedId = node.node_id
        self.nodeSelected.emit(node.page)
        self.accept()

    def _back_to_navigation(self):
        """从搜索模式返回导航模式"""
        self.search_mode = False
        self.search_input.clear()
        self.back_btn.setVisible(False)
        self._render()


class EpubPreviewPane(QLabel):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAlignment(Qt.AlignCenter)
        self.setStyleSheet("background: #2b2b2b;")
        self.setMinimumSize(200, 300)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.page_pixmap = None
        self.scale_factor = 1.0
        self.offset = QPointF(0, 0)

    def set_page(self, pixmap):
        self.page_pixmap = pixmap
        self.update()

    def mousePressEvent(self, event):
        if self.parent() and hasattr(self.parent(), "setFocus"):
            self.parent().setFocus()
        super().mousePressEvent(event)

    def paintEvent(self, event):
        super().paintEvent(event)
        if not self.page_pixmap:
            return
        painter = QPainter(self)
        painter.setRenderHint(QPainter.SmoothPixmapTransform)
        max_h = self.height()
        scale = max_h / self.page_pixmap.height()
        scaled_w = int(self.page_pixmap.width() * scale)
        scaled_h = max_h
        scaled = self.page_pixmap.scaled(scaled_w, scaled_h, Qt.IgnoreAspectRatio, Qt.SmoothTransformation)
        x = (self.width() - scaled_w) // 2
        y = 0
        painter.drawPixmap(x, y, scaled)


class DraggableWidget(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.drag_pos = None

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            self.drag_pos = event.globalPos() - self.frameGeometry().topLeft()
            event.accept()

    def mouseMoveEvent(self, event):
        if self.drag_pos and event.buttons() == Qt.LeftButton:
            self.move(event.globalPos() - self.drag_pos)
            event.accept()

    def mouseReleaseEvent(self, event):
        self.drag_pos = None


def _build_apply_css(params):
    fontsize = params.get("fontsize", 25)
    line_height = params.get("line_height", 1.3)
    para_spacing = params.get("para_spacing", 3)
    indent_chars = params.get("indent_chars", 2)
    justify = params.get("justify", False)
    mt = params.get("margin_top", 0)
    mb = params.get("margin_bottom", 0)
    ml = params.get("margin_left", 20)
    mr = params.get("margin_right", 20)
    ta = "justify" if justify else "left"

    css = f"@page {{ margin-top: {mt}pt; margin-bottom: {mb}pt; margin-left: {ml}pt; margin-right: {mr}pt; }}"
    block_sel = "body, p, div, span, h1, h2, h3, h4, h5, h6, li, td, th, article, section, nav, header, footer, aside, blockquote, pre, code, ul, ol, dl, dt, dd, figure, figcaption"
    css += f"{block_sel} {{ line-height: {line_height} !important; }}"
    p_sel = "p, div, li, td, th, blockquote, article, section, nav, header, footer, aside, figure, figcaption, dd, dt"
    css += f"{p_sel} {{ text-indent: {indent_chars}em !important; text-align: {ta} !important; margin-top: 0 !important; margin-bottom: {para_spacing}pt !important; }}"
    css += f"h1, h2, h3, h4, h5, h6 {{ text-indent: 0 !important; text-align: left !important; margin-top: {para_spacing * 2}pt !important; margin-bottom: {para_spacing}pt !important; }}"
    css += f"ul, ol {{ margin-top: 0 !important; margin-bottom: {para_spacing}pt !important; padding-left: 2em !important; }}"
    return css


def _modify_epub_css_in_memory(epub_bytes, extra_css):
    """PyMuPDF的apply_css()对EPUB无效，需要直接修改EPUB内部的CSS文件。
    返回修改后的EPUB字节流。
    """
    import io
    import zipfile

    extra_rule = "\n/* TactiReader injected */\n" + extra_css + "\n"

    out_buf = io.BytesIO()
    try:
        with zipfile.ZipFile(io.BytesIO(epub_bytes), "r") as zin:
            with zipfile.ZipFile(out_buf, "w", zipfile.ZIP_DEFLATED) as zout:
                for item in zin.infolist():
                    data = zin.read(item.filename)
                    if item.filename.lower().endswith(".css"):
                        try:
                            text = data.decode("utf-8", errors="ignore")
                            if "TactiReader injected" not in text:
                                text += extra_rule
                            data = text.encode("utf-8")
                        except Exception:
                            pass
                    zout.writestr(item, data)
    except Exception as e:
        print(f"[_modify_epub_css_in_memory] failed: {e}")
        return epub_bytes, False
    return out_buf.getvalue(), True


class EpubPreviewDialog(QDialog):
    def __init__(self, epub_path, initial_params=None, parent=None):
        super().__init__(parent)
        self.epub_path = epub_path
        self.doc = None
        self.current_page = 0
        self.result_params = None
        self._resize_timer = QTimer(self)
        self._resize_timer.setSingleShot(True)
        self._resize_timer.timeout.connect(self._do_relayout)
        self._raw_epub_data = None

        if not os.path.isfile(epub_path):
            QMessageBox.critical(self, "Error", f"EPUB file not found:\n{epub_path}")
            return

        try:
            with open(epub_path, "rb") as f:
                self._raw_epub_data = f.read()
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to read EPUB:\n{e}")
            return

        self.setWindowTitle("EPUB Preview")
        self.setWindowFlags(Qt.Window | Qt.FramelessWindowHint)
        self.showFullScreen()
        self.setStyleSheet("background: #2b2b2b;")
        self.setFocusPolicy(Qt.StrongFocus)

        main_layout = QVBoxLayout(self)
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)

        pages_widget = QWidget()
        pages_layout = QHBoxLayout(pages_widget)
        pages_layout.setSpacing(0)
        pages_layout.setContentsMargins(0, 0, 0, 0)

        self.left_pane = EpubPreviewPane(self)
        self.right_pane = EpubPreviewPane(self)
        pages_layout.addWidget(self.left_pane, 1)
        pages_layout.addWidget(self.right_pane, 1)
        main_layout.addWidget(pages_widget, 1)

        self.status_label = QLabel("Loading...", self)
        self.status_label.setStyleSheet("color: #cccccc; font-size: 14px;")
        self.status_label.setAlignment(Qt.AlignRight | Qt.AlignVCenter)
        main_layout.addWidget(self.status_label)

        self.floating = DraggableWidget(self)
        self.floating.setStyleSheet("""
            background: rgba(40, 40, 40, 235);
            border: 1px solid #666;
            border-radius: 8px;
            color: #eee;
        """)
        flo_layout = QVBoxLayout(self.floating)
        flo_layout.setContentsMargins(12, 12, 12, 12)
        flo_layout.setSpacing(8)

        input_style = """
            QSpinBox, QDoubleSpinBox, QComboBox {
                background: #f0f0f0;
                color: #000;
                border: 1px solid #999;
                border-radius: 3px;
                padding: 2px 4px;
            }
            QPushButton {
                background: #555;
                color: #fff;
                border: 1px solid #888;
                border-radius: 4px;
                padding: 5px 15px;
                min-width: 60px;
            }
            QPushButton:hover { background: #777; }
            QPushButton:pressed { background: #333; }
            QCheckBox { color: #eee; spacing: 6px; }
            QLabel { color: #ddd; background: transparent; }
        """

        title = QLabel("排版设置", self.floating)
        title.setStyleSheet("font-size: 14pt; font-weight: bold; color: #fff; padding-bottom: 4px;")
        flo_layout.addWidget(title)

        self.fontsize_spin = QSpinBox(self.floating)
        self.fontsize_spin.setRange(8, 48)
        self.fontsize_spin.setValue(25)
        self.fontsize_spin.setSuffix(" pt")
        self._add_row(flo_layout, "字号:", self.fontsize_spin)

        self.lineheight_spin = QDoubleSpinBox(self.floating)
        self.lineheight_spin.setRange(1.0, 2.5)
        self.lineheight_spin.setSingleStep(0.1)
        self.lineheight_spin.setValue(1.3)
        self._add_row(flo_layout, "行高:", self.lineheight_spin)

        self.paraspacing_spin = QSpinBox(self.floating)
        self.paraspacing_spin.setRange(0, 32)
        self.paraspacing_spin.setSingleStep(2)
        self.paraspacing_spin.setValue(3)
        self.paraspacing_spin.setSuffix(" pt")
        self._add_row(flo_layout, "段落间距:", self.paraspacing_spin)

        self.indent_spin = QSpinBox(self.floating)
        self.indent_spin.setRange(0, 8)
        self.indent_spin.setValue(2)
        self.indent_spin.setSuffix(" 字符")
        self._add_row(flo_layout, "首行缩进:", self.indent_spin)

        self.justify_check = QCheckBox("两端对齐", self.floating)
        self.justify_check.setChecked(False)
        flo_layout.addWidget(self.justify_check)

        self.weight_combo = QComboBox(self.floating)
        self.weight_combo.addItems(["正常", "加粗", "lighter", "bolder"])
        self._add_row(flo_layout, "字体粗细:", self.weight_combo)

        self.page_width_spin = QSpinBox(self.floating)
        self.page_width_spin.setRange(40, 50)
        self.page_width_spin.setValue(45)
        self.page_width_spin.setSuffix(" %")
        self._add_row(flo_layout, "页面宽度:", self.page_width_spin)

        margin_form = QFormLayout()
        margin_form.setSpacing(4)
        self.margin_top = QSpinBox(self.floating); self.margin_top.setRange(0, 100); self.margin_top.setValue(0); self.margin_top.setSuffix(" pt")
        self.margin_bottom = QSpinBox(self.floating); self.margin_bottom.setRange(0, 100); self.margin_bottom.setValue(0); self.margin_bottom.setSuffix(" pt")
        self.margin_left = QSpinBox(self.floating); self.margin_left.setRange(0, 100); self.margin_left.setValue(20); self.margin_left.setSuffix(" pt")
        self.margin_right = QSpinBox(self.floating); self.margin_right.setRange(0, 100); self.margin_right.setValue(20); self.margin_right.setSuffix(" pt")
        margin_form.addRow("上边距:", self.margin_top)
        margin_form.addRow("下边距:", self.margin_bottom)
        margin_form.addRow("左边距:", self.margin_left)
        margin_form.addRow("右边距:", self.margin_right)
        flo_layout.addLayout(margin_form)

        btn_layout = QHBoxLayout()
        self.cancel_btn = QPushButton("取消", self.floating)
        self.ok_btn = QPushButton("确认", self.floating)
        self.ok_btn.setDefault(True)
        self.cancel_btn.clicked.connect(self.reject)
        self.ok_btn.clicked.connect(self._on_confirm)
        btn_layout.addWidget(self.cancel_btn)
        btn_layout.addWidget(self.ok_btn)
        flo_layout.addLayout(btn_layout)

        # 加载初始参数
        if initial_params:
            self.fontsize_spin.setValue(initial_params.get("fontsize", 25))
            self.lineheight_spin.setValue(initial_params.get("line_height", 1.3))
            self.paraspacing_spin.setValue(initial_params.get("para_spacing", 3))
            self.indent_spin.setValue(initial_params.get("indent_chars", 2))
            self.justify_check.setChecked(initial_params.get("justify", False))
            fw = initial_params.get("font_weight", "normal")
            weight_idx_map = {"normal": 0, "bold": 1, "lighter": 2, "bolder": 3, 400: 0, 700: 1, 300: 2, 600: 3}
            self.weight_combo.setCurrentIndex(weight_idx_map.get(fw, 0))
            self.margin_top.setValue(initial_params.get("margin_top", 0))
            self.margin_bottom.setValue(initial_params.get("margin_bottom", 0))
            self.margin_left.setValue(initial_params.get("margin_left", 20))
            self.margin_right.setValue(initial_params.get("margin_right", 20))
            self.page_width_spin.setValue(initial_params.get("page_width_pct", 45))

        self.floating.adjustSize()
        self.floating.move(60, 60)
        self.floating.setStyleSheet(self.floating.styleSheet() + input_style)
        self.floating.show()
        self.floating.raise_()

        for w in [
            self.fontsize_spin, self.lineheight_spin,
            self.paraspacing_spin, self.indent_spin, self.justify_check,
            self.weight_combo, self.page_width_spin,
            self.margin_top, self.margin_bottom,
            self.margin_left, self.margin_right
        ]:
            if hasattr(w, "valueChanged"):
                w.valueChanged.connect(self._schedule_relayout)
            elif hasattr(w, "currentIndexChanged"):
                w.currentIndexChanged.connect(self._schedule_relayout)
            elif hasattr(w, "stateChanged"):
                w.stateChanged.connect(self._schedule_relayout)

        QTimer.singleShot(100, self._do_relayout)

    def _add_row(self, layout, label_text, widget):
        row = QHBoxLayout()
        label = QLabel(label_text, self.floating)
        label.setFixedWidth(70)
        row.addWidget(label)
        row.addWidget(widget, 1)
        layout.addLayout(row)

    def _schedule_relayout(self):
        self._resize_timer.start(200)

    def _get_params(self):
        return {
            "fontsize": self.fontsize_spin.value(),
            "line_height": self.lineheight_spin.value(),
            "para_spacing": self.paraspacing_spin.value(),
            "indent_chars": self.indent_spin.value(),
            "justify": self.justify_check.isChecked(),
            "font_weight": ["normal", "bold", "lighter", "bolder"][self.weight_combo.currentIndex()],
            "margin_top": self.margin_top.value(),
            "margin_bottom": self.margin_bottom.value(),
            "margin_left": self.margin_left.value(),
            "margin_right": self.margin_right.value(),
            "page_width_pct": self.page_width_spin.value(),
        }

    def _do_relayout(self):
        if self._raw_epub_data is None:
            return
        self._resize_timer.stop()
        QApplication.setOverrideCursor(Qt.WaitCursor)
        new_doc = None
        try:
            params = self._get_params()
            fontsize = params["fontsize"]
            page_width_pct = params["page_width_pct"]

            screen_w = self.screen().geometry().width()
            page_w_px = int(screen_w * page_width_pct / 100)
            page_h_px = self.screen().geometry().height()
            pt_per_px = 72.0 / 96.0
            page_w_pt = page_w_px * pt_per_px
            page_h_pt = page_h_px * pt_per_px

            new_doc = fitz.open(stream=self._raw_epub_data, filetype="epub")
            css = _build_apply_css(params)
            # PyMuPDF的apply_css()对EPUB无效，直接修改EPUB内部CSS
            modified_bytes, _ = _modify_epub_css_in_memory(self._raw_epub_data, css)
            new_doc = fitz.open(stream=modified_bytes, filetype="epub")
            new_doc.layout(fontsize=fontsize, width=page_w_pt, height=page_h_pt)

            old_doc = self.doc
            self.doc = new_doc
            new_doc = None
            if old_doc:
                old_doc.close()

            total = len(self.doc)
            self.current_page = max(0, min(self.current_page, total - 1))
            mat = fitz.Matrix(2.0, 2.0)
            left_pm = QPixmap()
            right_pm = QPixmap()
            if self.current_page < total:
                p = self.doc[self.current_page]
                pix = p.get_pixmap(matrix=mat)
                stride = pix.stride if pix.stride is not None else pix.width * 3
                fmt = QImage.Format_RGBA8888 if pix.alpha else QImage.Format_RGB888
                img = QImage(pix.samples, pix.width, pix.height, stride, fmt)
                left_pm = QPixmap.fromImage(img.copy())
            if self.current_page + 1 < total:
                p = self.doc[self.current_page + 1]
                pix = p.get_pixmap(matrix=mat)
                stride = pix.stride if pix.stride is not None else pix.width * 3
                fmt = QImage.Format_RGBA8888 if pix.alpha else QImage.Format_RGB888
                img = QImage(pix.samples, pix.width, pix.height, stride, fmt)
                right_pm = QPixmap.fromImage(img.copy())
            self.left_pane.set_page(left_pm if not left_pm.isNull() else None)
            self.right_pane.set_page(right_pm if not right_pm.isNull() else None)
            lpn = self.current_page + 1 if self.current_page < total else 0
            rpn = self.current_page + 2 if self.current_page + 1 < total else 0
            self.status_label.setText(f"[{lpn if lpn else '-'}/{rpn if rpn else '-'}]  共 {total} 页")
            self.floating.raise_()
        except Exception as e:
            import traceback
            traceback.print_exc()
            self.status_label.setText(f"Relayout error: {e}")
            if new_doc:
                try: new_doc.close()
                except: pass
        finally:
            QApplication.restoreOverrideCursor()

    def keyPressEvent(self, event):
        if event.key() in (Qt.Key_Right, Qt.Key_Down, Qt.Key_PageDown):
            total = len(self.doc) if self.doc else 0
            if self.current_page + 2 < total:
                self.current_page += 2
                self._do_relayout()
            event.accept()
        elif event.key() in (Qt.Key_Left, Qt.Key_Up, Qt.Key_PageUp):
            if self.current_page - 2 >= 0:
                self.current_page -= 2
                self._do_relayout()
            event.accept()
        elif event.key() == Qt.Key_Escape:
            self.reject()
        else:
            super().keyPressEvent(event)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._schedule_relayout()

    def _on_confirm(self):
        self.result_params = self._get_params()
        if self.doc and len(self.doc) > 0:
            try:
                r = self.doc[0].rect
                self.result_params["page_width"] = r.width
                self.result_params["page_height"] = r.height
            except Exception:
                pass
        self.accept()

    def closeEvent(self, event):
        if self.doc:
            self.doc.close()
            self.doc = None
        super().closeEvent(event)


class TacticalPane(QLabel):
    focused = pyqtSignal(bool)

    def __init__(self, parent=None):

        super().__init__(parent)
        self.page_pixmap = None
        self.scaled_pixmap = None
        self.offset = QPointF(0, 0)
        self.scale_factor = 1.0
        self.drag_start = None
        self.page_num = -1
        self.is_left = False

        # 旋转相关
        self.rotation = 0
        self.original_pixmap = None

        # 批注相关
        self.annotations = []  # 当前页面的批注
        self.current_annotation = None
        self.annotation_mode = None  # None, "pen", "rect", "text"
        self.annotation_start = QPointF()
        self.temp_annotation = None
        self.pen_path = None
        self.pen_points = []
        self.text_input_widget = None
        self.drawing = False

        # 默认颜色 - 每个功能独立
        self.pen_color = QColor(255, 0, 0)  # 红色 - 画笔
        self.rect_color = QColor(255, 0, 0, 128)  # 半透明红色 - 矩形高亮
        self.text_color = QColor(255, 0, 0)  # 红色 - 文本
        self.pen_width = 3
        self.rect_border_width = 2
        # 文字批注字体大小（pt），优先从主窗口同步
        main_window = self.window()
        if main_window is not None and type(main_window).__name__ == 'TactiReader' and hasattr(main_window, 'text_annotation_font_size'):
            self.font_size = main_window.text_annotation_font_size
        else:
            self.font_size = 25
        
        # 文本编辑相关
        self.editing_text_annotation = None
        self.text_edit_start_pos = QPointF()

        # 搜索高亮
        self.search_highlights = []  # [{'rect': QRectF, 'color': QColor}, ...]
        self.search_text = ""  # 当前搜索词
        self.search_color = QColor(255, 255, 0, 100)  # 半透明黄色高亮

        self.setFrameShape(QFrame.Box)
        self.setFrameShadow(QFrame.Sunken)
        self.setAlignment(Qt.AlignCenter)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setMouseTracking(True)
        self.setCursor(Qt.ArrowCursor)
        # === 文字选取相关 ===
        self.text_selection_mode = False
        self.selection_start = None  # QPointF (widget coordinates)
        self.selection_end = None  # QPointF (widget coordinates)
        self.text_selection_highlights = []  # [{'rect': [x,y,w,h], 'color': QColor}, ...]
        self.page_text_dict = None  # 存储 fitz.get_text("dict") 结果
        self.doc_page = None  # PyMuPDF page object
        # ====================
        # 新增：用于控制拖动状态
        self.is_selecting_text = False

    def _transform_point_for_rotation(
        self, x, y, creation_rotation, current_rotation, pixmap_width, pixmap_height
    ):
        """将原始PDF坐标点根据旋转角度转换为当前屏幕坐标"""
        if creation_rotation == current_rotation:
            return x, y

        relative_rotation = (current_rotation - creation_rotation) % 360

        if relative_rotation == 90:
            return pixmap_height - y, x
        elif relative_rotation == 180:
            return pixmap_width - x, pixmap_height - y
        elif relative_rotation == 270:
            return y, pixmap_width - x
        else:
            return x, y

    def _pixmap_coord_to_pdf_0deg(self, px, py):
        """将当前旋转视图下的 pixmap 像素坐标，转换为 0° PDF 坐标"""
        if not self.original_pixmap:
            return px, py
        orig_w = self.original_pixmap.width()
        orig_h = self.original_pixmap.height()
        rot = self.rotation
        if rot == 0:
            return px, py
        elif rot == 90:
            return py, orig_h - px
        elif rot == 180:
            return orig_w - px, orig_h - py
        elif rot == 270:
            return orig_w - py, px
        else:
            return px, py

    def _pixmap_rect_to_pdf_0deg_rect(self, x, y, w, h):
        """将当前旋转视图下的 pixmap 矩形，转换为 0° PDF 坐标下的包围盒"""
        x1, y1 = self._pixmap_coord_to_pdf_0deg(x, y)
        x2, y2 = self._pixmap_coord_to_pdf_0deg(x + w, y + h)
        pdf_x = min(x1, x2)
        pdf_y = min(y1, y2)
        pdf_w = abs(x1 - x2)
        pdf_h = abs(y1 - y2)
        return pdf_x, pdf_y, pdf_w, pdf_h

    def focusInEvent(self, event):
        """当窗格获得键盘焦点时触发"""
        super().focusInEvent(event)
        # 发射信号，告诉主窗口：“我获得了焦点，我是左窗格吗？”
        self.focused.emit(self.is_left_pane)

    def set_page(
        self, pixmap, page_num, is_left=False, reset_view=False, annotations=None
    ):
        # 保存原始pixmap
        self.original_pixmap = pixmap
        self.page_pixmap = pixmap
        self.page_num = page_num
        self.is_left = is_left

        if reset_view:
            self.reset_view()
        # else: 保持现有的 self.rotation 值（由 render_facing 或用户操作设置）

        if annotations is not None:
            self.annotations = annotations
        elif hasattr(self.window(), "get_annotations_for_page"):
            self.annotations = self.window().get_annotations_for_page(page_num)
        else:
            self.annotations = []
        # 移除任何现有的文本编辑部件
        if self.text_input_widget:
            self.text_input_widget.deleteLater()
        self.text_input_widget = None
        self.editing_text_annotation = None
        # 应用旋转
        if self.rotation != 0:
            transform = QTransform().rotate(self.rotation)
            self.page_pixmap = self.original_pixmap.transformed(
                transform, Qt.SmoothTransformation
            )

        # 加载页面文本用于选取
        if (
            hasattr(self.window(), "doc") and self.window().doc and page_num > 0
        ):
            try:
                self.doc_page = self.window().doc[page_num - 1]
                self.page_text_dict = self.doc_page.get_text("dict")
            except Exception as e:
                print(f"[ERROR] Failed to load text for page {page_num}: {e}")
                self.doc_page = None
                self.page_text_dict = None
        else:
            self.doc_page = None
            self.page_text_dict = None
        self.update()

    def reset_view(self):
        self.rotation = 0
        self.offset = QPointF(0, 0)
        if self.original_pixmap:
            pane_width = self.width()
            pane_height = self.height()
            if pane_width > 0 and pane_height > 0:
                pw = self.original_pixmap.width()
                ph = self.original_pixmap.height()
                main_window = self.window()
                fit_mode = "fit_page"
                if (
                    main_window is not None
                    and type(main_window).__name__ == "TactiReader"
                    and hasattr(main_window, "default_fit_mode")
                ):
                    fit_mode = main_window.default_fit_mode
                if fit_mode == "actual_size":
                    self.scale_factor = 1.0
                elif fit_mode == "fit_width":
                    self.scale_factor = pane_width / pw
                elif fit_mode == "fit_height":
                    self.scale_factor = pane_height / ph
                elif fit_mode == "fit_page":
                    sw = pane_width / pw
                    sh = pane_height / ph
                    self.scale_factor = min(sw, sh)
                self.scale_factor = max(0.2, min(self.scale_factor, 10.0))
            else:
                self.scale_factor = 1.0
            transform = QTransform().rotate(self.rotation)
            self.page_pixmap = self.original_pixmap.transformed(
                transform, Qt.SmoothTransformation
            )
        else:
            self.scale_factor = 1.0
        self.update()

    def apply_fit_mode(self, mode):
        """应用缩放模式（不改变旋转/偏移，只改 scale_factor）"""
        if not self.original_pixmap:
            return
        pw = self.original_pixmap.width()
        ph = self.original_pixmap.height()
        pane_w = self.width()
        pane_h = self.height()
        if pane_w <= 0 or pane_h <= 0:
            return
        if mode == "actual_size":
            self.scale_factor = 1.0
        elif mode == "fit_width":
            self.scale_factor = max(0.2, min(pane_w / pw, 10.0))
        elif mode == "fit_height":
            self.scale_factor = max(0.2, min(pane_h / ph, 10.0))
        elif mode == "fit_page":
            sw = pane_w / pw
            sh = pane_h / ph
            self.scale_factor = max(0.2, min(sw, sh, 10.0))
        self.update()

    def rotate_clockwise(self):
        self.rotation = (self.rotation + 90) % 360
        if self.original_pixmap:
            transform = QTransform().rotate(self.rotation)
            self.page_pixmap = self.original_pixmap.transformed(
                transform, Qt.SmoothTransformation
            )
            # 旋转后自动缩放至适合页面（fit_page），左上角锚点
            pw = self.page_pixmap.width()
            ph = self.page_pixmap.height()
            pane_w = self.width()
            pane_h = self.height()
            if pane_w > 0 and pane_h > 0 and pw > 0 and ph > 0:
                sx = pane_w / pw
                sy = pane_h / ph
                self.scale_factor = max(0.2, min(sx, sy, 10.0))
            self.offset = QPointF(0, 0)
        self.update()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if (
            self.original_pixmap
            and not self.original_pixmap.isNull()
            and self.width() > 0
            and self.height() > 0
        ):
            main_window = self.window()
            if (
                main_window is not None
                and type(main_window).__name__ == "TactiReader"
                and hasattr(main_window, "default_fit_mode")
                and main_window.default_fit_mode == "fit_height"
            ):
                ph = self.original_pixmap.height()
                self.scale_factor = self.height() / ph
                self.scale_factor = max(0.2, min(self.scale_factor, 10.0))
                scaled_w = self.original_pixmap.width() * self.scale_factor
                self.offset = QPointF((self.width() - scaled_w) / 2, 0)
                self.update()

    def paintEvent(self, event):
        if not self.page_pixmap or self.page_pixmap.isNull():
            super().paintEvent(event)
            return

        painter = QPainter(self)
        painter.setRenderHint(QPainter.SmoothPixmapTransform)

        scaled_size = self.page_pixmap.size() * self.scale_factor
        self.scaled_pixmap = self.page_pixmap.scaled(
            scaled_size, Qt.IgnoreAspectRatio, Qt.SmoothTransformation
        )

        draw_x = self.offset.x()
        draw_y = self.offset.y()
        painter.drawPixmap(int(draw_x), int(draw_y), self.scaled_pixmap)

        # 绘制搜索高亮（支持页面旋转）
        for highlight in self.search_highlights:
            x0, y0, w, h = highlight["rect"]
            color = highlight["color"]

            # 获取原始 PDF 坐标下的四个角（0°）
            corners_0deg = [(x0, y0), (x0 + w, y0), (x0 + w, y0 + h), (x0, y0 + h)]

            # 转换到当前旋转下的 PDF 坐标
            corners_current = []
            for px, py in corners_0deg:
                xc, yc = self._transform_point_for_rotation(
                    px,
                    py,
                    0,
                    self.rotation,
                    self.original_pixmap.width(),
                    self.original_pixmap.height(),
                )
                corners_current.append((xc, yc))

            # 转换到屏幕坐标并创建包围盒
            screen_points = [
                QPointF(
                    cx * self.scale_factor + draw_x, cy * self.scale_factor + draw_y
                )
                for (cx, cy) in corners_current
            ]
            xs = [p.x() for p in screen_points]
            ys = [p.y() for p in screen_points]
            screen_rect = QRectF(min(xs), min(ys), max(xs) - min(xs), max(ys) - min(ys))

            painter.fillRect(screen_rect, color)
            # =======================================

        # 绘制批注
        for annotation in self.annotations:
            self.draw_annotation(painter, annotation, draw_x, draw_y)
        # === 新增：绘制文字选取高亮 ===
        for highlight in self.text_selection_highlights:
            x0, y0, w, h = highlight["rect"]
            color = highlight["color"]
            # 复用搜索高亮的坐标变换逻辑
            corners_0deg = [(x0, y0), (x0 + w, y0), (x0 + w, y0 + h), (x0, y0 + h)]
            corners_current = []
            for px, py in corners_0deg:
                xc, yc = self._transform_point_for_rotation(
                    px,
                    py,
                    0,
                    self.rotation,
                    self.original_pixmap.width(),
                    self.original_pixmap.height(),
                )
                corners_current.append((xc, yc))
            screen_points = [
                QPointF(
                    cx * self.scale_factor + draw_x, cy * self.scale_factor + draw_y
                )
                for (cx, cy) in corners_current
            ]
            xs = [p.x() for p in screen_points]
            ys = [p.y() for p in screen_points]
            screen_rect = QRectF(min(xs), min(ys), max(xs) - min(xs), max(ys) - min(ys))
            painter.fillRect(screen_rect, color)
        # === 文字选取高亮绘制结束 ===
        # 绘制临时批注（正在绘制中的）
        # === 修复：所见即所得的临时批注预览 (矩形、画笔、文本) ===
        # 1. 预览临时矩形/高亮
        if self.temp_annotation and self.temp_annotation["type"] == "rect":
            x, y, w, h = self.temp_annotation["rect"]
            screen_x = x * self.scale_factor + draw_x
            screen_y = y * self.scale_factor + draw_y
            screen_w = w * self.scale_factor
            screen_h = h * self.scale_factor
            painter.save()
            color = QColor(self.temp_annotation["color"])
            color.setAlpha(128)
            painter.setBrush(QBrush(color))
            painter.setPen(QPen(color, self.rect_border_width))
            painter.drawRect(int(screen_x), int(screen_y), int(screen_w), int(screen_h))
            painter.restore()

        # 2. 预览临时画笔路径
        if self.pen_path and len(self.pen_points) > 0:
            painter.save()
            pen = QPen(self.pen_color, self.pen_width)
            pen.setCapStyle(Qt.RoundCap)
            pen.setJoinStyle(Qt.RoundJoin)
            painter.setPen(pen)
            # 关键：直接使用当前视图的 scale+offset 转换点
            scaled_path = QPainterPath()
            for i, point in enumerate(self.pen_points):
                if isinstance(point, (list, tuple)) and len(point) >= 2:
                    px, py = point[0], point[1]
                else:  # 如果是 QPointF
                    px, py = point.x(), point.y()
                screen_px = px * self.scale_factor + draw_x
                screen_py = py * self.scale_factor + draw_y
                if i == 0:
                    scaled_path.moveTo(screen_px, screen_py)
                else:
                    scaled_path.lineTo(screen_px, screen_py)
            painter.drawPath(scaled_path)
            painter.restore()

        # 3. 文本批注的预览由内联编辑器自身处理，无需在此绘制
        # === 修复结束 ===
        # === 极简方案：直接问主窗口我是不是当前阅读区域 ===
        main_window = self.window()
        if hasattr(main_window, "last_focused_pane_is_left") and hasattr(
            main_window, "single_page_mode"
        ):
            # 判断自己是不是左窗格（通过对象身份）
            is_left_pane = self is main_window.left_pane
            is_right_pane = self is main_window.right_pane

            # 当前阅读区域逻辑：
            # - 单页模式：只有右窗格是活跃的
            # - 双页模式：左窗格活跃当且仅当 last_focused_pane_is_left 为 True
            is_active = False
            if main_window.single_page_mode:
                if is_right_pane:
                    is_active = True
            else:
                if is_left_pane and main_window.last_focused_pane_is_left:
                    is_active = True
                elif is_right_pane and not main_window.last_focused_pane_is_left:
                    is_active = True

            if is_active:
                border_pen = QPen(QColor(80, 110, 130), 2)
                border_pen.setJoinStyle(Qt.MiterJoin)
                painter.setPen(border_pen)
                painter.setBrush(Qt.NoBrush)
                painter.drawRect(1, 1, self.width() - 2, self.height() - 2)

    def draw_annotation(self, painter, annotation, offset_x, offset_y):
        if not self.original_pixmap:
            return

        anno_type = annotation.get("type", "")
        color = QColor(annotation.get("color", "#FF0000"))
        orig_w = self.original_pixmap.width()
        orig_h = self.original_pixmap.height()
        creation_rot = annotation.get("creation_rotation", 0)  # 批注创建时的页面旋转
        current_rot = self.rotation  # 当前页面旋转

        # === 核心：将批注从 creation_rot 坐标系 转换到 current_rot 坐标系 ===
        def transform_coords_from_creation_to_current(points_0deg):
            """将一组在 creation_rot 下定义的点，转换到 current_rot 下的坐标"""
            points_current = []
            for px, py in points_0deg:
                # Step 1: 从 creation_rot 逆变换回 0°
                x0, y0 = self._transform_point_for_rotation(
                    px, py, creation_rot, 0, orig_w, orig_h
                )
                # Step 2: 从 0° 正变换到 current_rot
                xc, yc = self._transform_point_for_rotation(
                    x0, y0, 0, current_rot, orig_w, orig_h
                )
                points_current.append((xc, yc))
            return points_current

        # ===================================================================

        if anno_type == "rect":
            x, y, w, h = annotation["rect"]
            corners_0deg = [(x, y), (x + w, y), (x + w, y + h), (x, y + h)]
            corners_current = transform_coords_from_creation_to_current(corners_0deg)

            # 计算包围盒（用于绘制）
            xs = [p[0] for p in corners_current]
            ys = [p[1] for p in corners_current]
            final_x, final_y = min(xs), min(ys)
            final_w, final_h = max(xs) - final_x, max(ys) - final_y

            screen_x = final_x * self.scale_factor + offset_x
            screen_y = final_y * self.scale_factor + offset_y
            screen_w = final_w * self.scale_factor
            screen_h = final_h * self.scale_factor

            painter.save()
            highlight_color = QColor(color)
            highlight_color.setAlpha(96)
            painter.setBrush(QBrush(highlight_color))
            painter.setPen(QPen(color, self.rect_border_width))
            painter.drawRect(int(screen_x), int(screen_y), int(screen_w), int(screen_h))
            painter.restore()

        elif anno_type == "pen":
            points = annotation.get("points", [])
            if len(points) < 2:
                return
            # 将所有笔迹点从 creation_rot 转换到 current_rot
            transformed_points = transform_coords_from_creation_to_current(points)
            # 转换到屏幕坐标
            screen_points = [
                QPointF(
                    px * self.scale_factor + offset_x, py * self.scale_factor + offset_y
                )
                for (px, py) in transformed_points
            ]
            painter.save()
            pen = QPen(color, self.pen_width * self.scale_factor)
            pen.setCapStyle(Qt.RoundCap)
            pen.setJoinStyle(Qt.RoundJoin)
            painter.setPen(pen)
            path = QPainterPath()
            for i, pt in enumerate(screen_points):
                if i == 0:
                    path.moveTo(pt)
                else:
                    path.lineTo(pt)
            painter.drawPath(path)
            painter.restore()

        elif anno_type == "text":
            x, y, w, h = annotation[
                "rect"
            ]  # 这已经是精准的 0° PDF 坐标下的文字包围盒！
            text = annotation.get("text", "")
            font_size = annotation.get("font_size", 12)

            if not text.strip():
                return

            # === 直接使用保存的矩形（四个角）===
            corners_0deg = [(x, y), (x + w, y), (x + w, y + h), (x, y + h)]

            # === 将四个角从 0° 转换到 current_rot ===
            corners_current = []
            for px, py in corners_0deg:
                xc, yc = self._transform_point_for_rotation(
                    px, py, 0, current_rot, orig_w, orig_h
                )
                corners_current.append((xc, yc))

            # === 转换到屏幕坐标并绘制 ===
            screen_path = QPainterPath()
            for i, (cx, cy) in enumerate(corners_current):
                sx = cx * self.scale_factor + offset_x
                sy = cy * self.scale_factor + offset_y
                if i == 0:
                    screen_path.moveTo(sx, sy)
                else:
                    screen_path.lineTo(sx, sy)
            screen_path.closeSubpath()

            # 绘制背景（透明）
            painter.save()
            highlight_color = QColor(color)
            highlight_color.setAlpha(0)  # 完全透明
            painter.setBrush(QBrush(highlight_color))
            painter.setPen(Qt.NoPen)  # ← 完全移除边框
            painter.drawPath(screen_path)
            painter.restore()

            # === 绘制文字（在旋转后的包围盒内）===
            # 计算四边形的屏幕包围盒（用于文字定位）
            xs = [p[0] for p in corners_current]
            ys = [p[1] for p in corners_current]
            min_x, max_x = min(xs), max(xs)
            min_y, max_y = min(ys), max(ys)
            text_rect_screen = QRectF(
                min_x * self.scale_factor + offset_x,
                min_y * self.scale_factor + offset_y,
                (max_x - min_x) * self.scale_factor,
                (max_y - min_y) * self.scale_factor,
            )

            painter.save()
            font = QFont("Arial")
            font.setPixelSize(int(font_size * self.scale_factor))
            painter.setFont(font)
            painter.setPen(QPen(color))
            painter.drawText(text_rect_screen, Qt.TextWordWrap, text)
            painter.restore()

    def set_search_highlights(self, highlights, search_text=""):
        """设置搜索高亮"""
        self.search_highlights = highlights
        self.search_text = search_text
        self.update()

    def wheelEvent(self, event):
        if event.modifiers() == Qt.ControlModifier:
            delta = event.angleDelta().y()
            zoom_factor = 1.1 if delta > 0 else 1 / 1.1
            old_scale = self.scale_factor
            new_scale = old_scale * zoom_factor
            new_scale = max(0.2, min(new_scale, 10.0))

            mouse_pos = event.pos()
            mx = mouse_pos.x()
            my = mouse_pos.y()

            img_x = (mx - self.offset.x()) / old_scale
            img_y = (my - self.offset.y()) / old_scale

            self.scale_factor = new_scale
            self.offset.setX(mx - img_x * new_scale)
            self.offset.setY(my - img_y * new_scale)
            self.update()
        else:
            scroll_amount = event.angleDelta().y() // 3
            self.offset.setY(self.offset.y() + scroll_amount)
            self.update()
        event.accept()

    def mousePressEvent(self, event):
        if self.text_selection_mode and event.button() == Qt.LeftButton:
            # J模式下，左键按下开始选取（但不立即绘制，等待拖动）
            self.is_selecting_text = True
            self.selection_start = event.pos()
            self.selection_end = event.pos()
            event.accept()
            return
            # 不立即调用 update_selected_text，避免单击产生空选区
        elif self.annotation_mode and event.button() == Qt.LeftButton:
            # 开始绘制批注
            self.drawing = True
            # 计算在PDF图片上的坐标（考虑缩放和偏移）
            img_x = (event.pos().x() - self.offset.x()) / self.scale_factor
            img_y = (event.pos().y() - self.offset.y()) / self.scale_factor
            self.annotation_start = QPointF(event.pos())
            if self.annotation_mode == "rect":
                self.temp_annotation = {
                    "type": "rect",
                    "rect": [img_x, img_y, 0, 0],
                    "color": self.rect_color.name(),
                }
            elif self.annotation_mode == "pen":
                self.pen_path = QPainterPath()
                self.pen_points = [(img_x, img_y)]  # 修复：初始化路径起点
                self.pen_path.moveTo(event.pos())
            elif self.annotation_mode == "text":
                # 如果已有输入框，先完成它
                if self.text_input_widget:
                    self.finish_text_annotation(self.text_input_widget.toPlainText())
                # 对于文本，创建覆盖页面剩余宽度的内联编辑器
                screen_x = event.pos().x()
                screen_y = event.pos().y()
                # 计算页面右边界（屏幕坐标）
                page_right = self.offset.x() + self.original_pixmap.width() * self.scale_factor
                edit_width = max(50, int(page_right - screen_x))
                edit_height = int(self.font_size * self.scale_factor * 2) + 10
                # 创建文本编辑部件
                self.text_input_widget = InlineTextEdit(self)
                self.text_input_widget.setGeometry(
                    int(screen_x), int(screen_y), edit_width, edit_height
                )
                self.text_input_widget.setStyleSheet(f"""
                QTextEdit {{
                    background-color: rgba(255, 255, 255, 200);
                    border: 1px solid {self.text_color.name()};
                    font-size: {int(self.font_size * self.scale_factor)}px;
                    color: {self.text_color.name()};
                }}
                """)
                self.text_input_widget.show()
                self.text_input_widget.setFocus()
                # 保存起始位置
                self.text_edit_start_pos = QPointF(screen_x, screen_y)
                # 连接信号
                self.text_input_widget.textConfirmed.connect(
                    self.finish_text_annotation
                )
                self.text_input_widget.editingCancelled.connect(
                    self.cancel_text_annotation
                )
                self.text_input_widget.textChanged.connect(
                    self._on_text_input_changed
                )
                # 创建临时批注
                self.temp_annotation = {
                    "type": "text",
                    "rect": [img_x, img_y, edit_width / self.scale_factor, edit_height / self.scale_factor],
                    "color": self.text_color.name(),
                    "text": "",
                    "font_size": self.font_size,
                }
                # 设置正在编辑的批注
                self.editing_text_annotation = self.temp_annotation
                self.update()
        elif event.button() == Qt.LeftButton and not self.annotation_mode:
            # 正常的拖拽
            self.drag_start = event.pos()
            self.setCursor(Qt.ClosedHandCursor)
        else:
            super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if (
            self.text_selection_mode
            and self.is_selecting_text
            and self.selection_start is not None
        ):
            # J模式下，拖动时更新选区
            self.selection_end = event.pos()
            self.update_selected_text()
            self.setCursor(Qt.IBeamCursor)
            event.accept()
            return
        elif self.annotation_mode and self.drawing:
            if self.annotation_mode == "rect" and self.temp_annotation:
                # 更新矩形大小
                current_pos = event.pos()
                start_x = self.annotation_start.x()
                start_y = self.annotation_start.y()
                rect_width = current_pos.x() - start_x
                rect_height = current_pos.y() - start_y
                img_x = (start_x - self.offset.x()) / self.scale_factor
                img_y = (start_y - self.offset.y()) / self.scale_factor
                img_width = rect_width / self.scale_factor
                img_height = rect_height / self.scale_factor
                # 确保宽度和高度为正
                if rect_width < 0:
                    img_x = img_x + img_width
                    img_width = -img_width
                if rect_height < 0:
                    img_y = img_y + img_height
                    img_height = -img_height
                self.temp_annotation["rect"] = [img_x, img_y, img_width, img_height]
                self.update()
            elif self.annotation_mode == "pen":
                # 添加画笔点
                img_x = (event.pos().x() - self.offset.x()) / self.scale_factor
                img_y = (event.pos().y() - self.offset.y()) / self.scale_factor
                self.pen_points.append((img_x, img_y))  # 修复：更新路径
                self.pen_path.lineTo(event.pos())
                self.update()
        elif self.drag_start:
            delta = event.pos() - self.drag_start
            self.offset += delta
            self.drag_start = event.pos()
            self.update()
        else:
            super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if (
            self.text_selection_mode
            and self.is_selecting_text
            and event.button() == Qt.LeftButton
        ):
            # J模式下，松开左键结束选取，保留高亮
            self.is_selecting_text = False
            self.update_selected_text()
            event.accept()
            return
            # 可在此处复制到剪贴板或弹出菜单
        elif self.annotation_mode and self.drawing and event.button() == Qt.LeftButton:
            self.drawing = False
            if self.annotation_mode == "rect" and self.temp_annotation:
                # 保存矩形批注
                final_rect = self.temp_annotation["rect"]
                if abs(final_rect[2]) > 5 and abs(final_rect[3]) > 5:  # 最小尺寸检查
                    x, y, w, h = final_rect
                    # === 关键修复：转换为 0° PDF 坐标 ===
                    pdf_x, pdf_y, pdf_w, pdf_h = self._pixmap_rect_to_pdf_0deg_rect(
                        x, y, w, h
                    )
                    saved_annotation = {
                        "type": "rect",
                        "rect": [pdf_x, pdf_y, pdf_w, pdf_h],
                        "color": self.temp_annotation["color"],
                        "creation_rotation": 0,  # 统一设为 0
                    }
                    self.annotations.append(saved_annotation)
                    if hasattr(self.window(), "save_annotation"):
                        self.window().save_annotation(self.page_num, saved_annotation)
                self.temp_annotation = None
            elif self.annotation_mode == "pen" and len(self.pen_points) > 1:
                # 保存画笔批注
                # === 关键修复：将每个点转换为 0° PDF 坐标 ===
                converted_points = []
                for pt in self.pen_points:
                    if isinstance(pt, (list, tuple)) and len(pt) >= 2:
                        px, py = pt[0], pt[1]
                    else:  # QPointF
                        px, py = pt.x(), pt.y()
                    pdf_x, pdf_y = self._pixmap_coord_to_pdf_0deg(px, py)
                    converted_points.append([pdf_x, pdf_y])  # 存为 list，兼容 JSON
                pen_annotation = {
                    "type": "pen",
                    "points": converted_points,
                    "color": self.pen_color.name(),
                    "width": self.pen_width,
                    "creation_rotation": 0,  # 统一设为 0
                }
                self.annotations.append(pen_annotation)
                if hasattr(self.window(), "save_annotation"):
                    self.window().save_annotation(self.page_num, pen_annotation)
                self.pen_points = []
                self.pen_path = None
            # 文本批注在文本编辑部件中处理
            self.update()
        elif event.button() == Qt.LeftButton and self.drag_start:
            self.drag_start = None
            self.setCursor(Qt.ArrowCursor)
        # === 新增：处理右键点击 ===
        elif event.button() == Qt.RightButton:
            self._handle_right_click(event)
        # =========================
        else:
            super().mouseReleaseEvent(event)

    def _handle_right_click(self, event):
        """
        处理右键点击事件。如果有选中文本则显示复制菜单；否则显示功能菜单。
        """
        # 检查是否有选中文本
        has_selection = hasattr(self, "selected_text") and bool(
            self.selected_text.strip()
        )

        if has_selection:
            # 有选中文本 → 复制菜单
            menu = QMenu(self)
            main_window = self.window()
            copy_action = QAction(main_window.tr("Copy"), self)

            def do_copy():
                clipboard = QApplication.clipboard()
                clipboard.setText(self.selected_text.strip())

            copy_action.triggered.connect(do_copy)
            menu.addAction(copy_action)
            menu.exec_(event.globalPos())
            return

        # 无选中文本 → 功能菜单
        main_window = self.window()
        if main_window is None or type(main_window).__name__ != "TactiReader":
            return

        menu = QMenu(self)

        # 0. 目录导航（放在第一个位置）
        toc_action = QAction(main_window.tr("目录导航"), self)
        toc_action.triggered.connect(main_window.open_toc_dialog)
        menu.addAction(toc_action)

        menu.addSeparator()

        # 1. 打开电子书
        open_action = QAction(main_window.tr("打开电子书..."), self)
        open_action.triggered.connect(main_window.open_pdf_dialog)
        menu.addAction(open_action)

        menu.addSeparator()

        # 3. 颜色模式子菜单
        theme_menu = menu.addMenu(main_window.tr("颜色模式"))
        current_theme = getattr(main_window, 'current_theme', 'light')
        for name in THEMES:
            display_name = THEME_NAMES.get(name, name)
            act = QAction(display_name, self)
            act.setCheckable(True)
            act.setChecked(name == current_theme)
            act.triggered.connect(lambda checked, n=name: main_window.apply_theme(n))
            theme_menu.addAction(act)

        # 4. 设置文字大小（批注文字）
        font_size_action = QAction(main_window.tr("设置文字大小"), self)
        font_size_action.triggered.connect(main_window.set_text_annotation_font_size)
        menu.addAction(font_size_action)

        menu.addSeparator()

        # 5. 换书子菜单
        if main_window.open_documents:
            switch_menu = menu.addMenu(main_window.tr("换书"))
            current_path = os.path.abspath(main_window.pdf_path) if main_window.pdf_path else ""
            for idx, path in enumerate(main_window.open_documents):
                fname = os.path.basename(path)
                act = QAction(fname, self)
                act.setCheckable(True)
                act.setChecked(os.path.abspath(path) == current_path)
                act.triggered.connect(lambda checked, i=idx: main_window._switch_to_document(i))
                switch_menu.addAction(act)

        # 6. 删书子菜单
        if main_window.open_documents:
            del_menu = menu.addMenu(main_window.tr("删书"))
            for idx, path in enumerate(main_window.open_documents):
                fname = os.path.basename(path)
                act = QAction(fname, self)

                def make_del_confirm(p, f):
                    def do_del():
                        reply = QMessageBox.warning(
                            main_window,
                            main_window.tr("确认删书"),
                            main_window.tr("确定要关闭「{}」吗？").format(f),
                            QMessageBox.Yes | QMessageBox.No,
                            QMessageBox.No,
                        )
                        if reply == QMessageBox.Yes:
                            main_window._close_document(main_window.open_documents.index(p) if p in main_window.open_documents else -1)
                    return do_del

                act.triggered.connect(make_del_confirm(path, fname))
                del_menu.addAction(act)

        menu.addSeparator()

        # 7. 默认大小子菜单（与菜单栏一致）
        fit_menu = menu.addMenu(main_window.tr("默认大小"))
        labels = {
            "actual_size": "实际大小",
            "fit_width": "适合宽度",
            "fit_page": "适合页面",
        }
        current_fit = getattr(main_window, 'default_fit_mode', 'fit_page')
        for mode, label in labels.items():
            act = QAction(label, self)
            act.setCheckable(True)
            act.setChecked(mode == current_fit)
            act.triggered.connect(lambda _, m=mode: main_window._set_fit_mode(m))
            fit_menu.addAction(act)

        menu.addSeparator()

        # 8. 清除此页所有笔记（二次确认）
        clear_annot_action = QAction(main_window.tr("清除此页所有笔记"), self)
        page_num_for_clear = self.page_num

        def _confirm_clear_annotations():
            reply = QMessageBox.warning(
                main_window,
                main_window.tr("确认清除"),
                main_window.tr("确定要清除第 {page} 页的所有笔记吗？此操作不可撤销。").format(page=page_num_for_clear),
                QMessageBox.Yes | QMessageBox.No,
                QMessageBox.No,
            )
            if reply == QMessageBox.Yes:
                if str(page_num_for_clear) in main_window.annotations:
                    del main_window.annotations[str(page_num_for_clear)]
                    self.annotations = []
                    self.update()
                    main_window.save_config()
                    main_window.statusBar().showMessage(
                        main_window.tr("🗑️ 已清除第 {page} 页的所有笔记").format(page=page_num_for_clear),
                        2000,
                    )
                else:
                    main_window.statusBar().showMessage(
                        main_window.tr("第 {page} 页没有笔记").format(page=page_num_for_clear),
                        1500,
                    )

        clear_annot_action.triggered.connect(_confirm_clear_annotations)
        menu.addAction(clear_annot_action)

        # === EPUB 专用：图片列表 & 脚注列表 ===
        if getattr(main_window, 'is_epub', False) and main_window.pdf_path:
            menu.addSeparator()

            img_list_action = QAction(main_window.tr("图片列表"), self)
            fn_list_action = QAction(main_window.tr("脚注列表"), self)

            def _show_image_list():
                try:
                    focused_pn = self.page_num
                    images, _ = _get_page_items(
                        main_window.pdf_path, main_window.doc, focused_pn,
                        chapter_map=main_window._epub_chapter_map,
                        images_src=main_window._epub_images_src,
                        footnotes_src=main_window._epub_footnotes_src,
                    )
                    if images:
                        dlg = ImageListDialog(images, main_window)
                        dlg.exec_()
                    else:
                        QMessageBox.information(main_window, '图片列表', '当前页面未找到图片。')
                except Exception as e:
                    QMessageBox.warning(main_window, '错误', f'解析图片失败: {e}')

            def _show_footnote_list():
                try:
                    focused_pn = self.page_num
                    _, footnotes = _get_page_items(
                        main_window.pdf_path, main_window.doc, focused_pn,
                        chapter_map=main_window._epub_chapter_map,
                        images_src=main_window._epub_images_src,
                        footnotes_src=main_window._epub_footnotes_src,
                    )
                    if footnotes:
                        dlg = FootnoteListDialog(footnotes, main_window)
                        dlg.exec_()
                    else:
                        QMessageBox.information(main_window, '脚注列表', '当前页面未找到脚注。')
                except Exception as e:
                    QMessageBox.warning(main_window, '错误', f'解析脚注失败: {e}')

            img_list_action.triggered.connect(_show_image_list)
            fn_list_action.triggered.connect(_show_footnote_list)
            menu.addAction(img_list_action)
            menu.addAction(fn_list_action)

        menu.exec_(event.globalPos())

    def _on_text_input_changed(self):
        """根据内容动态调整文本输入框高度。"""
        if not self.text_input_widget:
            return
        doc = self.text_input_widget.document()
        doc.setTextWidth(self.text_input_widget.viewport().width())
        new_height = int(doc.size().height()) + 10
        self.text_input_widget.setFixedHeight(max(new_height, int(self.font_size * self.scale_factor) + 10))

    def finish_text_annotation(self, text):
        if self.text_input_widget and self.temp_annotation:
            if text.strip():
                self.temp_annotation["text"] = text

                # === 关键修复：在 PDF 坐标系下计算文本尺寸 ===
                pdf_font_size = int(self.font_size)  # 字体大小（pt），直接用于 PDF 坐标
                font = QFont("Arial", pdf_font_size)
                font_metrics = QFontMetrics(font)

                # 在 PDF 坐标系中，1pt = 1 单位，所以直接计算
                # 注意：这里不需要考虑 scale_factor！
                text_rect = font_metrics.boundingRect(
                    QRect(0, 0, 1000, 10000),  # 虚拟大矩形（PDF 坐标）
                    Qt.TextWordWrap,
                    text,
                )
                pdf_text_width = text_rect.width() * 1.1  # 计算宽度并留下余量
                pdf_text_height = text_rect.height()

                # 更新矩形尺寸（直接使用 PDF 坐标尺寸！）
                self.temp_annotation["rect"][2] = pdf_text_width
                self.temp_annotation["rect"][3] = pdf_text_height
                # ===========================================

                # 转换为 0° PDF 坐标（位置）
                x, y, w, h = self.temp_annotation["rect"]
                pdf_x, pdf_y, pdf_w, pdf_h = self._pixmap_rect_to_pdf_0deg_rect(
                    x, y, w, h
                )
                saved_annotation = {
                    "type": "text",
                    "rect": [pdf_x, pdf_y, pdf_w, pdf_h],
                    "color": self.temp_annotation["color"],
                    "text": text,
                    "font_size": self.font_size,
                    "creation_rotation": 0,
                }
                self.annotations.append(saved_annotation)
                if hasattr(self.window(), "save_annotation"):
                    self.window().save_annotation(self.page_num, saved_annotation)
            self.text_input_widget.deleteLater()
            self.text_input_widget = None
            self.temp_annotation = None
            self.editing_text_annotation = None
            self.update()

    def cancel_text_annotation(self):
        """取消文本批注"""
        if self.text_input_widget:
            self.text_input_widget.deleteLater()
            self.text_input_widget = None
            self.temp_annotation = None
            self.editing_text_annotation = None
            self.update()

    def keyPressEvent(self, event):
        # === 新增：打印所有按键事件 ===
        print(
            f"[KEY DEBUG] Key: {event.key()}, Text: '{event.text()}', Modifiers: {event.modifiers()}, isAutoRepeat: {event.isAutoRepeat()}"
        )
        # =============================

        if (
            self.text_selection_mode
            and event.key() == Qt.Key_C
            and event.modifiers() == Qt.ControlModifier
        ):
            # Ctrl+C: 复制选中文本
            if hasattr(self, "selected_text") and self.selected_text.strip():
                clipboard = QApplication.clipboard()
                clipboard.setText(self.selected_text.strip())
                print(f"[INFO] Copied to clipboard: {self.selected_text.strip()}")

                # ===========================

        else:
            super().keyPressEvent(event)

    def cancel_annotation(self):
        """取消当前的批注绘制"""
        # 取消文本编辑
        if self.text_input_widget:
            self.cancel_text_annotation()

        self.annotation_mode = None
        self.drawing = False
        self.temp_annotation = None
        self.pen_points = []
        self.pen_path = None
        self.setCursor(Qt.ArrowCursor)
        self.update()

        if hasattr(self.window(), "update_status"):
            self.window().update_status()

    def set_text_selection_mode(self, enabled: bool):
        """启用/禁用文字选取模式"""
        print(f"[DEBUG] Pane {self.page_num} set_text_selection_mode: {enabled}")
        self.text_selection_mode = enabled
        self.setCursor(Qt.IBeamCursor if enabled else Qt.ArrowCursor)
        # 清除旧选区
        self.selection_start = None
        self.selection_end = None
        self.text_selection_highlights = []
        self.update()

    def update_selected_text(self):
        if not self.doc_page or not self.page_text_dict:
            self.text_selection_highlights = []
            return
        if self.selection_start is None or self.selection_end is None:
            self.text_selection_highlights = []
            return

        # 根据文档类型动态决定渲染倍率（PDF: 2.0, EPUB: 1.5）
        is_epub = getattr(self.window(), 'is_epub', False)
        render_scale = 1.5 if is_epub else 2.0

        # === 步骤1: 获取鼠标在当前 Widget 中的选区 (屏幕像素) ===
        sel_widget_x0 = min(self.selection_start.x(), self.selection_end.x())
        sel_widget_y0 = min(self.selection_start.y(), self.selection_end.y())
        sel_widget_x1 = max(self.selection_start.x(), self.selection_end.x())
        sel_widget_y1 = max(self.selection_start.y(), self.selection_end.y())

        selected_spans = []  # 存储 (y, x, text) 用于排序
        highlight_rects = []  # 存储 Pixmap 像素坐标，用于绘制

        # === 步骤2: 遍历所有文字块，将其 bbox 转换到当前屏幕坐标系 ===
        # 同时收集所有 span 的中心 Y 坐标，用于确定首尾行
        all_spans = []
        for block in self.page_text_dict.get("blocks", []):
            for line in block.get("lines", []):
                for span in line.get("spans", []):
                    text = span["text"]
                    if not text.strip():
                        continue

                    # span["bbox"] 是 0° PDF 坐标
                    pdf_x0, pdf_y0, pdf_x1, pdf_y1 = span["bbox"]

                    # 1. 转为 Pixmap 像素坐标 (0°)
                    px0, py0 = pdf_x0 * render_scale, pdf_y0 * render_scale
                    px1, py1 = pdf_x1 * render_scale, pdf_y1 * render_scale

                    # 2. 应用旋转，得到当前 Pixmap 坐标
                    corners_0deg_pixmap = [
                        (px0, py0),
                        (px1, py0),
                        (px1, py1),
                        (px0, py1),
                    ]
                    corners_current_pixmap = []
                    for cx, cy in corners_0deg_pixmap:
                        rot_x, rot_y = self._transform_point_for_rotation(
                            cx,
                            cy,
                            0,
                            self.rotation,
                            self.original_pixmap.width(),
                            self.original_pixmap.height(),
                        )
                        corners_current_pixmap.append((rot_x, rot_y))

                    # 3. 将当前 Pixmap 坐标转为 Widget (屏幕) 坐标
                    screen_points = [
                        QPointF(
                            cx * self.scale_factor + self.offset.x(),
                            cy * self.scale_factor + self.offset.y(),
                        )
                        for (cx, cy) in corners_current_pixmap
                    ]
                    span_screen_x0 = min(p.x() for p in screen_points)
                    span_screen_y0 = min(p.y() for p in screen_points)
                    span_screen_x1 = max(p.x() for p in screen_points)
                    span_screen_y1 = max(p.y() for p in screen_points)

                    center_x = (span_screen_x0 + span_screen_x1) / 2
                    center_y = (span_screen_y0 + span_screen_y1) / 2

                    all_spans.append(
                        {
                            "span": span,
                            "text": text,
                            "screen_bbox": (
                                span_screen_x0,
                                span_screen_y0,
                                span_screen_x1,
                                span_screen_y1,
                            ),
                            "center": (center_x, center_y),
                            "pdf_bbox": (pdf_x0, pdf_y0, pdf_x1, pdf_y1),
                        }
                    )

        if not all_spans:
            self.selected_text = ""
            self.text_selection_highlights = []
            self.update()
            return

        # === 步骤3: 找出被选中的 span 范围（按Y坐标）===
        # 找到Y坐标在选区内的所有span
        vertically_selected_spans = [
            s for s in all_spans if sel_widget_y0 <= s["center"][1] <= sel_widget_y1
        ]

        if not vertically_selected_spans:
            self.selected_text = ""
            self.text_selection_highlights = []
            self.update()
            return

        # 按Y坐标排序，确定第一行和最后一行的Y范围
        vertically_selected_spans.sort(key=lambda s: s["center"][1])
        first_span_center_y = vertically_selected_spans[0]["center"][1]
        last_span_center_y = vertically_selected_spans[-1]["center"][1]

        # === 步骤4: 按阅读习惯处理每个 span ===
        for s in all_spans:
            span = s["span"]
            text = s["text"]
            screen_x0, screen_y0, screen_x1, screen_y1 = s["screen_bbox"]
            pdf_x0, pdf_y0, pdf_x1, pdf_y1 = s["pdf_bbox"]
            center_x, center_y = s["center"]

            # 先判断垂直方向是否在选区内
            if not (sel_widget_y0 <= center_y <= sel_widget_y1):
                continue

            # --- 确定当前 span 属于哪一行 ---
            is_first_line = abs(center_y - first_span_center_y) < 5  # 容忍微小差异
            is_last_line = abs(center_y - last_span_center_y) < 5

            # --- 智能插值逻辑 ---
            selected_text_part = ""
            highlight_pdf_x0, highlight_pdf_x1 = pdf_x0, pdf_x1

            if is_first_line and is_last_line:
                # 单行情况：精确裁剪
                clip_x0 = max(screen_x0, sel_widget_x0)
                clip_x1 = min(screen_x1, sel_widget_x1)
                if clip_x1 > clip_x0:
                    span_width = screen_x1 - screen_x0
                    if span_width > 0:
                        start_ratio = (clip_x0 - screen_x0) / span_width
                        end_ratio = (clip_x1 - screen_x0) / span_width
                        start_idx = int(len(text) * start_ratio)
                        end_idx = int(len(text) * end_ratio)
                        start_idx = max(0, min(start_idx, len(text)))
                        end_idx = max(0, min(end_idx, len(text)))
                        if start_idx < end_idx:
                            selected_text_part = text[start_idx:end_idx]
                            char_width = (pdf_x1 - pdf_x0) / len(text)
                            highlight_pdf_x0 = pdf_x0 + start_idx * char_width
                            highlight_pdf_x1 = pdf_x0 + end_idx * char_width
            elif is_first_line:
                # 第一行：从起点X到行尾
                if screen_x1 > sel_widget_x0:  # 有交集
                    clip_x0 = max(screen_x0, sel_widget_x0)
                    span_width = screen_x1 - screen_x0
                    if span_width > 0:
                        start_ratio = (clip_x0 - screen_x0) / span_width
                        start_idx = int(len(text) * start_ratio)
                        start_idx = max(0, min(start_idx, len(text)))
                        selected_text_part = text[start_idx:]
                        char_width = (pdf_x1 - pdf_x0) / len(text)
                        highlight_pdf_x0 = pdf_x0 + start_idx * char_width
                        highlight_pdf_x1 = pdf_x1
            elif is_last_line:
                # 最后一行：从行首到终点X
                if screen_x0 < sel_widget_x1:  # 有交集
                    clip_x1 = min(screen_x1, sel_widget_x1)
                    span_width = screen_x1 - screen_x0
                    if span_width > 0:
                        end_ratio = (clip_x1 - screen_x0) / span_width
                        end_idx = int(len(text) * end_ratio)
                        end_idx = max(0, min(end_idx, len(text)))
                        selected_text_part = text[:end_idx]
                        # === 修复：在这里重新计算 char_width ===
                        if len(text) > 0:
                            char_width = (pdf_x1 - pdf_x0) / len(text)
                            highlight_pdf_x0 = pdf_x0
                            highlight_pdf_x1 = pdf_x0 + end_idx * char_width
                        else:
                            highlight_pdf_x0, highlight_pdf_x1 = pdf_x0, pdf_x1
                        # =======================================
            else:
                # 中间完整行：全选
                selected_text_part = text
                highlight_pdf_x0, highlight_pdf_x1 = pdf_x0, pdf_x1

            if selected_text_part:
                selected_spans.append((center_y, center_x, selected_text_part))
                # 添加高亮矩形 (PDF 坐标 -> Pixmap 坐标)
                highlight_rects.append(
                    [
                        highlight_pdf_x0 * render_scale,
                        pdf_y0 * render_scale,
                        (highlight_pdf_x1 - highlight_pdf_x0) * render_scale,
                        (pdf_y1 - pdf_y0) * render_scale,
                    ]
                )

        selected_spans.sort(key=lambda item: (item[0], item[1]))
        self.selected_text = "".join(text for _, _, text in selected_spans)
        self.text_selection_highlights = [
            {"rect": rect, "color": QColor(0, 100, 255, 80)} for rect in highlight_rects
        ]
        self.update()

    def set_annotation_mode(self, mode):
        """设置批注模式"""
        # 取消当前所有批注模式
        self.cancel_annotation()
        self.annotation_mode = mode
        if mode == "pen":
            self.setCursor(Qt.CrossCursor)
        elif mode == "rect":
            self.setCursor(Qt.CrossCursor)
        elif mode == "text":
            self.setCursor(Qt.IBeamCursor)
        else:
            self.setCursor(Qt.ArrowCursor)

    def set_pen_color(self, color):
        """设置画笔颜色"""
        self.pen_color = QColor(color)

    def set_rect_color(self, color):
        """设置矩形高亮颜色"""
        self.rect_color = QColor(color)

    def set_text_color(self, color):
        """设置文本颜色"""
        self.text_color = QColor(color)


class TactiReader(QMainWindow):
    def __init__(self, pdf_path=None):
        # 修复dpi导致吞字问题
        QApplication.setAttribute(Qt.AA_EnableHighDpiScaling)
        QApplication.setAttribute(Qt.AA_UseHighDpiPixmaps)
        super().__init__()
        self.config_manager = ConfigManager()
        # 设置全局字体：中文用微软雅黑，英文用等宽粗体
        font = QFont()
        font.setFamily("Microsoft YaHei, Consolas, Courier New, monospace")
        font.setPointSize(9)
        self.setFont(font)
        # 主题系统会先设置背景，这里不再硬编码
        # === 国际化支持 ===
        # 1. 首先加载全局语言设置
        self.current_lang = "en"  # 默认语言
        self.translations = {
            "en": {},
            "zh": {
                # === 文件菜单 ===
                "File": "文件",
                "Open PDF...": "打开 PDF...",
                "Save As PDF...": "另存为 PDF...",
                "Save As PDF": "另存为 PDF",
                "PDF Files (*.pdf)": "PDF 文件 (*.pdf)",
                "Export Notebook...": "导出笔记...",
                "Open Notebook...": "打开笔记...",
                "Save Notebook": "保存笔记",
                "TactiReader Notebook (*.tactinote)": "TactiReader 笔记 (*.tactinote)",
                "Recent Files": "最近文件",
                "<No recent files>": "<无最近文件>",
                "Save Configuration (S)": "保存配置 (S)",
                # === 视图菜单 ===
                "View": "视图",
                "Toggle Single/Double Page Mode (Z)": "切换单/双页模式 (Z)",
                "Toggle Left Pane Lock/Follow (C)": "切换左右页联动/解除 (C)",
                "Show/Hide Bookmarks & TOC Panel (N)": "显示/隐藏书签与目录面板 (N)",
                "Toggle Fullscreen (F11)": "全屏/退出全屏 (F11)",
                "Rotate Current Page Clockwise (~)": "顺时针旋转当前页 (~)",
                "Reset Current Page (X)": "重置当前页面 (X)",
                "Center Splitter and Reset (Ctrl+X)": "居中分隔条并重置 (Ctrl+X)",
                "Clear All Page Rotations (Ctrl+Shift+X)": "清除全文档旋转 (Ctrl+Shift+X)",
                "Theme": "颜色模式",
                "docs/help.md": "docs/help_zh.md",
                "docs/about.md": "docs/about_zh.md",
                # === 导航菜单 ===
                "Navigation": "导航",
                "Go to Page... (G)": "跳转到页码... (G)",
                "Go to Page": "跳转到页码",
                "Enter page number ({min}-{max}):": "输入页码 ({min}-{max})：",
                "Enter a number between {min} and {max}": "请输入 {min} 到 {max} 的页面",
                "Page number must be between 1 and {total_pages}": "页码必须在 1 到 {total_pages} 之间",
                "Please enter a valid number": "请输入有效数字",
                "Calibrate Physical Page Number... (Ctrl+G)": "标定物理页码... (Ctrl+G)",
                "Page Number Calibration": "页面标定",
                "Enter logical page number for physical page {physical}:": "输入物理第 {physical}页对应的逻辑页码:",
                "Clear Physical Page Offset (Ctrl+Shift+G)": "清除物理页码偏移 (Ctrl+Shift+G)",
                "Full-Text Search... (F)": "全文搜索... (F)",
                "Search in PDF": "在 PDF 中搜索",
                "Navigation Back (Ctrl+A)": "导航回退 (Ctrl+A)",
                "Set Flip Multiplier": "设置翻页倍数",
                "Flip by Multiplier": "按倍数翻页",
                "Next Pages (→)": "向前翻页 (→)",
                "Previous Pages (←)": "向后翻页 (←)",
                "Single Page Flip": "单页翻页",
                "Next Page (D)": "下一页 (D)",
                "Previous Page (A)": "上一页 (A)",
                "Jump to Home (Space)": "返回主页 (空格)",
                "Set Current Page as Home (Ctrl+Space)": "将当前页设为主页 (Ctrl+空格)",
                # === 瞬时书签 ===
                "Instant Bookmarks": "瞬时书签",
                "Jump To": "跳转",
                "Set": "设置",
                "Clear": "清除",
                "Jump to 'Q' (Q)": "跳转到 'Q' (Q)",
                "Jump to 'W' (W)": "跳转到 'W' (W)",
                "Jump to 'E' (E)": "跳转到 'E' (E)",
                "Jump to 'R' (R)": "跳转到 'R' (R)",
                "Jump to 'T' (T)": "跳转到 'T' (T)",
                "Jump to 'Y' (Y)": "跳转到 'Y' (Y)",
                "Jump to 'U' (U)": "跳转到 'U' (U)",
                "Jump to 'I' (I)": "跳转到 'I' (I)",
                "Jump to 'O' (O)": "跳转到 'O' (O)",
                "Jump to 'P' (P)": "跳转到 'P' (P)",
                "Set 'Q' Here (Ctrl+Q)": "在此处设置 'Q' (Ctrl+Q)",
                "Set 'W' Here (Ctrl+W)": "在此处设置 'W' (Ctrl+W)",
                "Set 'E' Here (Ctrl+E)": "在此处设置 'E' (Ctrl+E)",
                "Set 'R' Here (Ctrl+R)": "在此处设置 'R' (Ctrl+R)",
                "Set 'T' Here (Ctrl+T)": "在此处设置 'T' (Ctrl+T)",
                "Set 'Y' Here (Ctrl+Y)": "在此处设置 'Y' (Ctrl+Y)",
                "Set 'U' Here (Ctrl+U)": "在此处设置 'U' (Ctrl+U)",
                "Set 'I' Here (Ctrl+I)": "在此处设置 'I' (Ctrl+I)",
                "Set 'O' Here (Ctrl+O)": "在此处设置 'O' (Ctrl+O)",
                "Set 'P' Here (Ctrl+P)": "在此处设置 'P' (Ctrl+P)",
                "Clear 'Q' (Alt+Q)": "清除 'Q' (Alt+Q)",
                "Clear 'W' (Alt+W)": "清除 'W' (Alt+W)",
                "Clear 'E' (Alt+E)": "清除 'E' (Alt+E)",
                "Clear 'R' (Alt+R)": "清除 'R' (Alt+R)",
                "Clear 'T' (Alt+T)": "清除 'T' (Alt+T)",
                "Clear 'Y' (Alt+Y)": "清除 'Y' (Alt+Y)",
                "Clear 'U' (Alt+U)": "清除 'U' (Alt+U)",
                "Clear 'I' (Alt+I)": "清除 'I' (Alt+I)",
                "Clear 'O' (Alt+O)": "清除 'O' (Alt+O)",
                "Clear 'P' (Alt+P)": "清除 'P' (Alt+P)",
                "Set Bookmark": "设置书签",
                "Name for '{char}' (P.{page}):": "'{char}' 的名称（第 {page} 页）：",
                "🔖 '{char}' → {display_name}": "🔖 '{char}' → {display_name}",
                "⏩ '{char}': {display_name}": "⏩ '{char}'：{display_name}",
                "⚠️ '{char}' not set": "⚠️ '{char}' 未设置",
                # === 批注菜单 ===
                "Annotations": "批注",
                "Pen Mode (B)": "画笔模式 (B)",
                "Highlight Mode (H)": "高亮模式 (H)",
                "Text Mode (V)": "文本模式 (V)",
                "Finish or Exit Current Annotation (Esc)": "完成或退出当前批注 (Esc)",
                "Confirm Text Annotation (Ctrl+Enter)": "确认文字批注 (Ctrl+Enter)",
                "Set Text Font Size...": "设置文字大小...",
                "Text font size (pt):": "文字大小（磅）：",
                "Invalid font size.": "字体大小无效。",
                "Pen Color": "画笔颜色",
                "Highlight Color": "高亮颜色",
                "Text Color": "文字颜色",
                "Pen Color 1": "画笔颜色 1",
                "Pen Color 2": "画笔颜色 2",
                "Pen Color 3": "画笔颜色 3",
                "Pen Color 4": "画笔颜色 4",
                "Pen Color 5": "画笔颜色 5",
                "Pen Color 6": "画笔颜色 6",
                "Pen Color 7": "画笔颜色 7",
                "Pen Color 8": "画笔颜色 8",
                "Pen Color 9": "画笔颜色 9",
                "Pen Color 10": "画笔颜色 10",
                "Highlight Color 1": "高亮颜色 1",
                "Highlight Color 2": "高亮颜色 2",
                "Highlight Color 3": "高亮颜色 3",
                "Highlight Color 4": "高亮颜色 4",
                "Highlight Color 5": "高亮颜色 5",
                "Highlight Color 6": "高亮颜色 6",
                "Highlight Color 7": "高亮颜色 7",
                "Highlight Color 8": "高亮颜色 8",
                "Text Color 1": "文字颜色 1",
                "Text Color 2": "文字颜色 2",
                "Text Color 3": "文字颜色 3",
                "Text Color 4": "文字颜色 4",
                "Text Color 5": "文字颜色 5",
                "Text Color 6": "文字颜色 6",
                "Text Color 7": "文字颜色 7",
                "Text Color 8": "文字颜色 8",
                "Undo Last Annotation (Ctrl+Z)": "撤销上一条批注 (Ctrl+Z)",
                "Clear Current Page Annotations (Ctrl+Shift+C)": "清除当前页所有批注 (Ctrl+Shift+C)",
                "Global Reset (Ctrl+Shift+R)": "全局重置 (Ctrl+Shift+R)",
                "✏️ Pen mode (press ESC to cancel)": "✏️ 画笔模式（按 ESC 取消）",
                "🔲 Highlight mode (press ESC to cancel)": "🔲 高亮模式（按 ESC 取消）",
                "📝 Text mode (press ESC to cancel)": "📝 文本模式（按 ESC 取消）",
                "🗑️ Cleared annotations on page {page}": "🗑️ 已清除第 {page} 页批注",
                "↩️ Undo last annotation on page {page}": "↩️ 已撤销第 {page} 页最后一条批注",
                "ℹ️ No annotations to undo on page {page}": "ℹ️ 第 {page} 页无可撤销批注",
                # === 工具菜单 ===
                "Tools": "工具",
                "Toggle Text Selection Mode (J)": "进入或退出文字选取模式 (J)",
                "Copy Selected Text (Ctrl+C)": "复制选中文本 (Ctrl+C)",
                "Copy": "复制",
                "Copied to clipboard": "已复制到剪贴板",
                # === 帮助菜单 ===
                "Help": "帮助",
                "TactiReader Help": "战术阅读器 帮助",
                "About TactiReader": "关于 战术阅读器",
                "About": "关于",
                "Language": "语言",
                "English": "English",
                "简体中文": "简体中文",
                "Language Changed": "语言已更改",
                "Please restart TactiReader to apply the new language.": "请重启 TactiReader 以应用新语言。",
                # === 通用 UI / 消息 ===
                "TactiReader": "战术阅读器",
                "Document Outline": "文档目录",
                "Search Highlight": "搜索高亮",
                "Focus: Left": "焦点：左窗格",
                "Focus: Right": "焦点：右窗格",
                "Focus: None": "焦点：无",
                "Single": "单页",
                "Double": "双页",
                "None": "无",
                "↔️ Mode: {mode}-page": "↔️ 模式：{mode}页",
                "⬅️ Left pane: Locked": "🔓 已解除联动",
                "⬅️ Left pane: Following": "🔗 左右联动",
                "Unlinked": "已解除联动",
                "Linked": "左右联动",
                "🔁 Flip ×{x}": "🔁 翻页倍数 ×{x}",
                "🔄 Home reset to P.{page}": "🔄 主页重置为第 {page} 页",
                "🔄 Current pages reset (zoom+pan+rotation) & splitter centered": "🔄 当前页面重置（缩放+平移+旋转）且分隔条居中",
                "🔄 Left rotated to {angle}°": "🔄 左页旋转至 {angle}°",
                "🔄 Right rotated to {angle}°": "🔄 右页旋转至 {angle}°",
                "🗑️ All page rotations cleared for entire book!": "🗑️ 已清除整本书所有页面的旋转！",
                "💾 Configuration saved": "💾 配置已保存",
                "🗑️ All configuration cleared!": "🗑️ 所有配置已清除！",
                "<no bookmarks>": "<无书签>",
                # === 搜索对话框 ===
                "Search:": "搜索：",
                "Search": "搜索",
                "Enter search term...": "输入搜索内容...",
                "Found {count} result(s)": "找到 {count} 个结果",
                "No results": "无结果",
                "◀ Previous": "◀ 上一个",
                "Next ▶": "下一个 ▶",
                "Close": "关闭",
                "🔍 {context}": "🔍 {context}",
                # === 弹窗确认 ===
                "Clear All Config": "清除全部配置",
                "Are you sure you want to clear ALL settings (bookmarks, home, mode, etc.) for this PDF?": "确定要清除本 PDF 的所有设置（书签、主页、模式等）吗？",
                "Error": "错误",
                "OK": "确认",
                "Cancel": "取消",
                # === 笔记导入/导出消息 ===
                "No document is open.": "未打开任何文档。",
                "Failed to locate config file.": "无法定位配置文件。",
                "Notebook exported to: {}": "笔记已导出至：{}",
                "Failed to export notebook": "笔记导出失败",
                "Notebook imported from: {}": "笔记已从 {} 导入",
                "Failed to import notebook": "笔记导入失败",
                "Notebook saved.": "笔记已保存。",
                # === 多文档功能 ===
                "Open in New Window": "在新窗口中打开",
                # =================
            },
        }

        global_config = self.config_manager.load_global_config()
        lang_from_global_config = global_config.get("language", "en")
        if lang_from_global_config in self.translations:
            self.current_lang = lang_from_global_config

        # 读取保存的主题设置
        self.current_theme = global_config.get("theme", "light")

        # === NEW CODE START ===
        # 初始化最近文件列表
        self.recent_files = [
            f for f in global_config.get("recent_files", []) if os.path.isfile(f)
        ]
        # === 初始化全局打开文档列表 ===
        self.open_documents = [
            f
            for f in global_config.get("open_documents", [])
            if os.path.isfile(f)
            and (f.lower().endswith(".pdf") or f.lower().endswith(".tactinote") or f.lower().endswith(".epub"))
        ]
        # 保存上次阅读的文档
        self.last_read_document = global_config.get("current_document", "")
        # ==============================
        # === NEW CODE END ===

        # 2. 初始化核心变量
        self.pdf_path = None
        # === 新增：笔记本模式状态 ===
        self.notebook_source_path = None  # 记录源 .tactinote 文件路径
        # ==========================
        self.doc = None
        self.total_pages = 0
        self.is_epub = False
        self.epub_layout_params = None
        self._epub_chapter_map = {}       # page_num(1-idx) → html_filename
        self._epub_images_src = []        # 缓存的图片列表
        self._epub_footnotes_src = []     # 缓存的脚注列表
        self.last_focused_pane = "right"  # 可选值: 'left' 或 'right'
        self._theme_page_cache = {}  # 主题页面缓存：(page_num, theme) -> QPixmap
        # Auto-show help on first run (if no bookmarks/config exist)
        if not os.listdir(CONFIG_DIR) and not (pdf_path or self.recent_files):
            # 弹出独立的语言选择对话框
            lang_dlg = LanguageSelectDialog(self)
            lang_dlg.exec_()
            chosen_lang = lang_dlg.selected_lang

            # 立即设置并保存语言（不调用 set_language）
            self.current_lang = chosen_lang
            os.makedirs(os.path.dirname(GLOBAL_CONFIG_FILE), exist_ok=True)
            with open(GLOBAL_CONFIG_FILE, "w") as f:
                json.dump({"global_config": {"language": chosen_lang}}, f, indent=2)

            # 再弹帮助
            QTimer.singleShot(300, self.show_help)
        # === NEW CODE END ===
        # 3. 现在可以安全地创建UI元素，它们会使用正确的语言
        self.setWindowTitle(self.tr("TactiReader"))
        self.setWindowIcon(QIcon(resource_path("tactireader.png")))
        self.setGeometry(100, 100, 1200, 800)
        self.setFocusPolicy(Qt.StrongFocus)

        central = QWidget()
        self.setCentralWidget(central)

        # === 替换开始：使用 QSplitter 实现可拖动分隔 ===
        from PyQt5.QtWidgets import QSplitter

        # 创建主水平布局: [Bookmark Panel] | [Splitter(Left|Right)]
        main_layout = QHBoxLayout(central)
        main_layout.setSpacing(5)

        # Bookmark panel (保持不变)
        self.bookmark_panel = QWidget()
        self.bookmark_panel.setFixedWidth(180)

        self.bookmark_layout = QVBoxLayout(self.bookmark_panel)
        self.bookmark_layout.setAlignment(Qt.AlignTop)
        self.bookmark_layout.setSpacing(4)
        self.bookmark_layout.setContentsMargins(6, 6, 6, 6)

        # 文档目录按钮（始终可见）
        self._toc_panel_btn = QPushButton("📄 " + self.tr("Document Outline"))
        toc_font = QFont()
        toc_font.setFamily("Microsoft YaHei, Consolas, Courier New, monospace")
        toc_font.setPointSize(9)
        toc_font.setBold(True)
        self._toc_panel_btn.setFont(toc_font)
        self._toc_panel_btn.setStyleSheet("""
            text-align: left;
            padding: 4px;
            border: none;
            background: transparent;
        """)
        self._toc_panel_btn.clicked.connect(self.open_toc_dialog)
        self.bookmark_layout.addWidget(self._toc_panel_btn)

        main_layout.addWidget(self.bookmark_panel)
        self.bookmark_panel_visible = False
        self.bookmark_panel.setVisible(False)
        # 创建左右窗格
        self.left_pane = TacticalPane(self)
        self.left_pane.is_left_pane = True  # ← 关键：标记为左窗格
        self.right_pane = TacticalPane(self)
        self.right_pane.is_left_pane = False  # ← 关键：标记为右窗格
        # === 新增：连接焦点信号 ===
        self.left_pane.focused.connect(self._on_reading_pane_focused)
        self.right_pane.focused.connect(self._on_reading_pane_focused)

        # 创建 splitter 并添加窗格
        self.splitter = QSplitter(Qt.Horizontal)
        self.splitter.addWidget(self.left_pane)
        self.splitter.addWidget(self.right_pane)
        self.splitter.setHandleWidth(6)  # 分隔条宽度
        self.splitter.setSizes([500, 500])

        # === 创建中央区域（直接放 splitter，不再需要标签栏）===
        central_widget = QWidget()
        central_layout = QVBoxLayout(central_widget)
        central_layout.setContentsMargins(0, 0, 0, 0)
        central_layout.addWidget(self.splitter)
        main_layout.addWidget(central_widget)
        # State
        self.single_page_mode = False
        self.right_page = 1
        self.home_page = 1
        self.annotation_mode = None
        self.bookmarks = {}
        self.pdf_toc = []  # 存储 [(level, title, page), ...]
        self.toc_state = (1, "")  # (maxVisibleDepth, selectedId)
        self.text_annotation_font_size = 25  # 文字批注字体大小（pt）
        self.flip_multiplier = 2
        self.config_file = None
        self.left_locked = False
        self.locked_left_page = 1

        # 旋转状态
        self.page_rotations = {}  # 格式: {page_num: rotation_angle}
        self.page_number_offset = 0  # ← 新增：页码数字偏移（逻辑页 = 物理页 + offset）
        self.restore_left_view = False
        self.restore_right_view = False

        # 批注存储
        self.annotations = {}  # 格式: {page_num: [annotations]}

        # 搜索高亮相关
        self.search_highlights = {}  # {page_num: [{'rect': QRectF, 'color': QColor}, ...]}
        self.current_search_term = ""
        self.search_highlight_color = QColor(255, 255, 0, 60)  # 半透明黄色
        # === 历史栈：左右窗格独立，最多5步 ===
        # === 单步历史：左右窗格独立，仅保留最近一次跨页跳转前的位置 ===
        self.left_last_location = None  # (page_num, rotation, scale, offset) 或 None
        self.right_last_location = None  # 同上
        # ==================================================================
        # ===================================
        # 颜色设置 - 每个功能独立
        self.pen_colors = [QColor(*value) for value in PEN_COLOR_PRESETS]
        self.rect_colors = [QColor(*value) for value in RECT_COLOR_PRESETS]
        self.text_colors = [QColor(*value) for value in TEXT_COLOR_PRESETS]

        # 当前颜色索引
        self.current_pen_color_index = 0  # 默认纯正红
        self.current_rect_color_index = 0  # 默认纯正红
        self.current_text_color_index = 0  # 默认纯正红

        self.update_pane_colors()

        # === 全新菜单栏：TactiReader v2.0 防呆版 ===
        menubar = self.menuBar()
        # === 强制菜单栏为 VS Code 风格浅灰（不随系统变色）===
        menubar.setStyleSheet("""
            QMenuBar {
                background-color: #f8f8f8;
                color: #111111;
                border: none;
                padding: 2px;
                font-family: "Microsoft YaHei", "Consolas", sans-serif;
                font-size: 10pt;
                font-weight:450;
            }
            QMenuBar::item {
                background: transparent;
                padding: 4px 12px;
                border-radius: 4px;
            }
            QMenuBar::item:selected {
                background: rgba(0, 0, 0, 0.1);
            }
            QMenuBar::item:pressed {
                background: rgba(0, 0, 0, 0.2);
            }
            /* 子菜单样式 */
            QMenu {
                background-color: #fffffe;
                color: #111111;
                border: 1px solid #d0d0d0;
                font-weight:450;
            }
            QMenu::item {
                padding: 6px 24px;
            }
            QMenu::item:selected {
                background-color: #e6f0ff;
            }
            QMenu::item:checked {
                background-color: #d0e8ff;
                font-weight: bold;
            }
            QMenu::indicator {
                width: 14px;
                height: 14px;
            }
            QMenu::indicator:checked {
                image: none;
                border: 2px solid #1A73E8;
                background: #e6f0ff;
                border-radius: 2px;
            }
        """)
        # ===================================================
        # --- 文件 (File) ---
        file_menu = menubar.addMenu(self.tr("File"))
        open_action = QAction(self.tr("打开电子书..."), self)
        open_action.triggered.connect(self.open_pdf_dialog)
        file_menu.addAction(open_action)

        self.save_as_pdf_action = QAction(self.tr("另存为 PDF..."), self)
        self.save_as_pdf_action.triggered.connect(self.save_as_pdf)
        file_menu.addAction(self.save_as_pdf_action)

        file_menu.addSeparator()

        self.export_notebook_action = QAction(self.tr("导出笔记..."), self)
        self.export_notebook_action.triggered.connect(self.export_notebook)
        file_menu.addAction(self.export_notebook_action)

        import_notebook_action = QAction(self.tr("Open Notebook..."), self)
        import_notebook_action.triggered.connect(self.import_notebook)
        file_menu.addAction(import_notebook_action)

        file_menu.addSeparator()

        # 最近文件子菜单 (复用已有逻辑)
        self.recent_menu = file_menu.addMenu(self.tr("Recent Files"))
        self.update_recent_files_menu()

        file_menu.addSeparator()

        # 保存配置 (S)
        save_config_action = QAction(self.tr("Save Configuration (S)"), self)
        save_config_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_S))
        file_menu.addAction(save_config_action)

        # --- 视图 (View) ---
        view_menu = menubar.addMenu(self.tr("View"))
        # 切换单/双页模式 (Z)
        toggle_mode_action = QAction(
            self.tr("Toggle Single/Double Page Mode (Z)"), self
        )
        toggle_mode_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_Z))
        view_menu.addAction(toggle_mode_action)

        # 切换左窗格锁定/跟随 (C)
        toggle_lock_action = QAction(self.tr("Toggle Left Pane Lock/Follow (C)"), self)
        toggle_lock_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_C))
        view_menu.addAction(toggle_lock_action)

        view_menu.addSeparator()

        # 显示/隐藏书签与目录面板 (N)
        toggle_sidebar_action = QAction(
            self.tr("Show/Hide Bookmarks & TOC Panel (N)"), self
        )
        toggle_sidebar_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_N)
        )
        view_menu.addAction(toggle_sidebar_action)

        # 全屏/退出全屏 (F11)
        toggle_fullscreen_action = QAction(self.tr("Toggle Fullscreen (F11)"), self)
        toggle_fullscreen_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_F11)
        )
        view_menu.addAction(toggle_fullscreen_action)

        # EPUB 重新排版设置
        self.epub_relayout_action = QAction(self.tr("EPUB 排版设置..."), self)
        self.epub_relayout_action.triggered.connect(self._epub_relayout_settings)
        self.epub_relayout_action.setVisible(False)
        view_menu.addAction(self.epub_relayout_action)

        view_menu.addSeparator()

        # 顺时针旋转当前页 (`)
        rotate_clockwise_action = QAction(
            self.tr("Rotate Current Page Clockwise (~)"), self
        )
        rotate_clockwise_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_QuoteLeft)
        )
        view_menu.addAction(rotate_clockwise_action)

        # 重置当前页面 (X)
        reset_current_action = QAction(self.tr("Reset Current Page (X)"), self)
        reset_current_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_X))
        view_menu.addAction(reset_current_action)

        # 居中分隔条并重置 (Ctrl+X)
        reset_both_action = QAction(self.tr("Center Splitter and Reset (Ctrl+X)"), self)
        reset_both_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_X, Qt.ControlModifier)
        )
        view_menu.addAction(reset_both_action)

        # 清除全文档旋转 (Ctrl+Shift+X)
        clear_all_rotations_action = QAction(
            self.tr("Clear All Page Rotations (Ctrl+Shift+X)"), self
        )
        clear_all_rotations_action.triggered.connect(
            lambda: self._trigger_shortcut(
                Qt.Key_X, Qt.ControlModifier | Qt.ShiftModifier
            )
        )
        view_menu.addAction(clear_all_rotations_action)

        view_menu.addSeparator()

        # 主题切换子菜单
        theme_menu = view_menu.addMenu(self.tr("Theme"))
        self._theme_actions = {}
        for name in THEMES:
            act = QAction(THEME_NAMES.get(name, name.capitalize()), self)
            act.setCheckable(True)
            act.triggered.connect(lambda checked, n=name: self.apply_theme(n))
            theme_menu.addAction(act)
            self._theme_actions[name] = act

        # --- 导航 (Navigation) ---
        nav_menu = menubar.addMenu(self.tr("Navigation"))
        # 跳转到页码... (G)
        goto_page_action = QAction(self.tr("Go to Page... (G)"), self)
        goto_page_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_G))
        nav_menu.addAction(goto_page_action)

        # 标定物理页码... (Ctrl+G)
        calibrate_page_action = QAction(
            self.tr("Calibrate Physical Page Number... (Ctrl+G)"), self
        )
        calibrate_page_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_G, Qt.ControlModifier)
        )
        nav_menu.addAction(calibrate_page_action)

        # 清除物理页码偏移 (Ctrl+Shift+G)
        clear_page_offset_action = QAction(
            self.tr("Clear Physical Page Offset (Ctrl+Shift+G)"), self
        )
        clear_page_offset_action.triggered.connect(
            lambda: self._trigger_shortcut(
                Qt.Key_G, Qt.ControlModifier | Qt.ShiftModifier
            )
        )
        nav_menu.addAction(clear_page_offset_action)

        # 全文搜索... (F)
        search_action = QAction(self.tr("Full-Text Search... (F)"), self)
        search_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_F))
        nav_menu.addAction(search_action)

        # PDF 目录导航... (L) — 快捷键由 QShortcut 全局注册，菜单项仅作展示
        toc_action = QAction(self.tr("PDF Table of Contents... (L)"), self)
        toc_action.triggered.connect(self.open_toc_dialog)
        nav_menu.addAction(toc_action)

        # 导航回退 (Ctrl+A)
        navigate_back_action = QAction(self.tr("Navigation Back (Ctrl+A)"), self)
        navigate_back_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_A, Qt.ControlModifier)
        )
        nav_menu.addAction(navigate_back_action)

        nav_menu.addSeparator()

        # 设置翻页倍数
        multiplier_menu = nav_menu.addMenu(self.tr("Set Flip Multiplier"))
        for i in range(1, 10):
            action = QAction(self.tr(f"×{i} ({i})"), self)
            action.triggered.connect(
                lambda checked, num=i: self._trigger_shortcut(getattr(Qt, f"Key_{num}"))
            )
            multiplier_menu.addAction(action)

        nav_menu.addSeparator()

        # 按倍数翻页
        flip_by_multiplier_menu = nav_menu.addMenu(self.tr("Flip by Multiplier"))
        next_by_mult_action = QAction(self.tr("Next Pages (→)"), self)
        next_by_mult_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_Right)
        )
        flip_by_multiplier_menu.addAction(next_by_mult_action)
        prev_by_mult_action = QAction(self.tr("Previous Pages (←)"), self)
        prev_by_mult_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_Left)
        )
        flip_by_multiplier_menu.addAction(prev_by_mult_action)

        # 单页翻页
        single_flip_menu = nav_menu.addMenu(self.tr("Single Page Flip"))
        next_page_action = QAction(self.tr("Next Page (D)"), self)
        next_page_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_D))
        single_flip_menu.addAction(next_page_action)
        prev_page_action = QAction(self.tr("Previous Page (A)"), self)
        prev_page_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_A))
        single_flip_menu.addAction(prev_page_action)

        nav_menu.addSeparator()

        # 返回主页 (空格)
        jump_to_home_action = QAction(self.tr("Jump to Home (Space)"), self)
        jump_to_home_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_Space)
        )
        nav_menu.addAction(jump_to_home_action)

        # 将当前页设为主页 (Ctrl+空格)
        set_home_action = QAction(
            self.tr("Set Current Page as Home (Ctrl+Space)"), self
        )
        set_home_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_Space, Qt.ControlModifier)
        )
        nav_menu.addAction(set_home_action)

        nav_menu.addSeparator()

        # 瞬时书签
        bookmark_menu = nav_menu.addMenu(self.tr("Instant Bookmarks"))
        # 跳转
        jump_sub_menu = bookmark_menu.addMenu(self.tr("Jump To"))
        for key_char in ["Q", "W", "E", "R", "T", "Y", "U", "I", "O", "P"]:
            qt_key = getattr(Qt, f"Key_{key_char}")
            action = QAction(self.tr(f"Jump to '{key_char}' ({key_char})"), self)
            action.triggered.connect(
                lambda checked, k=qt_key: self._trigger_shortcut(k)
            )
            jump_sub_menu.addAction(action)
        # 设置
        set_sub_menu = bookmark_menu.addMenu(self.tr("Set"))
        for key_char in ["Q", "W", "E", "R", "T", "Y", "U", "I", "O", "P"]:
            qt_key = getattr(Qt, f"Key_{key_char}")
            action = QAction(self.tr(f"Set '{key_char}' Here (Ctrl+{key_char})"), self)
            action.triggered.connect(
                lambda checked, k=qt_key: self._trigger_shortcut(k, Qt.ControlModifier)
            )
            set_sub_menu.addAction(action)
        # 清除
        clear_sub_menu = bookmark_menu.addMenu(self.tr("Clear"))
        for key_char in ["Q", "W", "E", "R", "T", "Y", "U", "I", "O", "P"]:
            qt_key = getattr(Qt, f"Key_{key_char}")
            action = QAction(self.tr(f"Clear '{key_char}' (Alt+{key_char})"), self)
            action.triggered.connect(
                lambda checked, k=qt_key: self._trigger_shortcut(k, Qt.AltModifier)
            )
            clear_sub_menu.addAction(action)

        # --- 批注 (Annotation) ---
        annot_menu = menubar.addMenu(self.tr("Annotations"))
        # 画笔模式 (B)
        pen_action = QAction(self.tr("Pen Mode (B)"), self)
        pen_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_B))
        annot_menu.addAction(pen_action)
        # 高亮模式 (H)
        highlight_action = QAction(self.tr("Highlight Mode (H)"), self)
        highlight_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_H))
        annot_menu.addAction(highlight_action)
        # 文本模式 (V)
        text_action = QAction(self.tr("Text Mode (V)"), self)
        text_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_V))
        annot_menu.addAction(text_action)
        # 完成或退出当前批注 (Esc)
        esc_action = QAction(self.tr("Finish or Exit Current Annotation (Esc)"), self)
        esc_action.triggered.connect(lambda: self._trigger_shortcut(Qt.Key_Escape))
        annot_menu.addAction(esc_action)
        # 确认文字批注 (Ctrl+Enter)
        confirm_text_action = QAction(
            self.tr("Confirm Text Annotation (Ctrl+Enter)"), self
        )
        confirm_text_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_Return, Qt.ControlModifier)
        )
        annot_menu.addAction(confirm_text_action)
        # 设置文字批注字体大小
        set_font_size_action = QAction(self.tr("Set Text Font Size..."), self)
        set_font_size_action.triggered.connect(self.set_text_annotation_font_size)
        annot_menu.addAction(set_font_size_action)

        annot_menu.addSeparator()

        # 颜色选择 (复用你原有的逻辑)
        self._pen_color_actions = []
        pen_color_menu = annot_menu.addMenu(self.tr("Pen Color"))
        for i, color in enumerate(self.pen_colors):
            color_name = PEN_COLOR_NAMES[i] if i < len(PEN_COLOR_NAMES) else f"Color {i + 1}"
            color_action = QAction(self.tr(color_name), self)
            color_action.setCheckable(True)
            color_action.triggered.connect(
                lambda checked, idx=i: self.set_pen_color_index(idx)
            )
            pixmap = QPixmap(16, 16)
            pixmap.fill(color)
            color_action.setIcon(QIcon(pixmap))
            pen_color_menu.addAction(color_action)
            self._pen_color_actions.append(color_action)

        self._rect_color_actions = []
        rect_color_menu = annot_menu.addMenu(self.tr("Highlight Color"))
        for i, color in enumerate(self.rect_colors):
            color_name = RECT_COLOR_NAMES[i] if i < len(RECT_COLOR_NAMES) else f"Color {i + 1}"
            color_action = QAction(self.tr(color_name), self)
            color_action.setCheckable(True)
            color_action.triggered.connect(
                lambda checked, idx=i: self.set_rect_color_index(idx)
            )
            pixmap = QPixmap(16, 16)
            pixmap.fill(color)
            color_action.setIcon(QIcon(pixmap))
            rect_color_menu.addAction(color_action)
            self._rect_color_actions.append(color_action)

        self._text_color_actions = []
        text_color_menu = annot_menu.addMenu(self.tr("Text Color"))
        for i, color in enumerate(self.text_colors):
            color_name = TEXT_COLOR_NAMES[i] if i < len(TEXT_COLOR_NAMES) else f"Color {i + 1}"
            color_action = QAction(self.tr(color_name), self)
            color_action.setCheckable(True)
            color_action.triggered.connect(
                lambda checked, idx=i: self.set_text_color_index(idx)
            )
            pixmap = QPixmap(16, 16)
            pixmap.fill(color)
            color_action.setIcon(QIcon(pixmap))
            text_color_menu.addAction(color_action)
            self._text_color_actions.append(color_action)

        # 设置初始勾选状态
        self._update_color_menu_checks()

        annot_menu.addSeparator()

        # 撤销上一条批注 (Ctrl+Z)
        undo_action = QAction(self.tr("Undo Last Annotation (Ctrl+Z)"), self)
        undo_action.triggered.connect(
            lambda: self._trigger_shortcut(Qt.Key_Z, Qt.ControlModifier)
        )
        annot_menu.addAction(undo_action)
        # 清除当前页所有批注 (Ctrl+Shift+C)
        clear_current_annot_action = QAction(
            self.tr("Clear Current Page Annotations (Ctrl+Shift+C)"), self
        )
        clear_current_annot_action.triggered.connect(
            lambda: self._trigger_shortcut(
                Qt.Key_C, Qt.ControlModifier | Qt.ShiftModifier
            )
        )
        annot_menu.addAction(clear_current_annot_action)
        # 全局重置 (Ctrl+Shift+R)
        global_reset_action = QAction(self.tr("Global Reset (Ctrl+Shift+R)"), self)
        global_reset_action.triggered.connect(
            lambda: self._trigger_shortcut(
                Qt.Key_R, Qt.ControlModifier | Qt.ShiftModifier
            )
        )
        annot_menu.addAction(global_reset_action)

        # --- 工具 (Tools) ---
        tools_menu = menubar.addMenu(self.tr("Tools"))
        # 进入或退出文字选取模式 (J)
        toggle_text_select_action = QAction(
            self.tr("Toggle Text Selection Mode (J)"), self
        )
        toggle_text_select_action.triggered.connect(self.toggle_text_selection_mode)
        tools_menu.addAction(toggle_text_select_action)

        # --- 帮助 (Help) ---
        help_menu = menubar.addMenu(self.tr("Help"))
        help_action = QAction(self.tr("TactiReader Help"), self)
        help_action.triggered.connect(self.show_help)
        help_menu.addAction(help_action)
        about_action = QAction(self.tr("About TactiReader"), self)
        about_action.triggered.connect(self.show_about)
        help_menu.addAction(about_action)

        help_menu.addSeparator()

        # --- 语言 (Language) - 独立顶级菜单 ---
        lang_menu = menubar.addMenu(self.tr("Language"))
        en_action = QAction(self.tr("English"), self)
        zh_action = QAction(self.tr("简体中文"), self)
        en_action.triggered.connect(lambda: self.set_language("en"))
        zh_action.triggered.connect(lambda: self.set_language("zh"))
        lang_menu.addAction(en_action)
        lang_menu.addAction(zh_action)

        # --- 换书 / 删书（菜单形式替代顶部标签栏）---
        self.switch_book_menu = menubar.addMenu("换书")
        self.close_book_menu = menubar.addMenu("删书")
        self._book_menu_actions = []
        self._refresh_book_menus()

        # --- 默认大小（翻页时自动应用）---
        self.fit_menu = menubar.addMenu("默认大小")
        self.default_fit_mode = "fit_page"  # fit_width | fit_page | actual_size
        self._fit_actions = {}
        self._build_fit_menu()

        # 状态栏颜色显示
        self.color_status_label = QLabel()
        # 设置状态栏字体
        status_font = QFont()
        status_font.setFamily("Microsoft YaHei, Consolas, Courier New, monospace")
        status_font.setPointSize(9)
        self.color_status_label.setFont(status_font)

        # ✅ 关键：单独设置 QSS 加粗（更可靠）
        self.color_status_label.setStyleSheet("font-weight: 500; color: #000000;")
        # 设置状态栏字体
        status_font = QFont()
        status_font.setFamily("Microsoft YaHei, Consolas, Courier New, monospace")
        status_font.setPointSize(9)
        self.color_status_label.setFont(status_font)
        self.statusBar().addPermanentWidget(self.color_status_label)
        self.statusBar().setStyleSheet("""
        QStatusBar {
            background-color: #f8f8f8;
            color: #111111;
            border-top: 1px solid #e0e0e0;
            font-weight:480;
        }
    """)
        self.update_color_display()

        # 应用保存的主题
        self.apply_theme(self.current_theme)

        # 注册全局快捷键：L 打开文档目录（不依赖菜单栏可见性）
        self._toc_shortcut = QShortcut(
            QKeySequence("L"), self, self.open_toc_dialog
        )
        self._toc_shortcut.setContext(Qt.ApplicationShortcut)

        # 搜索对话框
        self.search_dialog = None

        self.setAcceptDrops(True)
        self.addAction(
            QAction(
                self.tr("Search in PDF"), self, shortcut="F", triggered=self.search_text
            )
        )
        # === 新增：全局 J 键 ===
        self.addAction(
            QAction(
                self.tr("Toggle Text Selection Mode"),
                self,
                shortcut="J",
                triggered=self.toggle_text_selection_mode,
            )
        )
        # === F11 全屏支持 ===
        self.addAction(
            QAction(
                self.tr("Toggle Fullscreen"),
                self,
                shortcut="F11",
                triggered=self.toggle_fullscreen,
            )
        )
        # ===================
        # === 新增：记录最后获得焦点的阅读窗格 ===
        self.last_focused_pane_is_left = False  # 默认右窗格
        # === NEW CODE START ===
        # === NEW CODE START ===
        # Auto-open: CLI path first, then all saved open documents
        if pdf_path and os.path.isfile(pdf_path):
            # 命令行参数优先
            if pdf_path.lower().endswith(".tactinote"):
                self.import_notebook_from_path(pdf_path)
                self.update_ui_text()
            elif pdf_path.lower().endswith(".epub"):
                self.load_epub(pdf_path)
                self.update_ui_text()
            elif pdf_path.lower().endswith(".pdf"):
                self.load_pdf(pdf_path)
                self.update_ui_text()
        elif self.open_documents:
            # 优先加载上次阅读的文档，否则加载第一本
            last_read_abs = os.path.abspath(self.last_read_document) if self.last_read_document else ""
            initial_doc = None
            if last_read_abs:
                for doc_path in self.open_documents:
                    if os.path.abspath(doc_path) == last_read_abs and os.path.isfile(doc_path):
                        initial_doc = doc_path
                        break
            if initial_doc is None and self.open_documents:
                initial_doc = self.open_documents[0]

            if initial_doc:
                if initial_doc.lower().endswith(".tactinote"):
                    self.import_notebook_from_path(initial_doc)
                    self.update_ui_text()
                elif initial_doc.lower().endswith(".epub"):
                    self.load_epub(initial_doc)
                    self.update_ui_text()
                elif initial_doc.lower().endswith(".pdf"):
                    self.load_pdf(initial_doc)
                    self.update_ui_text()
        # === NEW CODE END ===

    def import_notebook_from_path(self, notebook_path):
        """从给定路径导入笔记本，不弹出文件对话框"""
        if not os.path.isfile(notebook_path):
            return
        abs_notebook_path = os.path.abspath(notebook_path)
        if abs_notebook_path not in self.open_documents:
            self.open_documents.append(abs_notebook_path)
            self.save_global_config()
        try:
            hash_id = hashlib.md5(notebook_path.encode("utf-8")).hexdigest()[:12]
            temp_base_dir = os.path.join(CONFIG_DIR, "..", "temp")
            os.makedirs(temp_base_dir, exist_ok=True)
            work_dir = os.path.join(temp_base_dir, f"nb_{hash_id}")
            os.makedirs(work_dir, exist_ok=True)

            pdf_path = os.path.join(work_dir, "document.pdf")
            session_json_path = os.path.join(work_dir, "session.json")

            with zipfile.ZipFile(notebook_path, "r") as zf:
                zf.extract("document.pdf", work_dir)
                zf.extract("session.json", work_dir)

            if self.doc:
                self.doc.close()
            self.doc = fitz.open(pdf_path)
            self.pdf_path = notebook_path
            self.is_epub = False
            self.epub_layout_params = None
            self._epub_chapter_map = {}
            self._epub_images_src = []
            self._epub_footnotes_src = []
            self.total_pages = len(self.doc)

            # === 清空页面缓存，避免旧文档页面残留 ===
            self._theme_page_cache.clear()
            # ======================================

            # === 关键修复：重置所有全局状态（与 load_pdf 一致）
            self.notebook_source_path = notebook_path
            self.config_file = session_json_path
            self.annotations = {}
            self.bookmarks = {}
            self.page_rotations = {}
            self.page_number_offset = 0
            self.home_page = 1
            self.flip_multiplier = 2
            self.single_page_mode = False
            self.right_page = 1
            self.left_locked = False
            self.locked_left_page = 1
            self.restore_left_view = False
            self.restore_right_view = False
            self.search_highlights = {}
            self.current_search_term = ""
            # =======================================================
            self.load_config()
            self.load_pdf_toc()
            self.refresh_bookmark_panel()
            self.render_facing()
            QTimer.singleShot(0, self.apply_initial_view)
            self.right_pane.setFocus()
            self.update_status()
            self.update_ui_text()

            self.statusBar().showMessage(
                self.tr("Notebook imported from: {}").format(
                    os.path.basename(notebook_path)
                ),
                3000,
            )
            self.add_to_recent_files(notebook_path)
        except Exception as e:
            QMessageBox.critical(
                self, self.tr("Error"), f"{self.tr('Failed to import notebook')}: {e}"
            )
        self.update_document_tabs()
        self.epub_relayout_action.setVisible(False)

    def load_pdf_toc(self):
        """加载 PDF 内置书签（目录）并构建扁平列表"""
        if not self.doc:
            self.pdf_toc = []
            return
        try:
            raw_toc = self.doc.get_toc()
            self.pdf_toc = [
                (lvl, title, max(1, min(int(page), self.total_pages)))
                for lvl, title, page in raw_toc
                if isinstance(page, (int, float)) and page > 0
            ]
        except Exception as e:
            print(f"Failed to load TOC: {e}")
            self.pdf_toc = []

    def open_toc_dialog(self):
        """打开 PDF 目录导航对话框"""
        if not self.pdf_toc:
            return
        try:
            colors = getattr(self, '_theme_colors', None)
            dialog = TocDialog(
                self.pdf_toc,
                parent=self,
                theme_name=getattr(self, 'current_theme', 'light'),
                colors=colors,
                bookmarks=getattr(self, 'bookmarks', {}),
            )
            dialog.nodeSelected.connect(self.jump_to_page)
            if dialog.exec_() == QDialog.Accepted:
                # Save state
                self.toc_state = dialog.get_state()
                self.save_config()
        except Exception as e:
            import traceback
            QMessageBox.critical(self, "错误", f"打开目录失败:\n{traceback.format_exc()}")

    def set_text_annotation_font_size(self):
        """设置文字批注的字体大小（pt）"""
        current_size = getattr(self, 'text_annotation_font_size', 25)
        size_str, ok = QInputDialog.getText(
            self,
            self.tr("Set Text Font Size..."),
            self.tr("Text font size (pt):"),
            text=str(current_size),
        )
        if not ok:
            return
        try:
            new_size = float(size_str)
            if new_size <= 0 or new_size > 200:
                raise ValueError("out of range")
        except ValueError:
            QMessageBox.warning(self, self.tr("Error"), self.tr("Invalid font size."))
            return

        self.text_annotation_font_size = new_size
        # 同步更新左右窗格
        if hasattr(self, 'left_pane'):
            self.left_pane.font_size = new_size
        if hasattr(self, 'right_pane'):
            self.right_pane.font_size = new_size

    def _on_reading_pane_focused(self, is_left):
        """
        当左或右阅读窗格获得焦点时调用。
        :param is_left: True 表示左窗格获得焦点，False 表示右窗格。
        """
        self.last_focused_pane_is_left = is_left

    def search_text_with_highlight(self, search_term, case_sensitive=False):
        """执行搜索并高亮结果"""
        if not self.doc or not search_term:
            return []

        results = []
        self.search_highlights = {}  # 清空之前的高亮

        # 搜索所有页面
        for page_num in range(len(self.doc)):
            page = self.doc[page_num]
            try:
                # 获取页面文本
                text = page.get_text()
                search_text = search_term if case_sensitive else search_term.lower()
                page_text = text if case_sensitive else text.lower()

                # 查找所有匹配
                indices = []
                start = 0
                while True:
                    idx = page_text.find(search_text, start)
                    if idx == -1:
                        break
                    indices.append(idx)
                    start = idx + 1

                # 为每个匹配查找位置
                for idx in indices:
                    # 获取匹配文本的位置
                    match_text = text[idx : idx + len(search_term)]
                    # 使用 search_for 查找精确位置
                    match_rects = page.search_for(match_text)
                    for rect in match_rects:
                        # === 修复：将 PDF 坐标转换为 pixmap 坐标（因渲染时用了 Matrix(2.0, 2.0)）===
                        RENDER_SCALE = 2.0  # 必须与 render_page 中的 Matrix 缩放一致
                        highlight_rect = [
                            rect.x0 * RENDER_SCALE,
                            rect.y0 * RENDER_SCALE,
                            rect.width * RENDER_SCALE,
                            rect.height * RENDER_SCALE,
                        ]
                        # ==================================================================

                        if page_num + 1 not in self.search_highlights:
                            self.search_highlights[page_num + 1] = []
                        self.search_highlights[page_num + 1].append(
                            {
                                "rect": highlight_rect,
                                "color": self.search_highlight_color,
                            }
                        )
                        # ===========================================
                        # 添加到结果列表
                        context_start = max(0, idx - 40)
                        context_end = min(len(text), idx + len(search_term) + 40)
                        context = text[context_start:context_end]
                        results.append(
                            {
                                "page": page_num + 1,
                                "context": context.strip(),
                                "position": idx,
                            }
                        )
            except Exception as e:
                print(f"Error searching page {page_num}: {e}")

        # 更新当前搜索词
        self.current_search_term = search_term
        # 应用高亮到当前显示的页面
        self.apply_search_highlights()
        return results

    def apply_search_highlights(self):
        """应用搜索高亮到当前页面"""
        # 更新左窗格高亮
        if self.left_pane.page_num in self.search_highlights:
            self.left_pane.set_search_highlights(
                self.search_highlights[self.left_pane.page_num],
                self.current_search_term,
            )
        else:
            self.left_pane.set_search_highlights([])

        # 更新右窗格高亮
        if self.right_pane.page_num in self.search_highlights:
            self.right_pane.set_search_highlights(
                self.search_highlights[self.right_pane.page_num],
                self.current_search_term,
            )
        else:
            self.right_pane.set_search_highlights([])

    def clear_search_highlights(self):
        """清除所有搜索高亮"""
        self.search_highlights = {}
        self.current_search_term = ""
        self.left_pane.set_search_highlights([])
        self.right_pane.set_search_highlights([])
        self.update_status()

    def tr(self, text, **kwargs):
        """翻译界面文本。text 是英文原文作为 key"""
        trans_dict = self.translations.get(self.current_lang, self.translations["en"])
        translated = trans_dict.get(text, text)
        if kwargs:
            translated = translated.format(**kwargs)
        return translated

    def set_language(self, lang):
        if lang in ("en", "zh"):
            self.current_lang = lang

            # === 修复：先加载现有全局配置，再更新语言 ===
            global_data = {}
            if os.path.exists(GLOBAL_CONFIG_FILE):
                try:
                    with open(GLOBAL_CONFIG_FILE, "r") as f:
                        global_data = json.load(f)
                except Exception as e:
                    print(f"Failed to load global config: {e}")

            # 更新语言，保留其他字段（如 recent_files）
            global_config = global_data.get("global_config", {})
            global_config["language"] = self.current_lang
            global_data["global_config"] = global_config
            # ==========================================

            try:
                with open(GLOBAL_CONFIG_FILE, "w") as f:
                    json.dump(global_data, f, indent=2)
            except Exception as e:
                print(f"Failed to save global config: {e}")

            self.save_config()
            self.update_ui_text()
            QMessageBox.information(
                self,
                self.tr("Language Changed"),
                self.tr("Please restart TactiReader to apply the new language."),
            )

    def apply_theme(self, theme_name):
        """应用颜色主题到整个应用界面"""
        if theme_name not in THEMES:
            theme_name = 'light'

        self.current_theme = theme_name
        W_hex, B_hex = THEMES[theme_name]
        colors = {key: transform_color(value, W_hex, B_hex) for key, value in THEME_PALETTE.items()}

        # 1. 主窗口背景
        self.setStyleSheet(f"QMainWindow {{ background-color: {colors['bg']}; }}")

        # 2. 菜单栏样式
        self.menuBar().setStyleSheet(f"""
            QMenuBar {{
                background-color: {colors['menu_bg']};
                color: {colors['menu_fg']};
                border-bottom: 1px solid {colors['border']};
                font-family: "Microsoft YaHei", "Consolas", sans-serif;
                font-size: 10pt;
                font-weight: 450;
            }}
            QMenuBar::item:selected {{
                background-color: {colors['highlight']};
                color: {colors['button_fg']};
            }}
            QMenuBar::item:pressed {{
                background-color: {colors['highlight']};
                color: {colors['button_fg']};
            }}
            QMenu {{
                background-color: {colors['menu_bg']};
                color: {colors['menu_fg']};
                border: 1px solid {colors['border']};
            }}
            QMenu::item:selected {{
                background-color: {colors['highlight']};
                color: {colors['button_fg']};
            }}
            QMenu::item:checked {{
                background-color: {colors['highlight']};
                font-weight: bold;
            }}
            QMenu::indicator {{
                width: 14px;
                height: 14px;
            }}
            QMenu::indicator:checked {{
                image: none;
                border: 2px solid {colors['highlight']};
                background: {colors['menu_bg']};
                border-radius: 2px;
            }}
            QMenu::separator {{
                background-color: {colors['border']};
                height: 1px;
                margin: 4px 0px;
            }}
        """)

        # 3. 通用控件样式表
        self._theme_colors = colors
        style = f"""
            QWidget {{
                background-color: {colors['bg']};
                color: {colors['fg']};
            }}
            QPushButton {{
                background-color: {colors['button_bg']};
                color: {colors['button_fg']};
                border: 1px solid {colors['border']};
                border-radius: 3px;
                padding: 4px 10px;
            }}
            QPushButton:hover {{
                background-color: {colors['highlight']};
            }}
            QLineEdit, QTextEdit, QComboBox {{
                background-color: {colors['entry_bg']};
                color: {colors['entry_fg']};
                border: 1px solid {colors['border']};
            }}
            QLabel {{
                background-color: {colors['label_bg']};
                color: {colors['label_fg']};
            }}
            QFrame {{
                background-color: {colors['bg']};
                border: 1px solid {colors['border']};
            }}
            QScrollArea {{
                background-color: {colors['bg']};
                border: none;
            }}
            QSplitter::handle {{
                background-color: {colors['border']};
            }}
            QListWidget {{
                background-color: {colors['entry_bg']};
                color: {colors['entry_fg']};
                border: 1px solid {colors['border']};
            }}
            QToolBar {{
                background-color: {colors['bg']};
                border: 1px solid {colors['border']};
            }}
            TacticalPane {{
                background-color: {colors['bg']};
                color: {colors['fg']};
                border: 1px solid {colors['border']};
            }}
        """
        self.setStyleSheet(style)

        # 4. 更新菜单勾选状态
        for name, act in self._theme_actions.items():
            act.setChecked(name == theme_name)

        # 5. 更新状态栏样式
        self.statusBar().setStyleSheet(f"""
            QStatusBar {{
                background-color: {colors['bg']};
                color: {colors['fg']};
                border-top: 1px solid {colors['border']};
                font-weight: 480;
            }}
        """)
        self.color_status_label.setStyleSheet(f"font-weight: 500; color: {colors['fg']};")

        # 6. 刷新阅读窗格（让背景色立即生效）
        if hasattr(self, 'left_pane'):
            self.left_pane.update()
        if hasattr(self, 'right_pane'):
            self.right_pane.update()

        # 7. 清空页面缓存并重新渲染当前页面以应用新的主题色
        self._theme_page_cache.clear()
        if getattr(self, 'doc', None):
            self.render_facing()

        # 8. 保存主题配置
        try:
            global_config = self.config_manager.load_global_config()
            global_config["theme"] = theme_name
            self.config_manager.save_global_config(global_config)
        except Exception as e:
            print(f"Failed to save theme config: {e}")

    def update_ui_text(self):
        # 更新窗口标题
        if self.notebook_source_path:
            # 笔记本模式：显示 .tactinote 文件名
            self.setWindowTitle(
                f"{self.tr('TactiReader')} - {os.path.basename(self.notebook_source_path)}"
            )
        elif hasattr(self, "pdf_path") and self.pdf_path:
            # 普通PDF模式
            self.setWindowTitle(
                f"{self.tr('TactiReader')} - {os.path.basename(self.pdf_path)}"
            )
        else:
            self.setWindowTitle(self.tr("TactiReader"))
        # 更新书签面板（会刷新 <no bookmarks>）
        self.refresh_bookmark_panel()
        # 更新菜单栏文本
        self.update_menu_texts()

    def update_menu_texts(self):
        """更新菜单栏文本以反映当前语言"""
        # 注意：PyQt 的菜单系统不直接暴露菜单项以便重置文本，
        # 所以理想情况下应在创建时动态翻译。
        # 这个方法是为了展示目的，实际应用中可能需要重建菜单。
        pass

    def open_pdf_dialog(self):
        file_path, _ = QFileDialog.getOpenFileName(
            self,
            self.tr("Open PDF, EPUB or Notebook"),
            "",
            self.tr("PDF/EPUB Files (*.pdf *.epub);;PDF Files (*.pdf);;EPUB Files (*.epub);;TactiReader Notebook (*.tactinote);;All Files (*)"),
        )
        if file_path:
            abs_file_path = os.path.abspath(file_path)

            # 如果已在打开列表中，切换到对应文档（会触发已有保存逻辑）
            for i, path in enumerate(self.open_documents):
                if os.path.abspath(path) == abs_file_path:
                    self._switch_to_document(i)
                    return

            # === 关键修复：在加载新文档前，保存当前 .tactinote ===
            if getattr(self, "notebook_source_path", None) is not None:
                try:
                    self.save_config()
                    self._flush_notebook_to_source()
                except Exception as e:
                    print(
                        f"[WARN] Failed to save current .tactinote before opening new file: {e}"
                    )
            # ===================================================

            # 添加到文档列表
            self.open_documents.append(abs_file_path)
            self.save_global_config()

            # 更新标签栏
            self.update_document_tabs()

            # 加载新文档
            ext = os.path.splitext(file_path)[1].lower()
            if ext == ".tactinote":
                self.import_notebook_from_path(file_path)
            elif ext == ".epub":
                self.load_epub(file_path)
            else:
                self.load_pdf(file_path)

    # === NEW CODE START ===
    def add_to_recent_files(self, file_path):
        """将文件加入最近列表（去重+置顶），支持 .pdf 和 .tactinote"""
        if not os.path.isfile(file_path):
            return

        # === 移除扩展名检查，让 .tactinote 也能加入 ===
        # if not file_path.lower().endswith('.pdf'):
        #     return
        # =======================================

        if file_path in self.recent_files:
            self.recent_files.remove(file_path)
        self.recent_files.insert(0, file_path)
        self.recent_files = self.recent_files[:5]  # 只保留5个
        self.save_global_config()
        self.update_recent_files_menu()

    def update_recent_files_menu(self):
        """刷新“最近文件”子菜单"""
        self.recent_menu.clear()
        if self.recent_files:
            for fp in self.recent_files:
                action = QAction(os.path.basename(fp), self)
                action.setToolTip(fp)
                # === 修改：根据文件扩展名决定打开方式 ===
                if fp.lower().endswith(".tactinote"):
                    action.triggered.connect(
                        lambda checked, path=fp: self.import_notebook_from_path(path)
                    )
                elif fp.lower().endswith(".epub"):
                    action.triggered.connect(
                        lambda checked, path=fp: self.load_epub(path)
                    )
                else:
                    action.triggered.connect(
                        lambda checked, path=fp: self.load_pdf(path)
                    )
                # =======================================
                self.recent_menu.addAction(action)
        else:
            empty_action = QAction(self.tr("<No recent files>"), self)
            empty_action.setEnabled(False)
            self.recent_menu.addAction(empty_action)

    # === NEW CODE END ===

    def calibrate_page_number_offset(self):
        """Ctrl+G: 标定当前物理页对应的逻辑页码"""
        if not self.doc:
            return

        # 获取当前焦点窗格的物理页码
        is_left = self.last_focused_pane_is_left and not self.single_page_mode
        if is_left:
            current_physical = self.left_pane.page_num
        else:
            current_physical = self.right_pane.page_num

        if current_physical < 1:
            return

        # 计算当前逻辑页（用于默认值）
        current_logical = current_physical + self.page_number_offset

        # 弹出对话框
        logical_page, ok = QInputDialog.getInt(
            self,
            self.tr("Page Number Calibration"),
            self.tr("Enter logical page number for physical page {physical}:").format(
                physical=current_physical
            ),
            value=current_logical,
            min=1,
            max=99999,
        )
        if ok:
            # 更新偏移量：logical = physical + offset → offset = logical - physical
            self.page_number_offset = logical_page - current_physical
            self.save_config()
            self.statusBar().showMessage(
                self.tr("🔢 Page calibration: logical = physical + {offset}").format(
                    offset=self.page_number_offset
                ),
                2000,
            )

    def clear_page_number_offset(self):
        """Ctrl+Shift+G: 清除页码偏移"""
        self.page_number_offset = 0
        self.save_config()
        self.statusBar().showMessage(self.tr("🧹 Page number offset cleared"), 2000)

    # === 新增：辅助方法，用于菜单项触发快捷键 ===
    def _trigger_shortcut(self, key, modifiers=Qt.NoModifier):
        """
        模拟触发一个键盘快捷键事件。
        这样菜单项可以直接复用现有的 keyPressEvent 逻辑，无需重复代码。
        """
        event = QKeyEvent(QEvent.KeyPress, key, modifiers)
        self.keyPressEvent(event)

    # ===========================================
    def load_pdf(self, pdf_path):
        """加载 PDF（增强版）"""
        abs_path = os.path.abspath(pdf_path)

        # 添加到文档列表（如果不存在）
        if abs_path not in self.open_documents:
            self.open_documents.append(abs_path)
            self.save_global_config()

        # 检查是否已经是当前文档
        current_abs = os.path.abspath(self.pdf_path) if self.pdf_path else None
        if current_abs == abs_path:
            # 已经是当前文档，只更新 UI
            self.update_document_tabs()
            return
        self.add_to_recent_files(pdf_path)
        # === 原有加载逻辑 ===
        if self.pdf_path:
            self.save_config()

        if self.doc:
            self.doc.close()

        try:
            self.doc = fitz.open(pdf_path)
            self.pdf_path = pdf_path
            self.is_epub = False
            self.epub_layout_params = None
            self._epub_chapter_map = {}
            self._epub_images_src = []
            self._epub_footnotes_src = []
            self.total_pages = len(self.doc)

            # === 清空页面缓存，避免旧文档页面残留 ===
            self._theme_page_cache.clear()
            # ======================================

            self.config_file = get_config_path(pdf_path)
            # === 关键修复：重置所有全局状态变量（包括 notebook 状态）
            self.notebook_source_path = None
            self.annotations = {}
            self.bookmarks = {}
            self.page_rotations = {}
            self.page_number_offset = 0
            self.home_page = 1
            self.flip_multiplier = 2
            self.single_page_mode = False
            self.right_page = 1
            self.left_locked = False
            self.locked_left_page = 1
            self.restore_left_view = False
            self.restore_right_view = False
            self.search_highlights = {}
            self.current_search_term = ""
            # =======================================
            self.load_config()

            self.load_pdf_toc()
            self.refresh_bookmark_panel()
            self.render_facing()
            QTimer.singleShot(0, self.apply_initial_view)
            self.right_pane.setFocus()
            self.update_status()

            # 更新标签栏（现在 self.pdf_path 已更新）
            self.update_document_tabs()
            self.epub_relayout_action.setVisible(False)
            self.save_as_pdf_action.setEnabled(True)
            self.export_notebook_action.setEnabled(True)

        except Exception as e:
            QMessageBox.critical(
                self,
                self.tr("Error"),
                self.tr("Failed to open PDF:\n{}").format(str(e)),
            )
            if abs_path in self.open_documents:
                self.open_documents.remove(abs_path)
                self.save_global_config()
                self.update_document_tabs()

    def _build_epub_css(self, params):
        return _build_apply_css(params)

    def _load_epub_config(self, config_path):
        try:
            if not os.path.isfile(config_path):
                return None
            with open(config_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            return data.get("epub_layout", None)
        except Exception as e:
            print(f"Load EPUB config error: {e}")
            return None

    def _save_epub_config(self, config_path, params):
        try:
            data = {}
            if os.path.isfile(config_path):
                with open(config_path, "r", encoding="utf-8") as f:
                    data = json.load(f)
            data["epub_layout"] = params
            with open(config_path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            print(f"Save EPUB config error: {e}")

    def _apply_epub_layout(self, params):
        if not self.is_epub or not self.pdf_path:
            return
        try:
            if self.doc:
                self.doc.close()
                self.doc = None

            fontsize = params.get("fontsize", 25)

            if not hasattr(self, '_epub_raw_cache') or self._epub_raw_cache_path != self.pdf_path:
                with open(self.pdf_path, "rb") as f:
                    self._epub_raw_cache = f.read()
                self._epub_raw_cache_path = self.pdf_path

            saved_w = params.get("page_width", None)
            saved_h = params.get("page_height", None)
            if saved_w is not None and saved_h is not None and saved_w > 0 and saved_h > 0:
                page_w_pt = saved_w
                page_h_pt = saved_h
            else:
                page_width_pct = params.get("page_width_pct", 45)
                screen = self.screen()
                if screen:
                    screen_geom = screen.geometry()
                    screen_w = screen_geom.width()
                    screen_h = screen_geom.height()
                else:
                    screen_w = 1920
                    screen_h = 1080
                page_w_px = int(screen_w * page_width_pct / 100)
                page_h_px = screen_h
                pt_per_px = 72.0 / 96.0
                page_w_pt = page_w_px * pt_per_px
                page_h_pt = page_h_px * pt_per_px

            css = _build_apply_css(params)
            # PyMuPDF的apply_css()对EPUB无效，直接修改EPUB内部CSS
            modified_bytes, _ = _modify_epub_css_in_memory(self._epub_raw_cache, css)
            self.doc = fitz.open(stream=modified_bytes, filetype="epub")

            self.doc.layout(fontsize=fontsize, width=page_w_pt, height=page_h_pt)
            self.total_pages = len(self.doc)
        except Exception as e:
            import traceback
            traceback.print_exc()
            print(f"EPUB layout error: {e}")

    def _epub_relayout_settings(self):
        if not self.is_epub or not self.pdf_path:
            return
        reply = QMessageBox.warning(
            self,
            self.tr("EPUB 排版设置"),
            self.tr("重新进入排版设置将丢弃当前书籍的所有批注和书签，是否继续？"),
            QMessageBox.Yes | QMessageBox.No,
            QMessageBox.No,
        )
        if reply != QMessageBox.Yes:
            return
        epub_path = self.pdf_path
        self.load_epub(epub_path, force_preview=True)

    def load_epub(self, epub_path, force_preview=False):
        abs_path = os.path.abspath(epub_path)
        if abs_path not in self.open_documents:
            self.open_documents.append(abs_path)
            self.save_global_config()

        current_abs = os.path.abspath(self.pdf_path) if self.pdf_path else None
        if current_abs == abs_path and not force_preview:
            self.update_document_tabs()
            return
        self.add_to_recent_files(epub_path)

        if self.pdf_path:
            self.save_config()
        if self.doc:
            self.doc.close()

        try:
            doc = fitz.open(epub_path)
            if not doc.is_reflowable:
                QMessageBox.warning(self, "Warning", "This file is not a reflowable EPUB.")
                doc.close()
                if abs_path in self.open_documents:
                    self.open_documents.remove(abs_path)
                    self.save_global_config()
                    self.update_document_tabs()
                return
            doc.close()
            doc = None

            self.config_file = get_config_path(epub_path)
            saved_params = self._load_epub_config(self.config_file)

            if saved_params is None or force_preview:
                init_p = saved_params if force_preview and saved_params else None
                if force_preview and self.epub_layout_params:
                    init_p = self.epub_layout_params
                dlg = EpubPreviewDialog(epub_path, init_p, self)
                result = dlg.exec_()
                if result != QDialog.Accepted or dlg.result_params is None:
                    if abs_path in self.open_documents:
                        self.open_documents.remove(abs_path)
                        self.save_global_config()
                        self.update_document_tabs()
                    if len(self.open_documents) > 0:
                        self._switch_to_document(len(self.open_documents) - 1)
                    return
                saved_params = dlg.result_params
                self._save_epub_config(self.config_file, saved_params)

            self.pdf_path = epub_path
            self.is_epub = True
            self.epub_layout_params = saved_params
            self.doc = None

            self._theme_page_cache.clear()

            self.notebook_source_path = None
            self.annotations = {}
            self.bookmarks = {}
            self.page_rotations = {}
            self.page_number_offset = 0
            self.home_page = 1
            self.flip_multiplier = 2
            self.single_page_mode = False
            self.right_page = 1
            self.left_locked = False
            self.locked_left_page = 1
            self.restore_left_view = False
            self.restore_right_view = False
            self.search_highlights = {}
            self.current_search_term = ""

            self.default_fit_mode = "fit_page"
            self._apply_epub_layout(saved_params)
            self.total_pages = len(self.doc)

            # 预计算页码→HTML源文件映射 & 缓存图片/脚注
            self._epub_chapter_map = _build_page_to_chapter_map(self.pdf_path, self.doc)
            self._epub_images_src, self._epub_footnotes_src = _parse_epub_html_source(self.pdf_path)

            self.load_config()
            if self.is_epub:
                self.default_fit_mode = "fit_page"
                self._build_fit_menu()
            self.load_pdf_toc()
            self.refresh_bookmark_panel()
            self.render_facing()
            QTimer.singleShot(0, self.apply_initial_view)
            self.right_pane.setFocus()
            self.update_status()
            self.update_document_tabs()
            self.epub_relayout_action.setVisible(True)
            self.save_as_pdf_action.setEnabled(False)
            self.export_notebook_action.setEnabled(False)

        except Exception as e:
            QMessageBox.critical(
                self,
                self.tr("Error"),
                self.tr("Failed to open EPUB:\n{}").format(str(e)),
            )
            if abs_path in self.open_documents:
                self.open_documents.remove(abs_path)
                self.save_global_config()
                self.update_document_tabs()

    def load_config(self):
        try:
            data = self.config_manager.load_document_config(self.config_file)
            if not data:
                return

            config = data.get("config", {})
            self.flip_multiplier = config.get("multiplier", 2)
            self.home_page = max(1, min(config.get("home_page", 1), self.total_pages))
            self.right_page = max(1, min(config.get("last_page", 1), self.total_pages))
            self.single_page_mode = config.get("single_page_mode", False)

            self.left_locked = config.get("left_locked", False)
            self.locked_left_page = max(
                1, min(config.get("locked_left_page", 1), self.total_pages)
            )
            self.bookmark_panel_visible = config.get("bookmark_panel_visible", False)
            self.bookmark_panel.setVisible(self.bookmark_panel_visible)
            self.default_fit_mode = config.get("default_fit_mode", "fit_page")
            self._build_fit_menu()
            if "splitter_sizes" in config:
                sizes = config["splitter_sizes"]
                if len(sizes) == 2 and all(
                    isinstance(x, int) and x >= 0 for x in sizes
                ):
                    self.splitter.setSizes(sizes)

            self.current_pen_color_index = config.get("pen_color_index", 0)
            self.current_rect_color_index = config.get("rect_color_index", 0)
            self.current_text_color_index = config.get("text_color_index", 0)
            self.update_pane_colors()

            if "page_rotations" in data:
                self.page_rotations = data["page_rotations"]
            if "annotations" in data:
                self.annotations = data["annotations"]
            self.page_number_offset = data.get("page_number_offset", 0)

            if "global_left_scale" in data:
                self.left_pane.scale_factor = data["global_left_scale"]
                self.restore_left_view = True
            if "global_left_offset" in data:
                offset = data["global_left_offset"]
                self.left_pane.offset = QPointF(offset[0], offset[1])
                self.restore_left_view = True
            if "global_left_rotation" in data:
                self.left_pane.rotation = data["global_left_rotation"]
                self.restore_left_view = True
            if "global_right_scale" in data:
                self.right_pane.scale_factor = data["global_right_scale"]
                self.restore_right_view = True
            if "global_right_offset" in data:
                offset = data["global_right_offset"]
                self.right_pane.offset = QPointF(offset[0], offset[1])
                self.restore_right_view = True
            if "global_right_rotation" in data:
                self.right_pane.rotation = data["global_right_rotation"]
                self.restore_right_view = True

            # Restore TOC dialog state
            if "toc_max_depth" in data and "toc_selected_id" in data:
                self.toc_state = (data["toc_max_depth"], data["toc_selected_id"])

            bookmarks = {}
            for k, v in data.items():
                if k != "config" and k != "annotations" and k != "page_rotations":
                    if isinstance(v, dict):
                        bookmarks[k] = v
                    else:
                        bookmarks[k] = {"page": v, "name": ""}
            self.bookmarks = bookmarks
        except Exception as e:
            print(f"Config load error: {e}")

    def save_config(self):
        if not self.config_file:
            return
        data = self.bookmarks.copy()
        data["config"] = {
            "multiplier": self.flip_multiplier,
            "home_page": self.home_page,
            "last_page": self.right_page,
            "single_page_mode": self.single_page_mode,
            "left_locked": self.left_locked,
            "locked_left_page": self.locked_left_page,
            "pen_color_index": self.current_pen_color_index,
            "rect_color_index": self.current_rect_color_index,
            "text_color_index": self.current_text_color_index,
            # === 新增：书签面板状态 ===
            "bookmark_panel_visible": self.bookmark_panel_visible,
            "splitter_sizes": self.splitter.sizes(),
            "default_fit_mode": self.default_fit_mode,
        }
        data["page_rotations"] = self.page_rotations
        data["annotations"] = self.annotations
        data["page_number_offset"] = self.page_number_offset
        # === 保存全局视图状态（缩放/平移/旋转）===
        data["global_left_scale"] = self.left_pane.scale_factor
        data["global_left_offset"] = [
            self.left_pane.offset.x(),
            self.left_pane.offset.y(),
        ]
        data["global_left_rotation"] = self.left_pane.rotation

        data["global_right_scale"] = self.right_pane.scale_factor
        data["global_right_offset"] = [
            self.right_pane.offset.x(),
            self.right_pane.offset.y(),
        ]
        data["global_right_rotation"] = self.right_pane.rotation
        # =========================================
        # === TOC dialog state ===
        data["toc_max_depth"] = self.toc_state[0]
        data["toc_selected_id"] = self.toc_state[1]
        # =========================================
        try:
            self.config_manager.save_document_config(
                self.config_file,
                data,
                serializer=self.serialize_annotations,
            )

        except Exception as e:
            print(f"Save config failed: {e}")

    def apply_initial_view(self):
        if not self.restore_right_view and self.right_pane.original_pixmap:
            self.right_pane.reset_view()
        if (
            not self.single_page_mode
            and not self.restore_left_view
            and self.left_pane.original_pixmap
        ):
            self.left_pane.reset_view()

    # === NEW CODE START ===
    def save_global_config(self):
        """保存全局配置（包括已打开文档）"""
        try:
            global_config = self.config_manager.load_global_config()

            # 更新最近文件（保持原有逻辑）
            recent_files_clean = [f for f in self.recent_files if os.path.isfile(f)]
            global_config["recent_files"] = recent_files_clean[-10:]  # 保留最近10个

            # 新增：保存已打开文档
            # 保存已打开文档（支持 .pdf、.epub 和 .tactinote）
            open_docs_clean = [
                f
                for f in self.open_documents
                if os.path.isfile(f)
                and (f.lower().endswith(".pdf") or f.lower().endswith(".epub") or f.lower().endswith(".tactinote"))
            ]
            global_config["open_documents"] = open_docs_clean[-10:]  # 保留最近10个

            # 保存当前阅读的文档
            if self.pdf_path and os.path.isfile(self.pdf_path):
                global_config["current_document"] = os.path.abspath(self.pdf_path)
            else:
                global_config["current_document"] = ""

            # 保存语言设置
            global_config["language"] = self.current_lang

            self.config_manager.save_global_config(global_config)

        except Exception as e:
            print(f"Failed to save global config: {e}")

    def update_document_tabs(self):
        """更新菜单形式换书/删书（替代顶部标签栏）"""
        self._refresh_book_menus()

    # --- 默认大小菜单 ---
    def _build_fit_menu(self):
        """构建"默认大小"子菜单"""
        self.fit_menu.clear()
        self._fit_actions.clear()

        labels = {
            "actual_size": "实际大小",
            "fit_width": "适合宽度",
            "fit_page": "适合页面",
        }
        for mode, label in labels.items():
            act = QAction(label, self)
            act.setCheckable(True)
            act.setChecked(self.default_fit_mode == mode)
            act.triggered.connect(lambda _, m=mode: self._set_fit_mode(m))
            self.fit_menu.addAction(act)
            self._fit_actions[mode] = act

    def _set_fit_mode(self, mode):
        """设置默认缩放模式并更新菜单勾选"""
        self.default_fit_mode = mode
        for m, act in self._fit_actions.items():
            act.setChecked(m == mode)
        self.save_config()

    def _refresh_book_menus(self):
        """重建换书/删书菜单项"""
        # 清理旧菜单项
        for act in self._book_menu_actions:
            self.switch_book_menu.removeAction(act)
            self.close_book_menu.removeAction(act)
        self._book_menu_actions.clear()

        for idx, path in enumerate(self.open_documents):
            name = os.path.basename(path)
            current_abs = os.path.abspath(self.pdf_path) if self.pdf_path else ""
            is_active = os.path.abspath(path) == current_abs

            # 换书菜单：当前文档用 ✓
            switch_prefix = "✓ " if is_active else "  "
            # 删书菜单：当前文档用 ■
            close_prefix = "■ " if is_active else "  "

            # 换书菜单项
            sw = QAction(switch_prefix + name, self)
            sw.triggered.connect(lambda _, i=idx: self._switch_to_document(i))
            self.switch_book_menu.addAction(sw)

            # 删书菜单项
            cl = QAction(close_prefix + name, self)
            cl.triggered.connect(lambda _, i=idx: self._close_document(i))
            self.close_book_menu.addAction(cl)

            self._book_menu_actions.extend([sw, cl])

    def _switch_to_document(self, index):
        """切换到指定文档（菜单形式的换书）"""
        if not (0 <= index < len(self.open_documents)):
            return

        # 保存当前 notebook 状态
        if getattr(self, "notebook_source_path", None) is not None:
            self.save_config()
            self._flush_notebook_to_source()

        file_path = self.open_documents[index]
        current_path = self.pdf_path or ""

        if os.path.abspath(file_path) != os.path.abspath(current_path):
            if file_path.lower().endswith(".tactinote"):
                self.import_notebook_from_path(file_path)
            else:
                self.load_pdf(file_path)

        self.update_ui_text()

    def _close_document(self, index):
        """关闭指定文档（菜单形式的删书）"""
        if not self.open_documents or index >= len(self.open_documents):
            return

        closed_path = self.open_documents.pop(index)
        self.save_global_config()

        if self.open_documents:
            new_index = min(index, len(self.open_documents) - 1)
            new_path = self.open_documents[new_index]

            if self.doc is not None:
                self.doc.close()
                self.doc = None
            self.pdf_path = None
            self.notebook_source_path = None
            self.config_file = None

            if new_path.lower().endswith(".tactinote"):
                self.import_notebook_from_path(new_path)
            elif new_path.lower().endswith(".epub"):
                self.load_epub(new_path)
            else:
                self.load_pdf(new_path)
        else:
            if self.doc is not None:
                self.doc.close()
                self.doc = None
            self.pdf_path = None
            self.notebook_source_path = None
            self.config_file = None
            self.total_pages = 0

            self.left_pane.set_page(None, -1)
            self.right_pane.set_page(None, -1)
            self.refresh_bookmark_panel()
            self.update_status()
            self.update_ui_text()

    def open_in_new_window(self, pdf_path):
        """在新窗口中打开文档"""
        script_path = sys.argv[0]
        subprocess.Popen([sys.executable, script_path, pdf_path])

    def serialize_annotations(self, obj):
        return serialize_annotations(obj)

    def render_page(self, page_num, apply_theme=True):
        """渲染单页，可选是否应用主题变换"""
        if page_num < 0 or page_num >= self.total_pages:
            return QPixmap()

        # 缓存键：页码 + 主题
        cache_key = (page_num, getattr(self, 'current_theme', 'light'))
        if cache_key in self._theme_page_cache:
            return self._theme_page_cache[cache_key]

        try:
            page = self.doc[page_num]
            is_epub = getattr(self, 'is_epub', False)
            # 渲染倍率：PDF 保持 2.0（保证清晰度），EPUB 用 1.5
            mat = fitz.Matrix(1.5, 1.5) if is_epub else fitz.Matrix(2.0, 2.0)
            pix = page.get_pixmap(matrix=mat)
            stride = pix.stride if pix.stride is not None else pix.width * 3
            img_format = QImage.Format_RGBA8888 if pix.alpha else QImage.Format_RGB888
            qt_img = QImage(pix.samples, pix.width, pix.height, stride, img_format)
            pixmap = QPixmap.fromImage(qt_img)

            # 非浅色主题下，对页面像素应用主题映射
            if apply_theme and getattr(self, 'current_theme', 'light') != 'light':
                W_hex, B_hex = THEMES[self.current_theme]
                theme = self.current_theme
                if theme == 'night':
                    pixmap = transform_pixmap(pixmap, W_hex, B_hex, grayscale='night')
                elif theme == 'eink':
                    pixmap = transform_pixmap(pixmap, W_hex, B_hex, grayscale='eink')
                elif theme == 'invert':
                    pixmap = transform_pixmap(pixmap, W_hex, B_hex, invert=True)
                else:
                    pixmap = transform_pixmap(pixmap, W_hex, B_hex)

            # 限制缓存大小，避免内存无限增长（EPUB缓存更大，页数多）
            cache_limit = 40 if is_epub else 20
            if len(self._theme_page_cache) >= cache_limit:
                self._theme_page_cache.pop(next(iter(self._theme_page_cache)))
            self._theme_page_cache[cache_key] = pixmap

            return pixmap
        except Exception as e:
            print(f"Render error: {e}")
            return QPixmap()

    def _pre_render_pages(self, current_page):
        """异步预渲染当前页附近的页面（使用独立文档句柄保证线程安全）"""
        if not self.pdf_path or not self.doc:
            return
        pages_to_render = []
        for offset in range(-3, 4):
            page_num = current_page + offset
            if 0 <= page_num < self.total_pages:
                cache_key = (page_num, getattr(self, 'current_theme', 'light'))
                if cache_key not in self._theme_page_cache:
                    pages_to_render.append(page_num)
        if not pages_to_render:
            return

        # 用独立文档句柄在后台渲染，只返回 QImage（线程安全），QPixmap 转换在主线程
        file_path = self.pdf_path
        is_epub = getattr(self, 'is_epub', False)
        theme = getattr(self, 'current_theme', 'light')
        W_hex, B_hex = THEMES.get(theme, ('#FFFFFF', '#000000'))
        # 统一使用 2.0x 倍率，与主渲染一致
        scale = 2.0 if not is_epub else 1.5

        def _render_one(page_num):
            try:
                doc = fitz.open(file_path)
                page = doc[page_num]
                pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale))
                stride = pix.stride if pix.stride is not None else pix.width * 3
                img_format = QImage.Format_RGBA8888 if pix.alpha else QImage.Format_RGB888
                qt_img = QImage(pix.samples, pix.width, pix.height, stride, img_format).copy()
                doc.close()
                # 应用主题变换
                if theme != 'light':
                    temp_pixmap = QPixmap.fromImage(qt_img)
                    if theme == 'night':
                        temp_pixmap = transform_pixmap(temp_pixmap, W_hex, B_hex, grayscale='night')
                    elif theme == 'eink':
                        temp_pixmap = transform_pixmap(temp_pixmap, W_hex, B_hex, grayscale='eink')
                    elif theme == 'invert':
                        temp_pixmap = transform_pixmap(temp_pixmap, W_hex, B_hex, invert=True)
                    else:
                        temp_pixmap = transform_pixmap(temp_pixmap, W_hex, B_hex)
                    qt_img = temp_pixmap.toImage()
                return page_num, qt_img
            except Exception as e:
                print(f"Pre-render error page {page_num}: {e}")
                return page_num, None

        def _on_done(future):
            page_num, qt_img = future.result()
            if qt_img and not qt_img.isNull():
                cache_key = (page_num, theme)
                if cache_key not in self._theme_page_cache:
                    pixmap = QPixmap.fromImage(qt_img)
                    cache_limit = 40 if is_epub else 20
                    if len(self._theme_page_cache) >= cache_limit:
                        self._theme_page_cache.pop(next(iter(self._theme_page_cache)))
                    self._theme_page_cache[cache_key] = pixmap

        executor = ThreadPoolExecutor(max_workers=2)
        for pn in pages_to_render:
            f = executor.submit(_render_one, pn)
            f.add_done_callback(_on_done)
        executor.shutdown(wait=False)

    def render_facing(self):
        if not self.doc:
            return

        right_1idx = self.right_page
        self.left_pane.setVisible(not self.single_page_mode)

        # 渲染右页（主线程，保证 UI 响应）
        right_rotation = self.page_rotations.get(str(right_1idx), 0)
        self.right_pane.rotation = right_rotation
        right_pixmap = self.render_page(right_1idx - 1)
        right_annotations = self.get_annotations_for_page(right_1idx)
        if self.current_search_term and right_1idx in self.search_highlights:
            self.right_pane.set_search_highlights(
                self.search_highlights[right_1idx], self.current_search_term
            )
        else:
            self.right_pane.set_search_highlights([])
        self.right_pane.set_page(
            right_pixmap,
            right_1idx,
            is_left=False,
            reset_view=False,
            annotations=right_annotations,
        )

        # 渲染左页
        if not self.single_page_mode:
            left_page_num = max(1, min(self.locked_left_page, self.total_pages))
            self.locked_left_page = left_page_num
            left_rotation = self.page_rotations.get(str(left_page_num), 0)
            self.left_pane.rotation = left_rotation
            left_pixmap = self.render_page(left_page_num - 1)
            left_annotations = self.get_annotations_for_page(left_page_num)
            if self.current_search_term and left_page_num in self.search_highlights:
                self.left_pane.set_search_highlights(
                    self.search_highlights[left_page_num], self.current_search_term
                )
            else:
                self.left_pane.set_search_highlights([])
            self.left_pane.set_page(
                left_pixmap,
                left_page_num,
                is_left=True,
                reset_view=False,
                annotations=left_annotations,
            )

        self.update_status()

        # 异步预渲染当前页附近的页面（后台线程，不阻塞 UI）
        self._pre_render_pages(right_1idx - 1)

    def get_annotations_for_page(self, page_num):
        """获取指定页面的批注"""
        page_key = str(page_num)
        if page_key in self.annotations:
            # 确保批注数据格式正确
            annotations = self.annotations[page_key]
            for annotation in annotations:
                # 修复：确保points是列表的列表
                if annotation.get("type") == "pen":
                    points = annotation.get("points", [])
                    if points and isinstance(points[0], dict):
                        # 转换字典格式的points为列表格式
                        annotation["points"] = [
                            (p.get("x", 0), p.get("y", 0)) for p in points
                        ]
            return annotations
        return []

    def save_annotation(self, page_num, annotation):
        """保存批注"""
        page_key = str(page_num)
        if page_key not in self.annotations:
            self.annotations[page_key] = []
        self.annotations[page_key].append(annotation)
        self.save_config()

    def update_pane_colors(self):
        """更新面板颜色设置"""
        pen_color = self.pen_colors[self.current_pen_color_index]
        rect_color = self.rect_colors[self.current_rect_color_index]
        text_color = self.text_colors[self.current_text_color_index]

        self.left_pane.set_pen_color(pen_color)
        self.left_pane.set_rect_color(rect_color)
        self.left_pane.set_text_color(text_color)

        self.right_pane.set_pen_color(pen_color)
        self.right_pane.set_rect_color(rect_color)
        self.right_pane.set_text_color(text_color)

    def update_status(self):
        mode_str = self.tr("Single") if self.single_page_mode else self.tr("Double")
        lock_icon = "🔓" if self.left_locked else "🔗"

        # 批注模式状态
        annotation_mode = self.tr("None")
        if self.left_pane.annotation_mode:
            annotation_mode = f"L:{self.left_pane.annotation_mode}"
        elif self.right_pane.annotation_mode:
            annotation_mode = f"R:{self.right_pane.annotation_mode}"

        # 搜索高亮状态
        search_status = (
            f" 🔍{sum(len(h) for h in self.search_highlights.values())}"
            if self.search_highlights
            else ""
        )

        # === 新增：计算左右窗格的逻辑页码 ===
        left_logical = (
            self.left_pane.page_num + self.page_number_offset
            if self.left_pane.page_num > 0
            else 0
        )
        right_logical = (
            self.right_pane.page_num + self.page_number_offset
            if self.right_pane.page_num > 0
            else 0
        )

        if self.single_page_mode:
            page_display = f"P.{right_logical}"
        else:
            page_display = f"L.{left_logical} R.{right_logical}"
        # ===================================

        if self.is_epub:
            left_pn = left_logical if left_logical > 0 else "-"
            right_pn = right_logical if right_logical > 0 else "-"
            epub_suffix = f"    [{left_pn}/{right_pn}]"
        else:
            epub_suffix = ""

        msg = f"{mode_str} | {page_display} | Home: P.{self.home_page + self.page_number_offset} | ×{self.flip_multiplier} {lock_icon} | Annot: {annotation_mode}{search_status}{epub_suffix}"
        self.statusBar().showMessage(msg)

    def update_color_display(self):
        """更新状态栏颜色显示"""
        pen_color = self.pen_colors[self.current_pen_color_index]
        rect_color = self.rect_colors[self.current_rect_color_index]
        text_color = self.text_colors[self.current_text_color_index]

        # 创建颜色方块
        pen_html = f'<span style="color:{pen_color.name()}; background:white; padding:2px;">■</span>'
        rect_html = f'<span style="color:{rect_color.name()}; background:white; padding:2px;">■</span>'
        text_html = f'<span style="color:{text_color.name()}; background:white; padding:2px;">■</span>'

        self.color_status_label.setText(
            f" Pen:{pen_html}  Highlight:{rect_html}  Text:{text_html}"
        )

    def _update_color_menu_checks(self):
        """更新颜色菜单的勾选状态。"""
        if hasattr(self, '_pen_color_actions'):
            for i, action in enumerate(self._pen_color_actions):
                action.setChecked(i == self.current_pen_color_index)
        if hasattr(self, '_rect_color_actions'):
            for i, action in enumerate(self._rect_color_actions):
                action.setChecked(i == self.current_rect_color_index)
        if hasattr(self, '_text_color_actions'):
            for i, action in enumerate(self._text_color_actions):
                action.setChecked(i == self.current_text_color_index)

    def set_pen_color_index(self, index):
        """设置画笔颜色索引"""
        self.current_pen_color_index = index
        pen_color = self.pen_colors[index]
        self.left_pane.set_pen_color(pen_color)
        self.right_pane.set_pen_color(pen_color)
        self.update_color_display()
        self._update_color_menu_checks()
        self.save_config()

    def set_rect_color_index(self, index):
        """设置矩形高亮颜色索引"""
        self.current_rect_color_index = index
        rect_color = self.rect_colors[index]
        self.left_pane.set_rect_color(rect_color)
        self.right_pane.set_rect_color(rect_color)
        self.update_color_display()
        self._update_color_menu_checks()
        self.save_config()

    def set_text_color_index(self, index):
        """设置文本颜色索引"""
        self.current_text_color_index = index
        text_color = self.text_colors[index]
        self.left_pane.set_text_color(text_color)
        self.right_pane.set_text_color(text_color)
        self.update_color_display()
        self._update_color_menu_checks()
        self.save_config()

    def set_annotation_mode(self, mode):
        """设置批注模式 (全局)"""
        self.annotation_mode = mode

        # === 关键：将模式同步到左右两个窗格 ===
        self.left_pane.set_annotation_mode(mode)
        self.right_pane.set_annotation_mode(mode)
        # ===================================

        # 更新状态栏
        if hasattr(self, "update_status"):
            self.update_status()

    def clear_current_page_annotations(self):
        """清除当前焦点页面的批注"""
        is_left = self.last_focused_pane_is_left and not self.single_page_mode
        if is_left:
            page_num = self.left_pane.page_num
            pane = self.left_pane
        else:
            page_num = self.right_pane.page_num
            pane = self.right_pane

        if str(page_num) in self.annotations:
            del self.annotations[str(page_num)]
            pane.annotations = []
            pane.update()
            self.save_config()
            self.statusBar().showMessage(
                self.tr("🗑️ Cleared annotations on page {page}").format(page=page_num),
                2000,
            )

    def undo_last_annotation(self):
        """撤销最后添加的批注"""
        is_left = self.last_focused_pane_is_left and not self.single_page_mode
        if is_left:
            page_num = self.left_pane.page_num
            pane = self.left_pane
        else:
            page_num = self.right_pane.page_num
            pane = self.right_pane

        page_key = str(page_num)
        if page_key in self.annotations and self.annotations[page_key]:
            # 移除最后一个批注
            removed = self.annotations[page_key].pop()
            pane.annotations = self.annotations[page_key].copy()
            pane.update()
            self.save_config()
            self.statusBar().showMessage(
                self.tr("↩️ Undo last annotation on page {page}").format(page=page_num),
                2000,
            )
        else:
            self.statusBar().showMessage(
                self.tr("ℹ️ No annotations to undo on page {page}").format(
                    page=page_num
                ),
                1000,
            )

    def navigate_back(self):
        """Ctrl+A: 回退到上一个跨页位置（仅1步）"""
        is_left = self.last_focused_pane_is_left and not self.single_page_mode
        last_location = (
            self.left_last_location if is_left else self.right_last_location
        )
        pane = self.left_pane if is_left else self.right_pane

        if last_location is None:
            self.statusBar().showMessage("⏪ No previous location to go back", 1000)
            return

        page_num, rotation, scale, offset = last_location

        # 跳转到历史页面
        self._jump_to_page_internal(page_num, is_left=is_left)

        # 恢复视图状态
        pane.rotation = rotation
        pane.scale_factor = scale
        pane.offset = QPointF(offset[0], offset[1])
        pane.update()

        # 清空历史（避免重复回退）
        if is_left:
            self.left_last_location = None
        else:
            self.right_last_location = None

        self.statusBar().showMessage(f"⏪ Back to P.{page_num}", 1000)

    def _reset_pane_view(self, pane):
        """重置窗格视图：左上角锚点 + 恢复默认缩放（保留旋转）。"""
        if not pane or not pane.original_pixmap:
            return
        pane.offset = QPointF(0, 0)
        pane.apply_fit_mode(self.default_fit_mode)

    def _jump_to_page_internal(self, page_1idx, is_left=False):
        if not self.doc:
            return
        if page_1idx < 1:
            page_1idx = 1
        if page_1idx > self.total_pages:
            page_1idx = self.total_pages
        # === 记录单步历史（仅当跳转超过1页时）===
        current_page = self.left_pane.page_num if is_left else self.right_pane.page_num
        target_page = page_1idx

        # 检查是否为“跨页跳转”（绝对值 > 1）且当前页有效
        if abs(target_page - current_page) > 1 and current_page >= 1:
            # 保存当前状态：(page, rotation, scale, offset)
            current_state = (
                current_page,
                self.left_pane.rotation if is_left else self.right_pane.rotation,
                self.left_pane.scale_factor
                if is_left
                else self.right_pane.scale_factor,
                (self.left_pane.offset.x(), self.left_pane.offset.y())
                if is_left
                else (self.right_pane.offset.x(), self.right_pane.offset.y()),
            )
            # 直接覆盖（只保留最新）
            if is_left:
                self.left_last_location = current_state
            else:
                self.right_last_location = current_state
        # ===================================
        # ===================================
        # 如果是操作左页（且非单页模式）
        if is_left and not self.single_page_mode:
            # 左窗格向前跳转也更新 Home
            furthest = max(page_1idx, self.right_page)
            if furthest > self.home_page:
                self.home_page = furthest
            self.locked_left_page = page_1idx
            # 联动模式：右页跟随左页
            if not self.left_locked:
                self.right_page = max(1, min(page_1idx + 1, self.total_pages))
            self.render_facing()
            # 先设置左上角锚点，再应用默认缩放，确保渲染刷新时位置正确
            self._reset_pane_view(self.left_pane)
            if not self.left_locked:
                self._reset_pane_view(self.right_pane)
            self.left_pane.setFocus()
            self.save_config()
        else:
            # 操作右页（或单页模式）
            if page_1idx > self.home_page:
                self.home_page = page_1idx
            self.right_page = page_1idx
            # 联动模式：左页跟随右页
            if not self.single_page_mode and not self.left_locked:
                self.locked_left_page = max(1, page_1idx - 1)
            self.render_facing()
            self._reset_pane_view(self.right_pane)
            # 联动模式下，跟随的左窗格也重置视图
            if not self.single_page_mode and not self.left_locked:
                self._reset_pane_view(self.left_pane)
            self.right_pane.setFocus()
            self.update_status()

    def jump_to_page(self, page_1idx):
        """
        统一跳转入口。
        使用最后获得焦点的阅读窗格作为目标。
        """
        if not self.doc:
            return
        page_1idx = max(1, min(page_1idx, self.total_pages))

        # 判断目标窗格：使用最后记录的状态
        target_is_left = self.last_focused_pane_is_left and (not self.single_page_mode)

        # 调用内部实现
        self._jump_to_page_internal(page_1idx, is_left=target_is_left)

    def goto_page(self):
        if not self.doc:
            return

        # 创建自定义对话框以获得更好的控制
        dialog = QDialog(self)
        dialog.setWindowTitle(self.tr("Go to Page"))
        dialog.setMinimumWidth(350)  # 设置最小宽度

        layout = QVBoxLayout(dialog)

        # 添加标签
        min_logical = 1 + self.page_number_offset
        max_logical = self.total_pages + self.page_number_offset
        label = QLabel(
            self.tr("Enter page number ({min}-{max}):").format(
                min=min_logical, max=max_logical
            )
        )

        layout.addWidget(label)

        # 添加输入框
        self.page_input = QLineEdit()
        self.page_input.setPlaceholderText(
            self.tr("Enter a number between {min} and {max}").format(
                min=min_logical, max=max_logical
            )
        )
        layout.addWidget(self.page_input)

        # 添加按钮
        button_box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        button_box.accepted.connect(lambda: self.process_page_input(dialog))
        button_box.rejected.connect(dialog.reject)
        layout.addWidget(button_box)

        # 设置焦点到输入框
        self.page_input.setFocus()

        dialog.exec_()

    def process_page_input(self, dialog):
        page_str = self.page_input.text().strip()
        try:
            logical_page = int(page_str)
            # ⚠️ 保持原有转换逻辑不变！
            physical_page = logical_page - self.page_number_offset  # 注意是减号！

            if 1 <= physical_page <= self.total_pages:
                self.jump_to_page(physical_page)
                dialog.accept()
            else:
                QMessageBox.warning(
                    self,
                    self.tr("Invalid Page"),
                    self.tr(
                        "Physical page would be {physical}, which is out of range [1, {total_pages}].\n"
                        "Current offset: {offset}"
                    ).format(
                        physical=physical_page,
                        total_pages=self.total_pages,
                        offset=self.page_number_offset,
                    ),
                )
        except ValueError:
            QMessageBox.warning(
                self, self.tr("Invalid Input"), self.tr("Please enter a valid number")
            )

    def search_text(self):
        """增强的搜索功能"""
        if not self.doc:
            return

        # 创建搜索对话框
        self.search_dialog = SearchDialog(self, self.doc)
        # === 重要：手动更新 SearchDialog 的 UI 文本 ===
        if self.search_dialog:
            dialog = self.search_dialog
            dialog.setWindowTitle(self.tr("Search in PDF"))
            dialog.search_button.setText(self.tr("Search"))
            dialog.prev_button.setText(self.tr("◀ Previous"))
            dialog.next_button.setText(self.tr("Next ▶"))
            dialog.close_button.setText(self.tr("Close"))
            dialog.result_count_label.setText(self.tr("No results"))
        # ===============================================

        self.search_dialog.searchResultSelected.connect(self.on_search_result_selected)
        # === 关键新增：连接对话框关闭信号，用于清除高亮 ===
        self.search_dialog.finished.connect(self.clear_search_highlights)
        # ===============================================
        self.search_dialog.show()

    def on_search_result_selected(self, page_num, context):
        """处理搜索结果选择"""
        self.jump_to_page(page_num)
        # 在状态栏显示上下文
        if len(context) > 50:
            context = context[:50] + "..."
        self.statusBar().showMessage(
            self.tr("🔍 {context}").format(context=context), 3000
        )

    def export_notebook(self):
        """导出笔记：将当前PDF和其配置打包为 .tactinote 文件"""
        if not self.pdf_path or not self.doc:
            QMessageBox.warning(
                self, self.tr("Save Notebook"), self.tr("No document is open.")
            )  # <-- 这里改了
            return

        # 1. 确保最新状态已写入当前的配置文件
        self.save_config()

        # 2. 获取当前配置文件路径
        current_config_path = self.config_file
        if not current_config_path or not os.path.exists(current_config_path):
            QMessageBox.critical(
                self, self.tr("Error"), self.tr("Failed to locate config file.")
            )
            return

        # 3. 弹出保存对话框
        # === 智能生成默认文件名 ===
        if self.notebook_source_path:
            # 如果当前是从一个 .tactinote 打开的，就用它的名字
            base_name = os.path.splitext(os.path.basename(self.notebook_source_path))[0]
        elif self.pdf_path:
            # 如果是普通PDF模式，就用PDF的名字
            base_name = os.path.splitext(os.path.basename(self.pdf_path))[0]
        else:
            base_name = "notebook"
        default_name = base_name + ".tactinote"
        # =========================
        save_path, _ = QFileDialog.getSaveFileName(
            self,
            self.tr("Export Notebook"),
            default_name,
            self.tr("TactiReader Notebook (*.tactinote)"),
        )
        if not save_path:
            return
        if not save_path.endswith(".tactinote"):
            save_path += ".tactinote"

        try:
            import zipfile

            with zipfile.ZipFile(save_path, "w", zipfile.ZIP_STORED) as zf:
                # 打包 PDF
                zf.write(self.pdf_path, "document.pdf")
                # 打包现有的 .json 配置文件，并重命名为 session.json
                zf.write(current_config_path, "session.json")

            self.statusBar().showMessage(
                self.tr("Notebook exported to: {}").format(os.path.basename(save_path)),
                3000,
            )
        except Exception as e:
            QMessageBox.critical(
                self, self.tr("Error"), f"{self.tr('Failed to export notebook')}: {e}"
            )

    def save_as_pdf(self):
        """另存为PDF：复用现有逻辑，只做三件事"""
        if not self.doc or not self.pdf_path:
            return

        # === 智能生成默认文件名 ===
        if self.notebook_source_path:
            # 如果当前是从一个 .tactinote 打开的，就用它的名字（去掉 .tactinote 后缀）
            base_name = os.path.splitext(os.path.basename(self.notebook_source_path))[0]
        else:
            # 否则，用当前PDF的名字（去掉 .pdf 后缀）
            base_name = os.path.splitext(os.path.basename(self.pdf_path))[0]
        default_name = base_name + ".pdf"
        # =========================

        # 1. 弹出保存对话框
        new_pdf_path, _ = QFileDialog.getSaveFileName(
            self,
            self.tr("Save As PDF"),
            default_name,  # <-- 使用智能生成的默认名
            self.tr("PDF Files (*.pdf)"),
        )
        if not new_pdf_path:
            return
        if not new_pdf_path.lower().endswith(".pdf"):
            new_pdf_path += ".pdf"

        try:
            import shutil

            # STEP 1: 确保当前状态已保存到磁盘 (save config)
            self.save_config()

            # STEP 2: 搬运PDF (pdf搬运)
            shutil.copy2(self.pdf_path, new_pdf_path)

            # STEP 3: 搬运JSON (json搬运)
            old_config_path = self.config_file
            new_config_path = get_config_path(new_pdf_path)
            if old_config_path and os.path.exists(old_config_path):
                shutil.copy2(old_config_path, new_config_path)

            # 完成
            print(f"[INFO] Save As successful: {new_pdf_path}")

        except Exception as e:
            print(f"[ERROR] Save As failed: {e}")

    def import_notebook(self):
        """导入笔记：从 .tactinote 文件加载，并进入笔记本模式"""
        notebook_path, _ = QFileDialog.getOpenFileName(
            self,
            self.tr("Import Notebook"),
            "",
            self.tr("TactiReader Notebook (*.tactinote)"),
        )
        if not notebook_path:
            return
        abs_notebook_path = os.path.abspath(notebook_path)

        # 如果已在打开列表中，切换到对应文档
        for i, path in enumerate(self.open_documents):
            if os.path.abspath(path) == abs_notebook_path:
                self._switch_to_document(i)
                return

        # 否则，打开新笔记本
        self.import_notebook_from_path(notebook_path)

    def _flush_notebook_to_source(self):
        """内部方法：将当前工作区的状态打包回源 .tactinote 文件"""
        if not self.notebook_source_path or not self.config_file:
            return

        try:
            import zipfile
            import tempfile
            import shutil

            work_dir = os.path.dirname(self.config_file)
            source_pdf = os.path.join(work_dir, "document.pdf")
            source_session = self.config_file

            # 创建一个临时的 .tactinote 文件
            temp_dir = tempfile.mkdtemp(prefix="tactireader_flush_")
            temp_notebook = os.path.join(temp_dir, "temp.tactinote")

            with zipfile.ZipFile(temp_notebook, "w", zipfile.ZIP_STORED) as zf:
                zf.write(source_pdf, "document.pdf")
                zf.write(source_session, "session.json")

            # 原子性地替换源文件
            shutil.move(temp_notebook, self.notebook_source_path)
            # 清理工作目录
            shutil.rmtree(work_dir, ignore_errors=True)
            # 重置状态
            self.notebook_source_path = None

            self.statusBar().showMessage(self.tr("Notebook saved."), 2000)
        except Exception as e:
            print(f"Failed to flush notebook: {e}")

    def dragEnterEvent(self, event: QDragEnterEvent):
        if event.mimeData().hasUrls():
            urls = event.mimeData().urls()
            if len(urls) == 1 and urls[0].toLocalFile().lower().endswith(".pdf"):
                event.acceptProposedAction()

    def dropEvent(self, event: QDropEvent):
        if not event.mimeData().hasUrls():
            return

        url = event.mimeData().urls()[0]
        path = url.toLocalFile()

        if path.lower().endswith((".pdf", ".tactinote")):
            # === 关键修复：拖入前保存当前 .tactinote ===
            if getattr(self, "notebook_source_path", None) is not None:
                try:
                    self.save_config()
                    self._flush_notebook_to_source()
                except Exception as e:
                    print(f"[WARN] Failed to save current .tactinote before drop: {e}")
            # =========================================

            abs_path = os.path.abspath(path)

            # 检查是否已在打开列表中
            for i, opened_path in enumerate(self.open_documents):
                if os.path.abspath(opened_path) == abs_path:
                    self._switch_to_document(i)
                    event.accept()
                    return

            # 添加到文档列表
            self.open_documents.append(abs_path)
            self.save_global_config()
            self.update_document_tabs()  # 这会触发 tabBar 更新并设置 currentIndex

            # 加载文档
            if path.lower().endswith(".tactinote"):
                self.import_notebook_from_path(path)
            else:
                self.load_pdf(path)

            event.accept()
        else:
            event.ignore()

    def refresh_bookmark_panel(self):
        # 保留文档目录按钮，移除其他所有子控件
        widgets_to_keep = {self._toc_panel_btn}
        for i in reversed(range(self.bookmark_layout.count())):
            widget = self.bookmark_layout.itemAt(i).widget()
            if widget not in widgets_to_keep:
                self.bookmark_layout.removeWidget(widget)
                widget.deleteLater()

        # 重新添加自定义书签
        bookmark_widgets = []
        if not self.bookmarks:
            placeholder = QLabel(self.tr("<no bookmarks>"))
            placeholder.setAlignment(Qt.AlignCenter)
            placeholder.setWordWrap(True)
            placeholder.setStyleSheet("color: gray; font-style: italic;")
            bookmark_widgets.append(placeholder)
        else:
            keys_in_order = ["Q", "W", "E", "R", "T", "Y", "U", "I", "O", "P"]
            for key in keys_in_order:
                if key in self.bookmarks:
                    bm = self.bookmarks[key]
                    btn = BookmarkButton(key, bm["page"], bm.get("name", ""))
                    btn.bookmarkClicked.connect(self._on_bookmark_clicked)
                    bookmark_widgets.append(btn)

        # 将所有书签widget插入到布局的最前面（索引0开始）
        for i, widget in enumerate(bookmark_widgets):
            self.bookmark_layout.insertWidget(i, widget)

    def toggle_bookmark_panel(self):
        """切换书签/目录面板的显示/隐藏状态"""
        self.bookmark_panel_visible = not self.bookmark_panel_visible
        self.bookmark_panel.setVisible(self.bookmark_panel_visible)

        # 更新 splitter 大小以适应变化
        if hasattr(self, "splitter"):
            total_width = self.splitter.width()
            if self.bookmark_panel_visible:
                # 显示书签面板，阅读区域宽度减少
                reading_width = total_width
            else:
                # 隐藏书签面板，阅读区域占据更多空间
                reading_width = total_width + 180

        # 保存状态到配置
        self.save_config()

        # 状态栏提示
        status = "shown" if self.bookmark_panel_visible else "hidden"
        self.statusBar().showMessage(f"📂 Navigation panel {status}", 1000)

    def _on_bookmark_clicked(self, key):
        if key in self.bookmarks:
            page = self.bookmarks[key]["page"]
            self.jump_to_page(page)

    def keyPressEvent(self, event):
        if not self.doc:
            return

        key = event.key()
        modifiers = event.modifiers()
        focused_on_left = self.last_focused_pane_is_left and not self.single_page_mode
        # Ctrl+X: Reset current two pages (zoom, pan, rotation) and center splitter
        # Ctrl+X: Reset current two pages (zoom, pan, rotation) and center splitter
        if key == Qt.Key_X and modifiers == Qt.ControlModifier:
            # === 先重置 splitter 尺寸 ===
            total_width = self.splitter.width()
            self.splitter.setSizes([total_width // 2, total_width // 2])
            # ===========================

            # Reset right pane
            self.right_pane.reset_view()
            self.page_rotations[str(self.right_pane.page_num)] = 0

            # Reset left pane if in double page mode
            if not self.single_page_mode:
                self.left_pane.reset_view()
                self.page_rotations[str(self.left_pane.page_num)] = 0

            self.save_config()
            self.statusBar().showMessage(
                self.tr(
                    "🔄 Current pages reset (zoom+pan+rotation) & splitter centered"
                ),
                1500,
            )
            return

        # Ctrl+Shift+X: Clear all rotations for the entire book
        if key == Qt.Key_X and modifiers == (Qt.ControlModifier | Qt.ShiftModifier):
            # Clear all page rotations
            self.page_rotations.clear()

            # Reset both panes' view states
            self.left_pane.reset_view()
            self.right_pane.reset_view()

            # Also clear any stored annotations view states if needed (though annotations don't store view)
            self.save_config()
            self.render_facing()  # Re-render to apply rotation=0 to all pages
            self.statusBar().showMessage(
                self.tr("🗑️ All page rotations cleared for entire book!"), 2000
            )
            return
        # X: Reset zoom AND rotation on focused pane
        if key == Qt.Key_X and modifiers == Qt.NoModifier:
            if focused_on_left:
                self.left_pane.reset_view()
                self.page_rotations[str(self.left_pane.page_num)] = 0
                self.save_config()
                self.statusBar().showMessage(
                    self.tr("⬅️ Left reset (zoom+rotation)"), 1000
                )
            else:
                self.right_pane.reset_view()
                self.page_rotations[str(self.right_pane.page_num)] = 0
                self.save_config()
                self.statusBar().showMessage(
                    self.tr("➡️ Right reset (zoom+rotation)"), 1000
                )
            return

        # ~: Rotate clockwise on focused pane
        if key == Qt.Key_QuoteLeft and modifiers == Qt.NoModifier:
            if focused_on_left:
                self.left_pane.rotate_clockwise()
                self.page_rotations[str(self.left_pane.page_num)] = (
                    self.left_pane.rotation
                )
                self.save_config()
                self.statusBar().showMessage(
                    self.tr("🔄 Left rotated to {angle}°").format(
                        angle=self.left_pane.rotation
                    ),
                    1000,
                )
            else:
                self.right_pane.rotate_clockwise()
                self.page_rotations[str(self.right_pane.page_num)] = (
                    self.right_pane.rotation
                )
                self.save_config()
                self.statusBar().showMessage(
                    self.tr("🔄 Right rotated to {angle}°").format(
                        angle=self.right_pane.rotation
                    ),
                    1000,
                )
            return

        # B: 自由画笔
        if key == Qt.Key_B and modifiers == Qt.NoModifier:
            self.set_annotation_mode("pen")
            self.statusBar().showMessage(
                self.tr("✏️ Pen mode (press ESC to cancel)"), 2000
            )
            return

        # H: 矩形高亮
        if key == Qt.Key_H and modifiers == Qt.NoModifier:
            self.set_annotation_mode("rect")
            self.statusBar().showMessage(
                self.tr("🔲 Highlight mode (press ESC to cancel)"), 2000
            )
            return

        # V: 文本框
        if key == Qt.Key_V and modifiers == Qt.NoModifier:
            self.set_annotation_mode("text")
            self.statusBar().showMessage(
                self.tr("📝 Text mode (press ESC to cancel)"), 2000
            )
            return

        # L: 打开文档目录
        if key == Qt.Key_L and modifiers == Qt.NoModifier:
            self.open_toc_dialog()
            return

        # Z: Toggle single/double page mode
        if key == Qt.Key_Z and modifiers == Qt.NoModifier:
            self.single_page_mode = not self.single_page_mode
            if self.single_page_mode:
                self.left_locked = False
            self.save_config()
            self.render_facing()
            mode_name = (
                self.tr("Single") if self.single_page_mode else self.tr("Double")
            )
            self.statusBar().showMessage(
                self.tr("↔️ Mode: {mode}-page").format(mode=mode_name), 1500
            )
            return

        # C: Toggle left pane link/unlink (only in double mode)
        if key == Qt.Key_C and modifiers == Qt.NoModifier and not self.single_page_mode:
            self.left_locked = not self.left_locked
            if not self.left_locked:
                # 恢复联动：焦点页不变，另一页联动过来
                if self.last_focused_pane_is_left:
                    # 焦点在左页：右页 = 左页 + 1
                    self.locked_left_page = max(1, self.left_pane.page_num)
                    self.right_page = max(1, min(self.left_pane.page_num + 1, self.total_pages))
                else:
                    # 焦点在右页：左页 = 右页 - 1
                    self.right_page = max(1, self.right_pane.page_num)
                    self.locked_left_page = max(1, self.right_page - 1)
            self.render_facing()
            status = self.tr("Unlinked") if self.left_locked else self.tr("Linked")
            self.statusBar().showMessage(f"🔗 {status}", 1500)
            self.save_config()
            return

        # S: Save config manually (or flush notebook)
        if key == Qt.Key_S and modifiers == Qt.NoModifier:
            if self.notebook_source_path is not None:
                # 笔记本模式：立即打包回源 .tactinote 文件
                self.save_config()
                self._flush_notebook_to_source()
            else:
                # 普通PDF模式：保存到 AppData
                self.save_config()
                self.statusBar().showMessage(self.tr("💾 Configuration saved"), 1500)
            return

        # SPACE: Jump to Home
        if key == Qt.Key_Space and modifiers == Qt.NoModifier:
            target = self.home_page
            self.jump_to_page(target)
            return

        # Ctrl+Space: Reset Home to current focused page
        if key == Qt.Key_Space and modifiers == Qt.ControlModifier:
            current_page = (
                self.left_pane.page_num if focused_on_left else self.right_page
            )
            self.home_page = current_page
            self.save_config()
            self.statusBar().showMessage(
                self.tr("🔄 Home reset to P.{page}").format(page=self.home_page), 2000
            )
            return
        # Ctrl+A: Navigate back in history
        if key == Qt.Key_A and modifiers == Qt.ControlModifier:
            self.navigate_back()
            return
        # A/D: Single step
        if key == Qt.Key_A and modifiers == Qt.NoModifier:
            current_page = (
                self.left_pane.page_num if focused_on_left else self.right_page
            )
            self.jump_to_page(current_page - 1)
            return
        if key == Qt.Key_D and modifiers == Qt.NoModifier:
            current_page = (
                self.left_pane.page_num if focused_on_left else self.right_page
            )
            self.jump_to_page(current_page + 1)
            return

        # Digit keys: color switch in annotation mode, flip multiplier otherwise
        digit_map = {getattr(Qt, f"Key_{i}"): i - 1 for i in range(1, 10)}
        if key in digit_map and modifiers == Qt.NoModifier:
            idx = digit_map[key]
            if self.annotation_mode == "pen":
                if idx < len(self.pen_colors):
                    self.set_pen_color_index(idx)
                    color_name = PEN_COLOR_NAMES[idx] if idx < len(PEN_COLOR_NAMES) else str(idx + 1)
                    self.statusBar().showMessage(
                        self.tr("✏️ Pen color: {name}").format(name=color_name), 1200
                    )
                return
            elif self.annotation_mode == "rect":
                if idx < len(self.rect_colors):
                    self.set_rect_color_index(idx)
                    color_name = RECT_COLOR_NAMES[idx] if idx < len(RECT_COLOR_NAMES) else str(idx + 1)
                    self.statusBar().showMessage(
                        self.tr("🔲 Highlight color: {name}").format(name=color_name), 1200
                    )
                return
            elif self.annotation_mode == "text":
                if idx < len(self.text_colors):
                    self.set_text_color_index(idx)
                    color_name = TEXT_COLOR_NAMES[idx] if idx < len(TEXT_COLOR_NAMES) else str(idx + 1)
                    self.statusBar().showMessage(
                        self.tr("📝 Text color: {name}").format(name=color_name), 1200
                    )
                return
            else:
                self.flip_multiplier = idx + 1
                self.save_config()
                self.statusBar().showMessage(
                    self.tr("🔁 Flip ×{x}").format(x=self.flip_multiplier), 1500
                )
                return

        # Arrow keys
        if key == Qt.Key_Left and modifiers == Qt.NoModifier:
            current_page = (
                self.left_pane.page_num if focused_on_left else self.right_page
            )
            self.jump_to_page(current_page - self.flip_multiplier)
            return
        if key == Qt.Key_Right and modifiers == Qt.NoModifier:
            current_page = (
                self.left_pane.page_num if focused_on_left else self.right_page
            )
            self.jump_to_page(current_page + self.flip_multiplier)
            return

        # F/G
        if key == Qt.Key_F and modifiers == Qt.NoModifier:
            self.search_text()
            return
        if key == Qt.Key_G and modifiers == Qt.NoModifier:
            self.goto_page()
            return
        # Ctrl+G: Calibrate page number offset
        if key == Qt.Key_G and modifiers == Qt.ControlModifier:
            self.calibrate_page_number_offset()
            return
        # Ctrl+Shift+G: Clear page number offset
        if key == Qt.Key_G and modifiers == (Qt.ControlModifier | Qt.ShiftModifier):
            self.clear_page_number_offset()
            return
        # Clear all config: Ctrl+Shift+R
        if key == Qt.Key_R and modifiers == (Qt.ControlModifier | Qt.ShiftModifier):
            reply = QMessageBox.question(
                self,
                self.tr("Clear All Config"),
                self.tr(
                    "Are you sure you want to clear ALL settings (bookmarks, home, mode, etc.) for this PDF?"
                ),
                QMessageBox.Yes | QMessageBox.No,
            )
            if reply == QMessageBox.Yes:
                self.home_page = 1
                self.bookmarks = {}
                self.flip_multiplier = 2
                self.single_page_mode = False
                self.left_locked = False
                self.locked_left_page = 1
                self.annotations = {}
                self.page_rotations = {}
                self.search_highlights = {}  # 清空搜索高亮
                self.current_search_term = ""
                self.current_pen_color_index = 0
                self.current_rect_color_index = 0
                self.current_text_color_index = 0
                self.update_pane_colors()
                self.save_config()
                self.render_facing()
                self.refresh_bookmark_panel()
                self.statusBar().showMessage(
                    self.tr("🗑️ All configuration cleared!"), 2000
                )
            return

        # 清除当前页面批注: Ctrl+Shift+C
        if key == Qt.Key_C and modifiers == (Qt.ControlModifier | Qt.ShiftModifier):
            self.clear_current_page_annotations()
            return

        # 撤销批注: Ctrl+Z
        if key == Qt.Key_Z and modifiers == Qt.ControlModifier:
            self.undo_last_annotation()
            return
        # N: Toggle bookmark/TOC panel visibility
        if key == Qt.Key_N and modifiers == Qt.NoModifier:
            self.toggle_bookmark_panel()
            return
        # Bookmarks: Q to P
        bookmark_key_map = {
            Qt.Key_Q: "Q",
            Qt.Key_W: "W",
            Qt.Key_E: "E",
            Qt.Key_R: "R",
            Qt.Key_T: "T",
            Qt.Key_Y: "Y",
            Qt.Key_U: "U",
            Qt.Key_I: "I",
            Qt.Key_O: "O",
            Qt.Key_P: "P",
        }

        if key in bookmark_key_map:
            char = bookmark_key_map[key]

            if modifiers == Qt.AltModifier:
                if char in self.bookmarks:
                    name = (
                        self.bookmarks[char].get("name", "")
                        or f"P.{self.bookmarks[char]['page']}"
                    )
                    del self.bookmarks[char]
                    self.save_config()
                    self.refresh_bookmark_panel()
                    self.statusBar().showMessage(
                        self.tr("🗑️ Cleared '{char}': {name}").format(
                            char=char, name=name
                        ),
                        2000,
                    )
                else:
                    self.statusBar().showMessage(
                        self.tr("ℹ️ '{char}' was empty").format(char=char), 1000
                    )
                return

            elif modifiers == Qt.ControlModifier:
                current_page = (
                    self.right_page if not focused_on_left else self.left_pane.page_num
                )
                name, ok = QInputDialog.getText(
                    self,
                    self.tr("Set Bookmark") + f" {char}",
                    self.tr("Name for '{char}' (P.{page}):").format(
                        char=char, page=current_page
                    ),
                    text=self.bookmarks.get(char, {}).get("name", ""),
                )
                if ok:
                    self.bookmarks[char] = {"page": current_page, "name": name.strip()}
                    self.save_config()
                    self.refresh_bookmark_panel()
                    display_name = name.strip() or f"P.{current_page}"
                    self.statusBar().showMessage(
                        self.tr("🔖 '{char}' → {display_name}").format(
                            char=char, display_name=display_name
                        ),
                        2000,
                    )
                return

            elif modifiers == Qt.NoModifier:
                if char in self.bookmarks:
                    bm = self.bookmarks[char]
                    self.jump_to_page(bm["page"])
                    display_name = bm.get("name", "").strip() or f"P.{bm['page']}"
                    self.statusBar().showMessage(
                        self.tr("⏩ '{char}': {display_name}").format(
                            char=char, display_name=display_name
                        ),
                        1500,
                    )
                else:
                    self.statusBar().showMessage(
                        self.tr("⚠️ '{char}' not set").format(char=char), 1500
                    )
                return

        # ESC: 取消批注模式
        if key == Qt.Key_Escape and modifiers == Qt.NoModifier:
            self.annotation_mode = None
            self.left_pane.cancel_annotation()
            self.right_pane.cancel_annotation()
            # 2. 退出文字选取模式 (通知两个窗格)
            self.left_pane.set_text_selection_mode(False)
            self.right_pane.set_text_selection_mode(False)
            self.update_status()
            return

        super().keyPressEvent(event)

    def toggle_fullscreen(self):
        """切换全屏模式"""
        if self.isFullScreen():
            self.showNormal()
            # 退出全屏时显示菜单栏和状态栏
            self.menuBar().setVisible(True)
            self.statusBar().setVisible(True)
        else:
            self.showFullScreen()
            # 进入全屏时隐藏菜单栏和状态栏
            self.menuBar().setVisible(False)
            self.statusBar().setVisible(False)

    def toggle_text_selection_mode(self):
        """全局切换文字选取模式（同步左右窗格）"""
        new_state = not self.right_pane.text_selection_mode
        self.left_pane.set_text_selection_mode(new_state)
        self.right_pane.set_text_selection_mode(new_state)
        status = "ON" if new_state else "OFF"
        self.statusBar().showMessage(f"🔤 Text Selection Mode: {status}", 2000)

    def show_help(self):
        viewer = MarkdownViewer(self.tr("Help"), self.tr("docs/help.md"), self)
        viewer.exec_()

    def show_about(self):
        viewer = MarkdownViewer(self.tr("About"), self.tr("docs/about.md"), self)
        viewer.exec_()

    def closeEvent(self, event):
        if self.doc:
            self.save_config()
            # === 新增：如果是笔记本模式，退出时打包回源文件 ===
            if self.notebook_source_path is not None:
                self._flush_notebook_to_source()
            # =============================================
            self.doc.close()
        # 保存全局配置（打开文档列表 + 当前阅读文档）
        self.save_global_config()
        event.accept()


class MarkdownViewer(QDialog):
    def __init__(self, title, md_file, parent=None):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.resize(800, 600)

        # 使用 QTextEdit（只读、纯文本/markdown 渲染）
        self.text_edit = QTextBrowser()
        self.text_edit.setReadOnly(True)
        # === 新增：设置更大的默认字体 ===
        font = self.text_edit.font()
        font.setPointSize(13)  # 默认通常是 9-10，12 更清晰
        self.text_edit.setFont(font)
        # 构建文件路径
        if getattr(sys, "frozen", False):
            base_path = sys._MEIPASS
        else:
            base_path = os.path.dirname(os.path.abspath(__file__))
        full_path = os.path.join(base_path, md_file)

        # 读取并渲染 Markdown
        try:
            with open(full_path, "r", encoding="utf-8") as f:
                md_content = f.read()
            html = markdown.markdown(
                md_content,
                extensions=["fenced_code", "tables", "toc"],
            )
            styled_html = f"""
<style>
body {{
    font-family: "Microsoft YaHei", "PingFang SC", "Segoe UI", sans-serif;
    font-size: 18px;
    line-height: 1.9;
    color: #2c3e50;
    max-width: 760px;
    margin: 0 auto;
    padding: 28px 32px;
}}
h1 {{
    font-size: 30px;
    color: #1a1a1a;
    border-bottom: 3px solid #3498db;
    padding-bottom: 14px;
    margin-top: 10px;
    margin-bottom: 28px;
    font-weight: 600;
}}
h2 {{
    font-size: 24px;
    color: #1a1a1a;
    border-left: 5px solid #3498db;
    padding-left: 14px;
    margin-top: 36px;
    margin-bottom: 18px;
    font-weight: 600;
}}
h3 {{
    font-size: 20px;
    color: #2c3e50;
    margin-top: 28px;
    margin-bottom: 14px;
    font-weight: 600;
}}
p {{
    margin: 14px 0;
    text-align: justify;
}}
strong {{
    color: #c0392b;
    font-weight: 600;
}}
em {{
    color: #7f8c8d;
}}
ul, ol {{
    margin: 14px 0;
    padding-left: 28px;
}}
li {{
    margin: 8px 0;
    line-height: 1.8;
}}
table {{
    width: 100%;
    border-collapse: collapse;
    margin: 24px 0;
    font-size: 16px;
}}
th {{
    background-color: #3498db;
    color: white;
    font-weight: 600;
    text-align: left;
    padding: 12px 16px;
    border: 1px solid #2980b9;
}}
td {{
    padding: 11px 16px;
    border: 1px solid #dce6f0;
    color: #2c3e50;
}}
tr:nth-child(even) {{
    background-color: #f7fafc;
}}
tr:hover {{
    background-color: #edf5fd;
}}
hr {{
    border: none;
    border-top: 1px solid #e0e6ed;
    margin: 32px 0;
}}
blockquote {{
    border-left: 4px solid #f39c12;
    background-color: #fef9ef;
    padding: 14px 20px;
    margin: 18px 0;
    color: #7d6608;
    font-style: italic;
}}
code {{
    background-color: #f0f3f6;
    color: #e74c3c;
    padding: 3px 7px;
    border-radius: 3px;
    font-family: Consolas, Monaco, monospace;
    font-size: 15px;
}}
pre {{
    background-color: #2c3e50;
    color: #ecf0f1;
    padding: 18px;
    border-radius: 6px;
    overflow-x: auto;
    margin: 18px 0;
}}
pre code {{
    background: none;
    color: #ecf0f1;
    padding: 0;
    font-size: 15px;
}}
</style>
<body>
{html}
</body>
"""
            self.text_edit.setHtml(styled_html)
        except Exception as e:
            self.text_edit.setPlainText(f"无法加载帮助文件: {md_file}\n错误: {str(e)}")

        layout = QVBoxLayout()
        layout.addWidget(self.text_edit)
        self.setLayout(layout)


# ============================================================
# EPUB 图片列表 & 脚注列表 & 图片查看器
# ============================================================

def _parse_epub_html_source(epub_path):
    """解析 EPUB 源文件，提取图片列表和脚注列表。
    返回: (images, footnotes)
      images: [{'src': str, 'alt': str, 'data': bytes, 'mime': str, 'chapter': str}, ...]
      footnotes: [{'marker': str, 'marker_html': str, 'content': str, 'content_html': str, 'chapter': str}, ...]
    """
    import xml.etree.ElementTree as ET

    images = []
    footnotes = []

    try:
        with zipfile.ZipFile(epub_path, 'r') as zf:
            # 1. 读取 container.xml 找到 OPF 路径
            container_xml = zf.read('META-INF/container.xml').decode('utf-8', errors='ignore')
            opf_match = re.search(r'full-path="([^"]+)"', container_xml)
            if not opf_match:
                opf_match = re.search(r"full-path='([^']+)'", container_xml)
            if not opf_match:
                return images, footnotes
            opf_path = opf_match.group(1)
            opf_dir = os.path.dirname(opf_path)

            # 2. 解析 OPF 获取 manifest 和 spine
            opf_data = zf.read(opf_path).decode('utf-8', errors='ignore')
            # 注册命名空间
            ns = {'opf': 'http://www.idpf.org/2007/opf', 'dc': 'http://purl.org/dc/elements/1.1/'}
            # 尝试解析 XML
            try:
                root = ET.fromstring(opf_data)
            except ET.ParseError:
                # 去掉命名空间再试
                opf_clean = re.sub(r'\sxmlns[^=]*="[^"]*"', '', opf_data)
                root = ET.fromstring(opf_clean)

            # 收集 manifest 条目 (id -> href)
            manifest = {}
            for item in root.iter():
                tag = item.tag.split('}')[-1] if '}' in item.tag else item.tag
                if tag == 'item':
                    item_id = item.get('id', '')
                    href = item.get('href', '')
                    mtype = item.get('media-type', '')
                    manifest[item_id] = {'href': href, 'media-type': mtype}

            # 收集 spine 顺序
            spine = []
            for item in root.iter():
                tag = item.tag.split('}')[-1] if '}' in item.tag else item.tag
                if tag == 'itemref':
                    idref = item.get('idref', '')
                    if idref in manifest:
                        spine.append(manifest[idref])

            # 3. 解析每个 HTML 文件
            footnote_id_counter = 0
            seen_footnote_contents = set()

            for item in spine:
                href = item['href']
                # 解析相对路径
                if opf_dir:
                    html_path = os.path.normpath(os.path.join(opf_dir, href)).replace('\\', '/')
                else:
                    html_path = href

                if not (html_path.lower().endswith(('.html', '.xhtml', '.htm', '.xml'))
                    or item.get('media-type', '').startswith('application/xhtml')
                    or item.get('media-type', '') == 'text/html'):
                    continue

                try:
                    html_data = zf.read(html_path).decode('utf-8', errors='ignore')
                except KeyError:
                    continue

                html_dir = os.path.dirname(html_path)
                chapter_name = os.path.basename(html_path)

                # ---- 提取图片 ----
                # 在 HTML 中找所有 <img> 标签
                img_pattern = re.compile(
                    r'<img\b[^>]*?src\s*=\s*["\']([^"\']+)["\'][^>]*?/?>',
                    re.IGNORECASE | re.DOTALL
                )
                # 找出每个 img 的上下文（父元素 100 字符内）
                for m in img_pattern.finditer(html_data):
                    src = m.group(1)
                    img_tag = m.group(0)

                    # 提取 alt
                    alt_match = re.search(r'alt\s*=\s*["\']([^"\']*)["\']', img_tag, re.IGNORECASE)
                    alt_text = alt_match.group(1) if alt_match else ''

                    # 检查父元素是否包含 footnote 标记
                    # 取 img 标签之前的 200 字符
                    start = max(0, m.start() - 200)
                    context = html_data[start:m.end()]
                    # 检查父元素 opening tag
                    parent_match = re.search(
                        r'<(aside|div|span|li|p|td|section)\b[^>]*?(?:epub:type\s*=\s*["\']footnote["\']|class\s*=\s*["\'][^"\']*footnote[^"\']*["\'])',
                        context, re.IGNORECASE
                    )
                    if parent_match:
                        # 这是脚注中的图片，跳过
                        continue

                    # 解析图片路径
                    img_src = src
                    if not img_src.startswith(('http://', 'https://', 'data:')):
                        # 相对路径
                        if html_dir:
                            img_src = os.path.normpath(os.path.join(html_dir, img_src)).replace('\\', '/')
                        # 去掉开头的 ./
                        img_src = re.sub(r'^\./', '', img_src)

                    # 尝试从 ZIP 中读取图片
                    try:
                        img_data = zf.read(img_src)
                        # 判断 MIME
                        if img_data[:4] == b'\x89PNG':
                            mime = 'image/png'
                        elif img_data[:3] == b'\xff\xd8\xff':
                            mime = 'image/jpeg'
                        elif img_data[:4] == b'GIF8':
                            mime = 'image/gif'
                        elif img_data[:4] == b'RIFF':
                            mime = 'image/webp'
                        else:
                            mime = 'image/png'

                        images.append({
                            'src': img_src,
                            'alt': alt_text,
                            'data': img_data,
                            'mime': mime,
                            'chapter': chapter_name,
                        })
                    except KeyError:
                        # 尝试其他路径变体
                        found = False
                        for name in zf.namelist():
                            if name.endswith('/' + os.path.basename(img_src)) or name == os.path.basename(img_src):
                                try:
                                    img_data = zf.read(name)
                                    if img_data[:4] == b'\x89PNG':
                                        mime = 'image/png'
                                    elif img_data[:3] == b'\xff\xd8\xff':
                                        mime = 'image/jpeg'
                                    else:
                                        mime = 'image/png'
                                    images.append({
                                        'src': name,
                                        'alt': alt_text,
                                        'data': img_data,
                                        'mime': mime,
                                        'chapter': chapter_name,
                                    })
                                    found = True
                                except Exception:
                                    pass
                                break
                        if not found:
                            pass  # 图片无法读取，跳过

                # ---- 提取脚注 ----
                # 模式1: <a epub:type="noteref" href="#fnX">...</a>
                # 模式2: <a class="footnote-ref" href="#fnX">...</a>
                # 模式3: <a href="#fnX" id="fnrefX">...</a>
                noteref_pattern = re.compile(
                    r'<a\b[^>]*?(?:epub:type\s*=\s*["\']noteref["\']|class\s*=\s*["\'](?:[^"\']*\s)?footnote-ref(?:\s[^"\']*)?["\'])[^>]*?href\s*=\s*["\']#([^"\']+)["\'][^>]*>(.*?)</a>',
                    re.IGNORECASE | re.DOTALL
                )
                for ref_match in noteref_pattern.finditer(html_data):
                    target_id = ref_match.group(1)
                    marker_html = ref_match.group(2).strip()
                    # 去掉 HTML 标签得到纯文本标记
                    marker_text = re.sub(r'<[^>]+>', '', marker_html).strip()

                    # 如果标记为空（图片标记），尝试从 alt 或 zy-footnote 提取
                    if not marker_text:
                        # 从 img 标签的 alt 属性提取
                        alt_match = re.search(r'alt\s*=\s*["\']([^"\']*)["\']', marker_html, re.IGNORECASE)
                        if alt_match and alt_match.group(1).strip():
                            marker_text = alt_match.group(1).strip()[:20]
                        else:
                            # 从整个 a 标签的 zy-footnote 属性提取
                            full_tag = ref_match.group(0)
                            zy_match = re.search(r'zy-footnote\s*=\s*["\']([^"\']*)["\']', full_tag, re.IGNORECASE)
                            if zy_match and zy_match.group(1).strip():
                                marker_text = zy_match.group(1).strip()[:20]
                            else:
                                marker_text = f'[{footnote_id_counter + 1}]'

                    # 查找对应的脚注内容
                    # 模式: <aside epub:type="footnote" id="fnX">...</aside>
                    # 模式: <li id="fnX">...</li>
                    # 模式: <div class="footnote" id="fnX">...</div>
                    content_patterns = [
                        # EPUB3 footnote
                        rf'<(?:aside|div|section)\b[^>]*?epub:type\s*=\s*["\']footnote["\'][^>]*?\bid\s*=\s*["\']{re.escape(target_id)}["\'][^>]*>(.*?)</(?:aside|div|section)>',
                        # id-based footnote
                        rf'<(?:aside|li|div|p|section)\b[^>]*?\bid\s*=\s*["\']{re.escape(target_id)}["\'][^>]*>(.*?)</(?:aside|li|div|p|section)>',
                        # class="footnote" + id
                        rf'<(?:aside|li|div|p|section)\b[^>]*?class\s*=\s*["\'][^"\']*\bfootnote\b[^"\']*["\'][^>]*?\bid\s*=\s*["\']{re.escape(target_id)}["\'][^>]*>(.*?)</(?:aside|li|div|p|section)>',
                    ]

                    content_html = ''
                    for pat in content_patterns:
                        cm = re.search(pat, html_data, re.IGNORECASE | re.DOTALL)
                        if cm:
                            content_html = cm.group(1).strip()
                            break

                    if not content_html:
                        continue

                    content_text = re.sub(r'<[^>]+>', '', content_html).strip()
                    content_text = re.sub(r'\s+', ' ', content_text)

                    # 去重（基于内容）
                    content_key = content_text[:50]
                    if content_key in seen_footnote_contents:
                        continue
                    seen_footnote_contents.add(content_key)

                    footnote_id_counter += 1
                    footnotes.append({
                        'marker': marker_text,
                        'marker_html': marker_html,
                        'content': content_text,
                        'content_html': content_html,
                        'chapter': chapter_name,
                        'id': target_id,
                    })

    except Exception as e:
        print(f"[_parse_epub_html_source] Error: {e}")
        import traceback
        traceback.print_exc()

    return images, footnotes


def _build_page_to_chapter_map(epub_path, doc):
    """预计算 PyMuPDF 页码 → EPUB HTML 源文件名的映射。

    一个 HTML 源文件（真实页，通常 .xhtml）可能跨多个 PyMuPDF 渲染页，
    这些页都映射到同一个 HTML 文件。
    返回: {page_1idx: html_basename, ...}
    """
    if not doc:
        return {}

    import xml.etree.ElementTree as ET

    # 1. 解析 spine，按顺序收集 HTML 文件及其纯文本
    html_files = []  # [(basename, clean_text), ...]

    try:
        with zipfile.ZipFile(epub_path, 'r') as zf:
            container_xml = zf.read('META-INF/container.xml').decode('utf-8', errors='ignore')
            opf_match = re.search(r'full-path="([^"]+)"', container_xml)
            if not opf_match:
                return {}
            opf_path = opf_match.group(1)
            opf_dir = os.path.dirname(opf_path)

            opf_data = zf.read(opf_path).decode('utf-8', errors='ignore')
            try:
                root = ET.fromstring(opf_data)
            except ET.ParseError:
                opf_clean = re.sub(r'\sxmlns[^=]*="[^"]*"', '', opf_data)
                root = ET.fromstring(opf_clean)

            manifest = {}
            for item in root.iter():
                tag = item.tag.split('}')[-1] if '}' in item.tag else item.tag
                if tag == 'item':
                    manifest[item.get('id', '')] = {
                        'href': item.get('href', ''),
                        'media-type': item.get('media-type', ''),
                    }

            for item in root.iter():
                tag = item.tag.split('}')[-1] if '}' in item.tag else item.tag
                if tag == 'itemref':
                    idref = item.get('idref', '')
                    if idref in manifest:
                        m = manifest[idref]
                        href = m['href']
                        if opf_dir:
                            html_path = os.path.normpath(os.path.join(opf_dir, href)).replace('\\', '/')
                        else:
                            html_path = href

                        if not (html_path.lower().endswith(('.html', '.xhtml', '.htm', '.xml'))
                                or m.get('media-type', '').startswith('application/xhtml')
                                or m.get('media-type', '') == 'text/html'):
                            continue

                        try:
                            html_data = zf.read(html_path).decode('utf-8', errors='ignore')
                            html_text = re.sub(r'<[^>]+>', '', html_data)
                            html_text_clean = re.sub(r'\s+', '', html_text)
                            html_files.append((os.path.basename(html_path), html_text_clean))
                        except KeyError:
                            continue
    except Exception as e:
        print(f"[_build_page_to_chapter_map] Error: {e}")
        return {}

    if not html_files:
        return {}

    # 2. 遍历所有 PyMuPDF 页面，逐页匹配到 HTML 源文件
    page_map = {}
    html_idx = 0
    total_pages = len(doc)

    for page_1idx in range(1, total_pages + 1):
        page = doc[page_1idx - 1]
        page_text = page.get_text("text")
        page_text_clean = re.sub(r'\s+', '', page_text)

        if not page_text_clean:
            # 空页面，沿用上一个映射
            if html_idx < len(html_files):
                page_map[page_1idx] = html_files[html_idx][0]
            continue

        search_key = page_text_clean[:50]

        # 先检查当前 HTML
        if html_idx < len(html_files) and search_key in html_files[html_idx][1]:
            page_map[page_1idx] = html_files[html_idx][0]
        else:
            # 当前 HTML 不匹配，向前搜寻后续 HTML
            found = False
            for next_idx in range(html_idx + 1, len(html_files)):
                if search_key in html_files[next_idx][1]:
                    html_idx = next_idx
                    page_map[page_1idx] = html_files[html_idx][0]
                    found = True
                    break
            if not found and html_idx < len(html_files):
                page_map[page_1idx] = html_files[html_idx][0]

    return page_map


def _get_page_items(epub_path, doc, page_1idx, chapter_map=None, images_src=None, footnotes_src=None):
    """获取焦点窗口所在 HTML 源文件中的全部图片和脚注。

    page_1idx: 焦点窗口的 1-indexed 页码
    chapter_map: 预计算的页码→HTML文件名映射
    images_src / footnotes_src: 预解析的全书图片/脚注列表
    """
    # 使用预计算映射或回退
    if chapter_map and page_1idx in chapter_map:
        chapter = chapter_map[page_1idx]
    else:
        chapter = None

    # 使用缓存或回退解析
    if images_src is None or footnotes_src is None:
        images_src, footnotes_src = _parse_epub_html_source(epub_path)

    if chapter:
        images = [img for img in images_src if img.get('chapter') == chapter]
        footnotes = [fn for fn in footnotes_src if fn.get('chapter') == chapter]
    else:
        images = images_src
        footnotes = footnotes_src

    return images, footnotes


class ImageViewer(QDialog):
    """图片查看器：支持 Ctrl+滚轮缩放 + 鼠标拖动"""

    def __init__(self, pixmap, title='', parent=None):
        super().__init__(parent)
        self.original_pixmap = pixmap
        self.scale_factor = 1.0
        self.offset = QPointF(0, 0)
        self.drag_start = None
        self._min_scale = 0.1
        self._max_scale = 10.0

        self.setWindowTitle(title if title else 'Image Viewer')
        self.setWindowFlags(Qt.Window | Qt.FramelessWindowHint)
        self.setModal(True)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setMouseTracking(True)
        self.setStyleSheet("background: #1a1a1a;")

        # 全屏显示
        screen = QApplication.primaryScreen().geometry()
        self.resize(screen.width(), screen.height())

        # 初始缩放：适合屏幕
        pw = self.original_pixmap.width()
        ph = self.original_pixmap.height()
        sw = screen.width() - 40
        sh = screen.height() - 40
        self.scale_factor = min(sw / pw, sh / ph, 1.0)
        self._update_offset_for_center()

    def _update_offset_for_center(self):
        """将图片居中"""
        scaled_w = self.original_pixmap.width() * self.scale_factor
        scaled_h = self.original_pixmap.height() * self.scale_factor
        self.offset = QPointF(
            (self.width() - scaled_w) / 2,
            (self.height() - scaled_h) / 2,
        )

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.SmoothPixmapTransform)
        painter.fillRect(self.rect(), QColor(26, 26, 26))

        scaled_size = self.original_pixmap.size() * self.scale_factor
        scaled_pm = self.original_pixmap.scaled(
            scaled_size, Qt.IgnoreAspectRatio, Qt.SmoothTransformation
        )
        painter.drawPixmap(int(self.offset.x()), int(self.offset.y()), scaled_pm)

    def wheelEvent(self, event):
        if event.modifiers() & Qt.ControlModifier:
            # Ctrl+滚轮缩放
            old_scale = self.scale_factor
            delta = event.angleDelta().y() / 120
            factor = 1.0 + delta * 0.15
            new_scale = old_scale * factor
            new_scale = max(self._min_scale, min(self._max_scale, new_scale))

            # 以鼠标位置为中心缩放
            mouse_pos = event.pos()
            img_x = (mouse_pos.x() - self.offset.x()) / old_scale
            img_y = (mouse_pos.y() - self.offset.y()) / old_scale

            self.scale_factor = new_scale
            self.offset.setX(mouse_pos.x() - img_x * new_scale)
            self.offset.setY(mouse_pos.y() - img_y * new_scale)
            self.update()
        else:
            super().wheelEvent(event)

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            self.drag_start = event.pos()
            self.setCursor(Qt.ClosedHandCursor)
        else:
            super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self.drag_start:
            delta = event.pos() - self.drag_start
            self.offset += delta
            self.drag_start = event.pos()
            self.update()
        else:
            super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if event.button() == Qt.LeftButton and self.drag_start:
            self.drag_start = None
            self.setCursor(Qt.ArrowCursor)
        else:
            super().mouseReleaseEvent(event)

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Escape:
            self.close()
        else:
            super().keyPressEvent(event)


class ImageListDialog(QDialog):
    """图片列表对话框：缩略图 + alt 文本，点击查看大图"""

    def __init__(self, images, parent=None):
        super().__init__(parent)
        self.images = images
        self.thumb_size = 180
        self.setWindowTitle('图片列表')
        self.setModal(True)
        self.setFocusPolicy(Qt.StrongFocus)
        self.resize(900, 650)
        self.setStyleSheet("""
            QDialog { background: #2b2b2b; }
            QLabel { color: #cccccc; }
        """)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(12, 12, 12, 12)

        # 标题
        title_label = QLabel(f'共 {len(images)} 张图片（ESC 关闭）')
        title_label.setStyleSheet("font-size: 16px; color: #eee; padding: 4px;")
        layout.addWidget(title_label)

        # 滚动区域
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setStyleSheet("QScrollArea { border: none; background: #2b2b2b; }")

        container = QWidget()
        container.setStyleSheet("background: #2b2b2b;")
        self.flow_layout = FlowLayout(container)
        self.flow_layout.setSpacing(10)

        for img_info in images:
            self._add_image_card(img_info)

        scroll.setWidget(container)
        layout.addWidget(scroll)

    def _add_image_card(self, img_info):
        """添加一张图片卡片（缩略图 + alt文本）"""
        card = QWidget()
        card.setStyleSheet("background: #3a3a3a; border-radius: 6px;")
        card.setFixedWidth(self.thumb_size + 20)
        card.setCursor(Qt.PointingHandCursor)

        card_layout = QVBoxLayout(card)
        card_layout.setContentsMargins(8, 8, 8, 8)
        card_layout.setSpacing(6)

        # 缩略图
        thumb_label = QLabel()
        thumb_label.setFixedSize(self.thumb_size, self.thumb_size)
        thumb_label.setAlignment(Qt.AlignCenter)
        thumb_label.setStyleSheet("background: #222; border-radius: 3px;")

        try:
            pix = QPixmap()
            pix.loadFromData(img_info['data'])
            if not pix.isNull():
                scaled = pix.scaled(
                    self.thumb_size - 10, self.thumb_size - 10,
                    Qt.KeepAspectRatio, Qt.SmoothTransformation
                )
                thumb_label.setPixmap(scaled)
        except Exception:
            thumb_label.setText('(加载失败)')

        card_layout.addWidget(thumb_label)

        # alt 文本
        alt_text = img_info.get('alt', '') or '(无描述)'
        alt_label = QLabel(alt_text)
        alt_label.setWordWrap(True)
        alt_label.setMaximumWidth(self.thumb_size)
        alt_label.setStyleSheet("color: #aaa; font-size: 12px; background: transparent;")
        alt_label.setAlignment(Qt.AlignCenter)
        card_layout.addWidget(alt_label)

        card.mousePressEvent = lambda e, info=img_info: self._on_image_click(info)
        thumb_label.mousePressEvent = lambda e, info=img_info: self._on_image_click(info)

        self.flow_layout.addWidget(card)

    def _on_image_click(self, img_info):
        """点击图片 → 打开查看器"""
        try:
            pix = QPixmap()
            pix.loadFromData(img_info['data'])
            if not pix.isNull():
                title = img_info.get('alt', '') or '图片查看'
                viewer = ImageViewer(pix, title, self)
                viewer.exec_()
        except Exception as e:
            print(f"[ImageListDialog] 打开图片失败: {e}")

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Escape:
            self.close()
        else:
            super().keyPressEvent(event)


class FootnotePopupViewer(QDialog):
    """脚注内容弹窗查看器"""

    def __init__(self, marker, content_html, parent=None):
        super().__init__(parent)
        self.setWindowTitle(f'脚注: {marker}')
        self.setWindowFlags(Qt.Window | Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint)
        self.setModal(True)
        self.setFocusPolicy(Qt.StrongFocus)

        screen = QApplication.primaryScreen().geometry()
        self.resize(min(700, screen.width() - 100), min(500, screen.height() - 100))

        # 居中
        self.move(
            (screen.width() - self.width()) // 2,
            (screen.height() - self.height()) // 2,
        )

        self.setStyleSheet("""
            QDialog { background: #2b2b2b; border: 2px solid #555; border-radius: 8px; }
        """)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(16, 16, 16, 16)

        # 标题栏
        header = QLabel(f'脚注 [{marker}]')
        header.setStyleSheet("color: #f0c040; font-size: 18px; font-weight: bold;")
        layout.addWidget(header)

        # 分隔线
        sep = QFrame()
        sep.setFrameShape(QFrame.HLine)
        sep.setStyleSheet("color: #555;")
        layout.addWidget(sep)

        # 内容
        content = QTextBrowser()
        content.setOpenExternalLinks(True)
        content.setStyleSheet("""
            QTextBrowser {
                background: #1e1e1e;
                color: #ddd;
                font-size: 15px;
                border: none;
                padding: 8px;
                line-height: 1.6;
            }
        """)
        content.setHtml(content_html)
        layout.addWidget(content)

        # 提示
        hint = QLabel('ESC 关闭')
        hint.setStyleSheet("color: #666; font-size: 12px;")
        hint.setAlignment(Qt.AlignRight)
        layout.addWidget(hint)

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Escape:
            self.close()
        else:
            super().keyPressEvent(event)


class FootnoteListDialog(QDialog):
    """脚注列表对话框：左标记 + 右内容，点击查看"""

    def __init__(self, footnotes, parent=None):
        super().__init__(parent)
        self.footnotes = footnotes
        self.setWindowTitle('脚注列表')
        self.setModal(True)
        self.setFocusPolicy(Qt.StrongFocus)

        # 窗口大小：占屏幕 60% 宽度（同目录窗口）
        screen_geo = QApplication.primaryScreen().availableGeometry()
        w = int(screen_geo.width() * 0.6)
        h = int(screen_geo.height() * 0.6)
        self.setGeometry(
            screen_geo.x() + (screen_geo.width() - w) // 2,
            screen_geo.y() + (screen_geo.height() - h) // 2,
            w, h,
        )

        self.setStyleSheet("""
            QDialog { background: #2b2b2b; }
            QLabel { color: #cccccc; }
        """)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(12, 12, 12, 12)

        # 标题
        title_label = QLabel(f'共 {len(footnotes)} 条脚注（ESC 关闭）')
        title_label.setStyleSheet("font-size: 16px; color: #eee; padding: 4px;")
        layout.addWidget(title_label)

        # 滚动区域
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setStyleSheet("QScrollArea { border: none; background: #2b2b2b; }")

        container = QWidget()
        container.setStyleSheet("background: #2b2b2b;")
        container_layout = QVBoxLayout(container)
        container_layout.setSpacing(8)

        idx = 1
        for fn in footnotes:
            self._add_footnote_row(container_layout, fn, idx)
            idx += 1

        scroll.setWidget(container)
        layout.addWidget(scroll)

    def _add_footnote_row(self, parent_layout, fn, idx):
        """添加一行脚注：左边标记，右边内容预览"""
        row = QWidget()
        row.setStyleSheet("background: #3a3a3a; border-radius: 6px;")
        row.setCursor(Qt.PointingHandCursor)
        row.setMinimumHeight(50)

        row_layout = QHBoxLayout(row)
        row_layout.setContentsMargins(12, 8, 12, 8)
        row_layout.setSpacing(12)

        # 左侧：脚注标记（紧凑序号 or 图）
        marker_html = fn.get('marker_html', '')
        is_img_marker = '<img' in marker_html.lower()

        marker_widget = QLabel()
        marker_widget.setAlignment(Qt.AlignCenter)
        marker_widget.setFixedWidth(50)
        if is_img_marker:
            marker_widget.setText('[图]')
        else:
            marker_widget.setText(f'[{idx}]')
        marker_widget.setStyleSheet("""
            color: #f0c040;
            font-size: 23px;
            font-weight: bold;
            background: #444;
            border-radius: 4px;
            padding: 6px;
        """)

        row_layout.addWidget(marker_widget)

        # 右侧：脚注内容预览
        content_widget = QLabel()
        content_widget.setText(fn.get('content', ''))
        content_widget.setWordWrap(True)
        content_widget.setStyleSheet("""
            color: #bbb;
            font-size: 23px;
            background: transparent;
            padding: 4px;
        """)
        row_layout.addWidget(content_widget, 1)

        # 点击事件
        row.mousePressEvent = lambda e, f=fn: self._on_footnote_click(f)
        marker_widget.mousePressEvent = lambda e, f=fn: self._on_footnote_click(f)
        content_widget.mousePressEvent = lambda e, f=fn: self._on_footnote_click(f)

        parent_layout.addWidget(row)

    def _on_footnote_click(self, fn):
        """点击脚注 → 弹出查看器"""
        viewer = FootnotePopupViewer(
            fn.get('marker', '?'),
            fn.get('content_html', fn.get('content', '')),
            self
        )
        viewer.exec_()

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Escape:
            self.close()
        else:
            super().keyPressEvent(event)


if __name__ == "__main__":
    # === 修复：DPI 设置必须在 QApplication 之前 ===
    # QApplication.setAttribute(Qt.AA_EnableHighDpiScaling)
    # QApplication.setAttribute(Qt.AA_UseHighDpiPixmaps)
    # ===========================================

    app = QApplication(sys.argv)
    initial_pdf = sys.argv[1] if len(sys.argv) > 1 else None
    window = TactiReader(initial_pdf)
    window.show()
    sys.exit(app.exec_())
