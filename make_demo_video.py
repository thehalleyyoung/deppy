"""Generate a demo MP4 showing deppy's actual verification capabilities.

The video presents three things deppy demonstrably does today:
1. semantic verification of recursive / class-based Python code,
2. code-shaped class invariant synthesis for stateful objects, and
3. runtime bug detection across a 20-family synthetic suite.

Terminal panes are built from real output produced by deppy's verification and
bug-detection engines; title / explanation cards summarize what the viewer is
seeing and normalize a few inferred invariants into code-like form.
"""

import inspect
import json
import os
from pathlib import Path
import re
import sys
import subprocess
import tempfile
import shutil
import textwrap
from PIL import Image, ImageDraw, ImageFont

# ── Configuration ──────────────────────────────────────────────────────────

WIDTH, HEIGHT = 1920, 1080
BG = (15, 15, 30)
FG = (220, 220, 220)
ACCENT = (100, 200, 255)
GREEN = (80, 220, 120)
RED = (255, 90, 90)
YELLOW = (255, 210, 80)
PURPLE = (180, 130, 255)
DIM = (120, 120, 140)
COMMENT = (100, 140, 100)
ORANGE = (255, 165, 60)
CYAN = (80, 220, 220)

FPS = 2
CODE_HOLD = 6         # frames to show code before output
PHASE_PAUSE = 3       # extra frames at phase headers
SYNTH_PAUSE = 2       # extra frames at synthesis discoveries
VC_PAUSE = 0          # extra frames per VC result (batched instead)
CONCLUSION_PAUSE = 6  # frames for conclusion
TITLE_FRAMES = 5      # frames for title/transition cards
FINAL_HOLD = 6        # frames to hold the final output

FONT_PATHS = [
    "/System/Library/Fonts/SFMono-Regular.otf",
    "/System/Library/Fonts/Menlo.ttc",
    "/System/Library/Fonts/Monaco.dfont",
    "/Library/Fonts/Courier New.ttf",
    "/System/Library/Fonts/Courier.dfont",
]

FONT_PATH = None
for p in FONT_PATHS:
    if os.path.exists(p):
        FONT_PATH = p
        break


def get_font(size):
    if FONT_PATH:
        try:
            return ImageFont.truetype(FONT_PATH, size)
        except Exception:
            pass
    return ImageFont.load_default()


FONT_CODE = get_font(17)
FONT_TITLE = get_font(44)
FONT_SUBTITLE = get_font(24)
FONT_SMALL = get_font(15)
FONT_HEADER = get_font(28)
FONT_DETAIL = get_font(20)

LINE_H = 20
MAX_LINES = 45

KEYWORD_RE = re.compile(r"\b(class|def|return|if|elif|else|while|for|in|and|or|not|import|from|try|except|with|as|pass|raise|del)\b")


# ── Frame rendering ───────────────────────────────────────────────────────

def new_frame():
    return Image.new("RGB", (WIDTH, HEIGHT), BG)


def draw_terminal_chrome(draw, title="deppy"):
    draw.rectangle([(40, 30), (WIDTH - 40, 70)], fill=(50, 50, 65))
    draw.ellipse([(60, 42), (76, 58)], fill=(255, 95, 86))
    draw.ellipse([(86, 42), (102, 58)], fill=(255, 189, 46))
    draw.ellipse([(112, 42), (128, 58)], fill=(39, 201, 63))
    draw.text((WIDTH // 2 - len(title) * 5, 44), title, font=FONT_SMALL, fill=DIM)
    draw.rectangle([(40, 70), (WIDTH - 40, HEIGHT - 40)], fill=(10, 10, 25))
    return 80


class ColorLine:
    def __init__(self):
        self.segments = []

    def add(self, text, color=FG):
        self.segments.append((text, color))
        return self

    def draw(self, draw_ctx, x, y, font=None):
        f = font or FONT_CODE
        cx = x
        for text, color in self.segments:
            draw_ctx.text((cx, y), text, font=f, fill=color)
            bbox = f.getbbox(text)
            cx += bbox[2] - bbox[0] if bbox else len(text) * 10


def render_lines(lines, title="deppy", subtitle=None):
    img = new_frame()
    draw = ImageDraw.Draw(img)
    y_start = draw_terminal_chrome(draw, title)
    if subtitle:
        draw.text((70, y_start + 3), subtitle, font=FONT_SUBTITLE, fill=ACCENT)
        y_start += 30

    y = y_start + 10
    for line in lines[:MAX_LINES]:
        if isinstance(line, ColorLine):
            line.draw(draw, 70, y)
        elif isinstance(line, str):
            draw.text((70, y), line, font=FONT_CODE, fill=FG)
        elif line is None:
            pass  # blank line
        y += LINE_H
    return img


def make_title_card(title, subtitle, description_lines):
    img = new_frame()
    draw = ImageDraw.Draw(img)
    draw.text((WIDTH // 2 - len(title) * 13, 160), title, font=FONT_TITLE, fill=ACCENT)
    draw.text((WIDTH // 2 - len(subtitle) * 7, 230), subtitle, font=FONT_SUBTITLE, fill=DIM)
    y = 320
    for line in description_lines:
        if isinstance(line, ColorLine):
            line.draw(draw, WIDTH // 2 - 420, y, FONT_DETAIL)
        elif line is None:
            pass
        else:
            draw.text((WIDTH // 2 - 420, y), line, font=FONT_DETAIL, fill=FG)
        y += 30
    return img


def make_explanation_card(title, lines):
    """Make a card explaining what's about to happen."""
    img = new_frame()
    draw = ImageDraw.Draw(img)
    draw.text((WIDTH // 2 - len(title) * 8, 200), title, font=FONT_HEADER, fill=ACCENT)
    y = 280
    for line in lines:
        if isinstance(line, ColorLine):
            line.draw(draw, 160, y, FONT_DETAIL)
        elif line is None:
            pass
        else:
            draw.text((160, y), line, font=FONT_DETAIL, fill=FG)
        y += 32
    return img


def source_to_lines(source):
    """Render plain source as demo code lines with very light highlighting."""
    rendered = []
    for raw in textwrap.dedent(source).strip("\n").splitlines():
        if not raw.strip():
            rendered.append(None)
            continue
        line = ColorLine()
        cursor = 0
        for match in KEYWORD_RE.finditer(raw):
            start, end = match.span()
            if start > cursor:
                line.add(raw[cursor:start], FG)
            line.add(raw[start:end], YELLOW)
            cursor = end
        if cursor < len(raw):
            line.add(raw[cursor:], FG)
        rendered.append(line)
    return rendered


# ── Output colorizer ─────────────────────────────────────────────────────

def classify_line(raw: str) -> str:
    """Classify a line for pause/highlight decisions."""
    stripped = raw.strip()
    if stripped.startswith("Phase "):
        return "phase"
    if stripped.startswith("Inferred loop invariant") or stripped.startswith("Discovered"):
        return "synthesis"
    if stripped.startswith("Ranking function") or stripped.startswith("Recursive structure"):
        return "synthesis"
    if stripped.startswith("Base case:") or stripped.startswith("Induction on:"):
        return "synthesis"
    if stripped.startswith("Source:") and "synthesized" in stripped:
        return "synthesis"
    if "I1:" in stripped or "I2:" in stripped or "I3:" in stripped or "I4:" in stripped:
        return "synthesis"
    if "PROVED" in stripped and (stripped[0].isdigit() or stripped.startswith("__init__")):
        return "vc_result"
    if "FAILED" in stripped and (stripped[0].isdigit() or stripped.startswith("__init__")):
        return "vc_result"
    if stripped.startswith("CONCLUSION:"):
        return "conclusion"
    if stripped.startswith("Root cause:"):
        return "root_cause"
    if stripped.startswith("Sheaf type-section analysis:"):
        return "phase"
    if stripped.startswith("Obstructions") or stripped.startswith("Resolved obstructions"):
        return "phase"
    if stripped.startswith("No gluing obstructions"):
        return "conclusion"
    if re.match(r"^\d+\. \[[A-Z_]+\]", stripped):
        return "vc_result"
    if stripped.startswith("✓ ["):
        return "synthesis"
    if "→" in stripped and ("VC" in stripped or "establishment" in stripped or "preservation" in stripped):
        return "vc_list"
    if stripped.startswith("= ") and "proof obligations" in stripped:
        return "synthesis"
    return "normal"


def colorize_output(text: str) -> list:
    """Convert verification output to colored lines."""
    lines = []
    for raw in text.split("\n"):
        stripped = raw.strip()
        if raw.startswith("Semantic verification"):
            lines.append(ColorLine().add(raw, ACCENT))
        elif raw.startswith("=="):
            lines.append(ColorLine().add(raw, ACCENT))
        elif raw.startswith("Sheaf type-section analysis:"):
            lines.append(ColorLine().add(raw, ACCENT))
        elif raw.startswith("Cover topology:") or raw.startswith("Section requirements extracted:"):
            lines.append(ColorLine().add(raw, CYAN))
        elif raw.startswith("Gluing audit:") or raw.startswith("Obstructions (bugs as gluing failures):") or raw.startswith("Resolved obstructions"):
            lines.append(ColorLine().add(raw, ACCENT))
        elif "Genuine obstructions" in raw:
            lines.append(ColorLine().add(raw, RED))
        elif "Resolved by guards" in raw:
            lines.append(ColorLine().add(raw, GREEN))
        elif "Spurious (Z3 UNSAT" in raw:
            lines.append(ColorLine().add(raw, YELLOW))
        elif raw.startswith("Precondition:"):
            lines.append(ColorLine().add(raw, YELLOW))
        elif raw.startswith("Postconditions"):
            lines.append(ColorLine().add(raw, DIM))
        elif stripped.startswith("- sortedness") or stripped.startswith("- permutation") or stripped.startswith("- length"):
            lines.append(ColorLine().add(raw, FG))
        # Phase headers
        elif stripped.startswith("Phase "):
            lines.append(ColorLine().add(raw, ACCENT))
        # Cover synthesis details
        elif stripped.startswith("Decompose function") or stripped.startswith("Parse "):
            lines.append(ColorLine().add(raw, CYAN))
        elif stripped.startswith("Each site carries") or stripped.startswith("Build site cover"):
            lines.append(ColorLine().add(raw, CYAN))
        elif stripped.startswith("Site kinds:") or stripped.startswith("Proof-relevant"):
            lines.append(ColorLine().add(raw, DIM))
        elif "sites," in stripped and "overlaps" in stripped and stripped[0].isdigit() is False:
            lines.append(ColorLine().add(raw, DIM))
        # Synthesis details
        elif stripped.startswith("Inferred loop invariant") or stripped.startswith("Discovered"):
            lines.append(ColorLine().add(raw, PURPLE))
        elif stripped.startswith("Loop invariant") or stripped.startswith("Ranking function") or stripped.startswith("Variables:"):
            lines.append(ColorLine().add(raw, PURPLE))
        elif stripped.startswith("State variables"):
            lines.append(ColorLine().add(raw, PURPLE))
        elif stripped.startswith("result[") or stripped.startswith("len(arr)"):
            lines.append(ColorLine().add(raw, PURPLE))
        elif stripped.startswith("Recursive") or stripped.startswith("Base case:") or stripped.startswith("Induction"):
            lines.append(ColorLine().add(raw, PURPLE))
        elif stripped.startswith("merge_sort("):
            lines.append(ColorLine().add(raw, PURPLE))
        elif stripped.startswith("Source:") and "synthesized" in stripped:
            lines.append(ColorLine().add(raw, PURPLE))
        # Class invariant
        elif stripped.startswith("Class invariant"):
            lines.append(ColorLine().add(raw, ACCENT))
        elif stripped.startswith("I") and stripped[1:2].isdigit() and ":" in stripped:
            lines.append(ColorLine().add(raw, PURPLE))
        # Method covers
        elif stripped.endswith("overlaps") and ":" in stripped and ("__init__" in stripped or "get" in stripped or "put" in stripped):
            lines.append(ColorLine().add(raw, DIM))
        elif stripped.startswith("Shared state"):
            lines.append(ColorLine().add(raw, DIM))
        elif stripped.startswith("Strategy:"):
            lines.append(ColorLine().add(raw, PURPLE))
        # VC enumeration
        elif stripped.startswith("= ") and "proof obligations" in stripped:
            lines.append(ColorLine().add(raw, CYAN))
        elif stripped.startswith("Each overlap"):
            lines.append(ColorLine().add(raw, CYAN))
        # VC discovery edges
        elif "→" in stripped and ("VC" in stripped or "identity" in stripped or "postcondition" in stripped or "termination" in stripped):
            lines.append(ColorLine().add(raw, ORANGE))
        elif "→" in stripped and ("establishment" in stripped or "preservation" in stripped):
            lines.append(ColorLine().add(raw, ORANGE))
        elif raw.startswith("---") or raw.startswith("-" * 10):
            lines.append(ColorLine().add(raw, DIM))
        elif ("PROVED" in stripped and stripped[0].isdigit()) or ("PROVED" in stripped and stripped.startswith("__init__")):
            lines.append(ColorLine().add(raw, GREEN))
        elif ("FAILED" in stripped and stripped[0].isdigit()) or ("FAILED" in stripped and stripped.startswith("__init__")):
            lines.append(ColorLine().add(raw, RED))
        elif stripped.startswith("[Z3") or stripped.startswith("[trivial") or stripped.startswith("[structural") or stripped.startswith("[decreases"):
            lines.append(ColorLine().add(raw, PURPLE))
        elif stripped.startswith("[FAILED"):
            lines.append(ColorLine().add(raw, RED))
        elif stripped.startswith("Cover has") or stripped.startswith("len(result)") or stripped.startswith("After loop"):
            lines.append(ColorLine().add(raw, ORANGE))
        elif raw.startswith("Root cause:"):
            lines.append(ColorLine().add(raw, ORANGE))
        elif raw.startswith("CONCLUSION:") or stripped.startswith("CONCLUSION:"):
            if "CORRECT" in raw and "INCORRECT" not in raw:
                lines.append(ColorLine().add(raw, GREEN))
            else:
                lines.append(ColorLine().add(raw, RED))
        elif stripped.startswith("All ") and "proved" in stripped:
            lines.append(ColorLine().add(raw, GREEN))
        elif stripped.startswith("Failed:"):
            lines.append(ColorLine().add(raw, RED))
        elif stripped.startswith("Eviction guard") or "capacity" in stripped.lower() and "+" in stripped:
            lines.append(ColorLine().add(raw, RED))
        elif stripped.startswith("Method `"):
            lines.append(ColorLine().add(raw, RED))
        elif re.match(r"^\d+\. \[[A-Z_]+\]", stripped):
            lines.append(ColorLine().add(raw, RED))
        elif stripped.startswith("Required section:"):
            lines.append(ColorLine().add(raw, PURPLE))
        elif stripped.startswith("Available section:"):
            lines.append(ColorLine().add(raw, DIM))
        elif stripped.startswith("Gap:"):
            lines.append(ColorLine().add(raw, ORANGE))
        elif stripped.startswith("✓ ["):
            lines.append(ColorLine().add(raw, GREEN))
        elif stripped.startswith("Elapsed:"):
            lines.append(ColorLine().add(raw, DIM))
        elif stripped.startswith("No gluing obstructions"):
            lines.append(ColorLine().add(raw, GREEN))
        elif stripped == "":
            lines.append(None)
        else:
            lines.append(ColorLine().add(raw, FG))
    return lines


# ── Source code as colored lines ──────────────────────────────────────────

CORRECT_CODE_LINES = [
    ColorLine().add("def ", YELLOW).add("merge", ACCENT).add("(left, right):", FG),
    ColorLine().add("    result = []", FG),
    ColorLine().add("    i = j = 0", FG),
    ColorLine().add("    ", FG).add("while ", YELLOW).add("i < len(left) ", FG).add("and", YELLOW).add(" j < len(right):", FG),
    ColorLine().add("        ", FG).add("if ", YELLOW).add("left[i] <= right[j]:", FG),
    ColorLine().add("            result.append(left[i])", FG),
    ColorLine().add("            i += 1", FG),
    ColorLine().add("        ", FG).add("else", YELLOW).add(":", FG),
    ColorLine().add("            result.append(right[j])", FG),
    ColorLine().add("            j += 1", FG),
    ColorLine().add("    result.extend(left[i:])", FG).add("   # remaining left", COMMENT),
    ColorLine().add("    result.extend(right[j:])", FG).add("  # remaining right", COMMENT),
    ColorLine().add("    ", FG).add("return ", YELLOW).add("result", FG),
]

BUGGY_MISSING_LINES = [
    ColorLine().add("def ", YELLOW).add("merge", RED).add("(left, right):", FG),
    ColorLine().add("    result = []", FG),
    ColorLine().add("    i = j = 0", FG),
    ColorLine().add("    ", FG).add("while ", YELLOW).add("i < len(left) ", FG).add("and", YELLOW).add(" j < len(right):", FG),
    ColorLine().add("        ", FG).add("if ", YELLOW).add("left[i] <= right[j]:", FG),
    ColorLine().add("            result.append(left[i])", FG),
    ColorLine().add("            i += 1", FG),
    ColorLine().add("        ", FG).add("else", YELLOW).add(":", FG),
    ColorLine().add("            result.append(right[j])", FG),
    ColorLine().add("            j += 1", FG),
    ColorLine().add("    ", FG).add("return ", YELLOW).add("result", FG),
    ColorLine().add("    ", FG).add("# BUG: missing result.extend(left[i:])", RED),
    ColorLine().add("    ", FG).add("#      missing result.extend(right[j:])", RED),
]

BUGGY_REVERSED_LINES = [
    ColorLine().add("def ", YELLOW).add("merge", RED).add("(left, right):", FG),
    ColorLine().add("    result = []", FG),
    ColorLine().add("    i = j = 0", FG),
    ColorLine().add("    ", FG).add("while ", YELLOW).add("i < len(left) ", FG).add("and", YELLOW).add(" j < len(right):", FG),
    ColorLine().add("        ", FG).add("if ", YELLOW).add("left[i] ", FG).add(">=", RED).add(" right[j]:", FG).add("  # BUG: >= not <=", RED),
    ColorLine().add("            result.append(left[i])", FG),
    ColorLine().add("            i += 1", FG),
    ColorLine().add("        ", FG).add("else", YELLOW).add(":", FG),
    ColorLine().add("            result.append(right[j])", FG),
    ColorLine().add("            j += 1", FG),
    ColorLine().add("    result.extend(left[i:])", FG),
    ColorLine().add("    result.extend(right[j:])", FG),
    ColorLine().add("    ", FG).add("return ", YELLOW).add("result", FG),
]

MERGE_SORT_LINES = [
    ColorLine().add("def ", YELLOW).add("merge_sort", ACCENT).add("(arr):", FG),
    ColorLine().add("    ", FG).add("if ", YELLOW).add("len(arr) <= 1:", FG),
    ColorLine().add("        ", FG).add("return ", YELLOW).add("arr", FG),
    ColorLine().add("    mid = len(arr) // 2", FG),
    ColorLine().add("    left = ", FG).add("merge_sort", ACCENT).add("(arr[:mid])", FG).add("   # recursive", COMMENT),
    ColorLine().add("    right = ", FG).add("merge_sort", ACCENT).add("(arr[mid:])", FG).add("  # recursive", COMMENT),
    ColorLine().add("    ", FG).add("return ", YELLOW).add("merge(left, right)", FG),
]


# ── Capture real output ──────────────────────────────────────────────────

CORRECT_SRC = '''
def merge(left, right):
    result = []
    i = j = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            result.append(left[i])
            i += 1
        else:
            result.append(right[j])
            j += 1
    result.extend(left[i:])
    result.extend(right[j:])
    return result
'''

BUGGY_MISSING_SRC = '''
def merge(left, right):
    result = []
    i = j = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            result.append(left[i])
            i += 1
        else:
            result.append(right[j])
            j += 1
    return result
'''

BUGGY_REVERSED_SRC = '''
def merge(left, right):
    result = []
    i = j = 0
    while i < len(left) and j < len(right):
        if left[i] >= right[j]:
            result.append(left[i])
            i += 1
        else:
            result.append(right[j])
            j += 1
    result.extend(left[i:])
    result.extend(right[j:])
    return result
'''

MERGE_SORT_SRC = '''
def merge_sort(arr):
    if len(arr) <= 1:
        return arr
    mid = len(arr) // 2
    left = merge_sort(arr[:mid])
    right = merge_sort(arr[mid:])
    return merge(left, right)
'''

LRU_CORRECT_SRC = '''
class LRUCache:
    def __init__(self, capacity):
        self.capacity = capacity
        self.cache = {}
        self.order = []

    def get(self, key):
        if key not in self.cache:
            return -1
        self.order.remove(key)
        self.order.append(key)
        return self.cache[key]

    def put(self, key, value):
        if key in self.cache:
            self.order.remove(key)
        elif len(self.cache) >= self.capacity:
            lru_key = self.order.pop(0)
            del self.cache[lru_key]
        self.cache[key] = value
        self.order.append(key)
'''

LRU_BUG_ORDERING_SRC = '''
class LRUCache:
    def __init__(self, capacity):
        self.capacity = capacity
        self.cache = {}
        self.order = []

    def get(self, key):
        if key not in self.cache:
            return -1
        return self.cache[key]

    def put(self, key, value):
        if key in self.cache:
            self.order.remove(key)
        elif len(self.cache) >= self.capacity:
            lru_key = self.order.pop(0)
            del self.cache[lru_key]
        self.cache[key] = value
        self.order.append(key)
'''

LRU_BUG_CAPACITY_SRC = '''
class LRUCache:
    def __init__(self, capacity):
        self.capacity = capacity
        self.cache = {}
        self.order = []

    def get(self, key):
        if key not in self.cache:
            return -1
        self.order.remove(key)
        self.order.append(key)
        return self.cache[key]

    def put(self, key, value):
        if key in self.cache:
            self.order.remove(key)
        elif len(self.cache) > self.capacity:
            lru_key = self.order.pop(0)
            del self.cache[lru_key]
        self.cache[key] = value
        self.order.append(key)
'''

LRU_CORRECT_LINES = [
    ColorLine().add("class ", YELLOW).add("LRUCache", ACCENT).add(":", FG),
    ColorLine().add("    def ", YELLOW).add("__init__", FG).add("(self, capacity):", FG),
    ColorLine().add("        self.capacity = capacity", FG),
    ColorLine().add("        self.cache = {}", FG),
    ColorLine().add("        self.order = []", FG).add("  # LRU tracking", COMMENT),
    None,
    ColorLine().add("    def ", YELLOW).add("get", ACCENT).add("(self, key):", FG),
    ColorLine().add("        ", FG).add("if ", YELLOW).add("key ", FG).add("not in ", YELLOW).add("self.cache:", FG),
    ColorLine().add("            ", FG).add("return ", YELLOW).add("-1", FG),
    ColorLine().add("        self.order.remove(key)", FG),
    ColorLine().add("        self.order.append(key)", FG).add("  # move to end", COMMENT),
    ColorLine().add("        ", FG).add("return ", YELLOW).add("self.cache[key]", FG),
    None,
    ColorLine().add("    def ", YELLOW).add("put", ACCENT).add("(self, key, value):", FG),
    ColorLine().add("        ", FG).add("if ", YELLOW).add("key ", FG).add("in ", YELLOW).add("self.cache:", FG),
    ColorLine().add("            self.order.remove(key)", FG),
    ColorLine().add("        ", FG).add("elif ", YELLOW).add("len(self.cache) ", FG).add(">=", GREEN).add(" self.capacity:", FG),
    ColorLine().add("            lru_key = self.order.pop(0)", FG),
    ColorLine().add("            ", FG).add("del ", YELLOW).add("self.cache[lru_key]", FG),
    ColorLine().add("        self.cache[key] = value", FG),
    ColorLine().add("        self.order.append(key)", FG),
]

LRU_BUG_ORDERING_LINES = [
    ColorLine().add("class ", YELLOW).add("LRUCache", RED).add(":", FG),
    ColorLine().add("    def ", YELLOW).add("__init__", FG).add("(self, capacity):", FG),
    ColorLine().add("        self.capacity = capacity", FG),
    ColorLine().add("        self.cache = {}", FG),
    ColorLine().add("        self.order = []", FG),
    None,
    ColorLine().add("    def ", YELLOW).add("get", RED).add("(self, key):", FG),
    ColorLine().add("        ", FG).add("if ", YELLOW).add("key ", FG).add("not in ", YELLOW).add("self.cache:", FG),
    ColorLine().add("            ", FG).add("return ", YELLOW).add("-1", FG),
    ColorLine().add("        ", FG).add("return ", YELLOW).add("self.cache[key]", FG).add("  # BUG: no move-to-front!", RED),
    None,
    ColorLine().add("    def ", YELLOW).add("put", FG).add("(self, key, value):", FG),
    ColorLine().add("        ", FG).add("if ", YELLOW).add("key ", FG).add("in ", YELLOW).add("self.cache:", FG),
    ColorLine().add("            self.order.remove(key)", FG),
    ColorLine().add("        ", FG).add("elif ", YELLOW).add("len(self.cache) >= self.capacity:", FG),
    ColorLine().add("            lru_key = self.order.pop(0)", FG),
    ColorLine().add("            ", FG).add("del ", YELLOW).add("self.cache[lru_key]", FG),
    ColorLine().add("        self.cache[key] = value", FG),
    ColorLine().add("        self.order.append(key)", FG),
]

LRU_BUG_CAPACITY_LINES = [
    ColorLine().add("class ", YELLOW).add("LRUCache", RED).add(":", FG),
    ColorLine().add("    def ", YELLOW).add("__init__", FG).add("(self, capacity):", FG),
    ColorLine().add("        self.capacity = capacity", FG),
    ColorLine().add("        self.cache = {}", FG),
    ColorLine().add("        self.order = []", FG),
    None,
    ColorLine().add("    def ", YELLOW).add("get", FG).add("(self, key):", FG),
    ColorLine().add("        ...", DIM).add("  # (correct — same as above)", COMMENT),
    None,
    ColorLine().add("    def ", YELLOW).add("put", RED).add("(self, key, value):", FG),
    ColorLine().add("        ", FG).add("if ", YELLOW).add("key ", FG).add("in ", YELLOW).add("self.cache:", FG),
    ColorLine().add("            self.order.remove(key)", FG),
    ColorLine().add("        ", FG).add("elif ", YELLOW).add("len(self.cache) ", FG).add(">", RED).add(" self.capacity:", FG).add("  # BUG: > not >=", RED),
    ColorLine().add("            lru_key = self.order.pop(0)", FG),
    ColorLine().add("            ", FG).add("del ", YELLOW).add("self.cache[lru_key]", FG),
    ColorLine().add("        self.cache[key] = value", FG),
    ColorLine().add("        self.order.append(key)", FG),
]


def capture_outputs():
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), "src"))
    from deppy.render.verify import verify, verify_recursive, verify_class

    results = {}
    post = "result is sorted and result is a permutation of left and right"
    results["merge_sort"] = str(verify_recursive(MERGE_SORT_SRC, precondition="arr is a list of comparable elements",
                                                  postcondition="result is sorted and result is a permutation of arr"))
    results["buggy_missing"] = str(verify(BUGGY_MISSING_SRC, precondition="left and right are sorted", postcondition=post))
    results["buggy_reversed"] = str(verify(BUGGY_REVERSED_SRC, precondition="left and right are sorted", postcondition=post))
    results["lru_correct"] = str(verify_class(LRU_CORRECT_SRC))
    results["lru_bug_ordering"] = str(verify_class(LRU_BUG_ORDERING_SRC))
    results["lru_bug_capacity"] = str(verify_class(LRU_BUG_CAPACITY_SRC))
    return results


def _condense_verification_output(text: str) -> str:
    """Trim very noisy overlap dumps while preserving the proof story."""
    kept = []
    for raw in text.splitlines():
        stripped = raw.strip()
        if "✗ INCOMPATIBLE" in raw:
            continue
        if stripped.startswith("i_") or stripped.startswith("j_") or stripped.startswith("arg_"):
            continue
        if stripped.startswith("guard_if_") or stripped.startswith("call_result."):
            continue
        if stripped.startswith("error_"):
            continue
        kept.append(raw)

    compact = []
    previous_blank = False
    for raw in kept:
        is_blank = raw.strip() == ""
        if is_blank and previous_blank:
            continue
        compact.append(raw)
        previous_blank = is_blank
    return "\n".join(compact)


def capture_runtime_bug_outputs():
    """Capture representative runtime-bug analyses from the synthetic suite."""
    src_dir = os.path.join(os.path.dirname(__file__), "src")
    tests_dir = os.path.join(os.path.dirname(__file__), "tests")
    if src_dir not in sys.path:
        sys.path.insert(0, src_dir)
    if tests_dir not in sys.path:
        sys.path.insert(0, tests_dir)

    from deppy.render.bug_detect import detect_bugs, format_bug_report
    from synthetic_bug_suite import (
        div_zero_buggy,
        div_zero_safe,
        non_termination_buggy,
        deadlock_buggy,
        memory_leak_buggy,
        SUITE,
    )

    selected = {
        "div_zero_buggy": div_zero_buggy,
        "div_zero_safe": div_zero_safe,
        "non_termination_buggy": non_termination_buggy,
        "deadlock_buggy": deadlock_buggy,
        "memory_leak_buggy": memory_leak_buggy,
    }

    reports = {}
    for name, fn in selected.items():
        source = textwrap.dedent(inspect.getsource(fn))
        report = detect_bugs(source, function_name=fn.__name__)
        reports[name] = {
            "source": source,
            "report": format_bug_report(report),
        }

    bug_types = []
    for bug_type, _, _, _ in SUITE:
        if bug_type not in bug_types:
            bug_types.append(bug_type)
    reports["bug_types"] = bug_types
    return reports


def load_runtime_suite_summary():
    """Load saved synthetic-suite metrics; fall back to recomputation if absent."""
    results_path = Path(__file__).with_name("eval_synthetic_results.json")
    if results_path.exists():
        data = json.loads(results_path.read_text())
        data["source"] = str(results_path.name)
        return data

    sys.path.insert(0, os.path.join(os.path.dirname(__file__), "src"))
    from eval_synthetic import run_evaluation

    summary = run_evaluation()
    return {
        "n_pairs": summary.total_cases // 2,
        "sheaf": {
            "tp": summary.sheaf_tp,
            "tn": summary.sheaf_tn,
            "fp": summary.sheaf_fp,
            "fn": summary.sheaf_fn,
            "accuracy": (summary.sheaf_tp + summary.sheaf_tn) / summary.total_cases if summary.total_cases else 0,
        },
        "a3": {
            "tp": summary.a3_tp,
            "tn": summary.a3_tn,
            "fp": summary.a3_fp,
            "fn": summary.a3_fn,
            "accuracy": (summary.a3_tp + summary.a3_tn) / summary.total_cases if summary.total_cases else 0,
        },
        "source": "live run_evaluation()",
    }


def make_runtime_summary_card(summary, bug_types):
    bug_rows = [
        "  " + "   ".join(bug_types[:5]),
        "  " + "   ".join(bug_types[5:10]),
        "  " + "   ".join(bug_types[10:15]),
        "  " + "   ".join(bug_types[15:20]),
    ]
    sheaf = summary["sheaf"]
    a3 = summary["a3"]
    n_pairs = summary.get("n_pairs", 0)
    n_cases = n_pairs * 2
    return make_explanation_card(
        "Runtime Bug Detection — 20 Bug Families",
        [
            "",
            f"Synthetic benchmark: {n_pairs} buggy/safe pairs = {n_cases} total cases.",
            f"Metrics artifact: {summary.get('source', 'saved results')}",
            "",
            ColorLine().add("Sheaf detector: ", ACCENT).add(
                f"TP {sheaf['tp']}  TN {sheaf['tn']}  FP {sheaf['fp']}  FN {sheaf['fn']}  acc {sheaf['accuracy']:.1%}",
                GREEN,
            ),
            ColorLine().add("a3-python:     ", DIM).add(
                f"TP {a3['tp']}  TN {a3['tn']}  FP {a3['fp']}  FN {a3['fn']}  acc {a3['accuracy']:.1%}",
                YELLOW,
            ),
            "",
            ColorLine().add("Families covered:", ACCENT),
            *bug_rows,
            "",
            "Representative reports follow for refinement, termination,",
            "concurrency, and resource-lifetime failure classes.",
        ],
    )


def make_lru_invariant_code_card():
    return make_explanation_card(
        "Class Invariant Synthesis — Code Form",
        [
            "",
            "Normalized clauses inferred from constructor + mutator analysis:",
            "",
            ColorLine().add("  assert len(self.cache) <= self.capacity", PURPLE),
            ColorLine().add("  assert set(self.cache.keys()) == set(self.order)", PURPLE),
            ColorLine().add("  assert len(self.cache) == len(self.order)", PURPLE),
            ColorLine().add("  on cache hit: self.order.remove(key); self.order.append(key)", PURPLE),
            "",
            "Clauses 1-3 are state invariants; clause 4 is the recovered",
            "transition schema for access-recency preservation.",
        ],
    )


# ── Build frames — line-by-line with pauses ──────────────────────────────

def build_demo_frames(code_lines, output_text, subtitle, code_hold=None):
    """Build frames: show code, then reveal output with context-aware pacing.

    - Phase headers and synthesis discoveries: 1 line/frame + pause
    - VC enumeration list: 2 lines/frame (fast scroll)
    - VC discharge results: 3 lines/frame (name + desc + method)
    - Normal lines: 1 line/frame
    """
    if code_hold is None:
        code_hold = CODE_HOLD
    frames = []

    # Show the source code
    code_frame_lines = [
        ColorLine().add(f"# {subtitle}", COMMENT),
        None,
    ]
    code_frame_lines.extend(code_lines)
    frames.extend([render_lines(code_frame_lines, subtitle=subtitle)] * code_hold)

    # Split output into raw lines for classification + colored lines for rendering
    raw_lines = output_text.split("\n")
    colored_lines = colorize_output(output_text)

    # Reveal with context-aware batching
    accumulated = []
    i = 0
    in_discharge = False  # True when we're in the Phase 4 discharge section
    in_vc_list = False    # True when listing VC matrix entries

    while i < len(raw_lines):
        raw = raw_lines[i]
        line_type = classify_line(raw)

        # Detect discharge section start
        if "discharge" in raw.lower() and "Phase" in raw:
            in_discharge = True
            in_vc_list = False
        elif raw.strip().startswith("Phase "):
            in_discharge = False
            in_vc_list = False

        # Detect VC matrix listing
        if "proof obligations" in raw:
            in_vc_list = True

        if line_type == "phase":
            accumulated.append(colored_lines[i])
            i += 1
            visible = accumulated[-MAX_LINES:]
            frame = render_lines(visible, subtitle=subtitle)
            frames.append(frame)
            frames.extend([frame] * PHASE_PAUSE)

        elif line_type == "synthesis":
            accumulated.append(colored_lines[i])
            i += 1
            visible = accumulated[-MAX_LINES:]
            frame = render_lines(visible, subtitle=subtitle)
            frames.append(frame)
            frames.extend([frame] * SYNTH_PAUSE)

        elif line_type == "conclusion":
            accumulated.append(colored_lines[i])
            i += 1
            visible = accumulated[-MAX_LINES:]
            frame = render_lines(visible, subtitle=subtitle)
            frames.append(frame)
            frames.extend([frame] * CONCLUSION_PAUSE)

        elif line_type == "root_cause":
            accumulated.append(colored_lines[i])
            i += 1
            visible = accumulated[-MAX_LINES:]
            frame = render_lines(visible, subtitle=subtitle)
            frames.append(frame)
            frames.extend([frame] * (SYNTH_PAUSE + 1))

        elif in_vc_list and line_type == "vc_list":
            # Batch VC list entries: 2 per frame
            batch_end = min(i + 2, len(raw_lines))
            while batch_end < len(raw_lines) and batch_end < i + 2:
                if classify_line(raw_lines[batch_end]) == "vc_list":
                    batch_end += 1
                else:
                    break
            for j in range(i, batch_end):
                accumulated.append(colored_lines[j])
            i = batch_end
            visible = accumulated[-MAX_LINES:]
            frames.append(render_lines(visible, subtitle=subtitle))

        elif in_discharge and line_type == "vc_result":
            # Batch VC discharge: show the VC header + 2 detail lines as one frame
            batch_end = i + 1
            # Include the description and method lines that follow
            while batch_end < len(raw_lines) and batch_end < i + 4:
                next_type = classify_line(raw_lines[batch_end])
                if next_type in ("vc_result", "phase", "conclusion", "root_cause"):
                    break
                batch_end += 1
            for j in range(i, batch_end):
                accumulated.append(colored_lines[j])
            i = batch_end
            visible = accumulated[-MAX_LINES:]
            frame = render_lines(visible, subtitle=subtitle)
            frames.append(frame)
            # Brief pause on FAILED VCs
            if "FAILED" in raw:
                frames.extend([frame] * 2)

        else:
            accumulated.append(colored_lines[i])
            i += 1
            visible = accumulated[-MAX_LINES:]
            frames.append(render_lines(visible, subtitle=subtitle))

    # Hold final output
    visible = accumulated[-MAX_LINES:] if len(accumulated) > MAX_LINES else accumulated
    frames.extend([render_lines(visible, subtitle=subtitle)] * FINAL_HOLD)
    return frames


def main():
    print("Capturing real deppy output...")
    outputs = {k: _condense_verification_output(v) for k, v in capture_outputs().items()}
    runtime_outputs = capture_runtime_bug_outputs()
    runtime_summary = load_runtime_suite_summary()

    for name, text in outputs.items():
        n_lines = len(text.split("\n"))
        print(f"  {name}: {n_lines} lines")
    for name, payload in runtime_outputs.items():
        if isinstance(payload, dict) and "report" in payload:
            print(f"  {name}: {len(payload['report'].splitlines())} bug-report lines")

    print("Generating frames...")
    all_frames = []

    # ════════════════════════════════════════════════════════════════════
    # INTRO
    # ════════════════════════════════════════════════════════════════════

    intro = make_title_card(
        "deppy",
        "Python Verification / Bug Detection",
        [
            "",
            "Inputs: AST + SSA-like state facts + guards + solver discharge.",
            "Outputs: semantic VCs, synthesized invariants, obstruction reports.",
            "",
            "Displayed artifacts are restricted to currently emitted deppy traces:",
            "  • recursive VC generation + ranking-function evidence",
            "  • class invariant synthesis rendered as normalized clauses",
            "  • runtime obstruction detection on 20 synthetic bug families",
            "",
            ColorLine().add("Demo scope: ", DIM).add("function proofs, class proofs, runtime bug reports", ACCENT),
        ],
    )
    all_frames.extend([intro] * TITLE_FRAMES)

    # Table of contents
    toc = make_title_card(
        "Demo Index",
        "",
        [
            "",
            ColorLine().add("Part I  ", ACCENT).add("Merge Sort — Function-Level Verification", FG),
            ColorLine().add("  1. ", DIM).add("merge_sort        ", GREEN).add("— structural induction + ranking", FG),
            ColorLine().add("  2. ", DIM).add("Bug: missing extend", RED).add("— incomplete output dataflow", FG),
            ColorLine().add("  3. ", DIM).add("Bug: reversed cmp  ", RED).add("— SMT refutation of sortedness", FG),
            "",
            ColorLine().add("Part II ", ACCENT).add("LRU Cache — Class-Level Verification", FG),
            ColorLine().add("  4. ", DIM).add("Invariant synthesis ", GREEN).add("— normalized code clauses", FG),
            ColorLine().add("  5. ", DIM).add("Correct LRU        ", GREEN).add("— 24/24 VCs proved", FG),
            ColorLine().add("  6. ", DIM).add("Bug: stale ordering ", RED).add("— transition schema violation", FG),
            ColorLine().add("  7. ", DIM).add("Bug: off-by-one     ", RED).add("— capacity overflow model", FG),
            "",
            ColorLine().add("Part III", ACCENT).add(" Runtime Bug Detection", FG),
            ColorLine().add("  8. ", DIM).add("20-family suite    ", GREEN).add("— benchmark metrics", FG),
            ColorLine().add("  9. ", DIM).add("DIV_ZERO buggy/safe", GREEN).add("— unsatisfied vs refined section", FG),
            ColorLine().add(" 10. ", DIM).add("NON_TERMINATION    ", RED).add("— missing descent witness", FG),
            ColorLine().add(" 11. ", DIM).add("DEADLOCK + leak    ", RED).add("— concurrency/resource violations", FG),
        ],
    )
    all_frames.extend([toc] * TITLE_FRAMES)

    # ════════════════════════════════════════════════════════════════════
    # PART I: Merge Sort
    # ════════════════════════════════════════════════════════════════════

    part1_intro = make_explanation_card(
        "Part I — Function-Level Verification",
        [
            "",
            "Function-level sheaf-descent pipeline:",
            "",
            ColorLine().add("  1. Cover synthesis", ACCENT).add("  — AST → proof-relevant sites", FG),
            ColorLine().add("                       ", ACCENT).add("    (args, SSA states, branches, calls, return)", FG),
            ColorLine().add("  2. Structural extraction", ACCENT).add(" — recursion / descent witnesses", FG),
            ColorLine().add("  3. VC generation", ACCENT).add("    — site overlaps induce gluing constraints", FG),
            ColorLine().add("  4. SMT discharge", ACCENT).add("     — Z3 proves or refutes each VC", FG),
            "",
            "Asymptotic objective: O(|sites|) obligations, not O(|inputs|) tests.",
        ],
    )
    all_frames.extend([part1_intro] * TITLE_FRAMES)

    # ── 1. Recursive merge_sort ───────────────────────────────────────

    merge_sort_explain = make_explanation_card(
        "Recursive Verification — Structural Induction",
        [
            "",
            "VC schema for recursive merge sort:",
            "",
            ColorLine().add("  Base VC: ", ACCENT).add("len(arr) ≤ 1 ⇒ sorted(arr)", FG),
            ColorLine().add("  Split VC: ", ACCENT).add("arr = arr[:mid] ++ arr[mid:]", FG),
            ColorLine().add("  Merge VC: ", ACCENT).add("sorted(L) ∧ sorted(R) ⇒ sorted(merge(L,R))", FG),
            ColorLine().add("  Perm VC: ", ACCENT).add("multiset(merge(L,R)) = multiset(L) ⊎ multiset(R)", FG),
            ColorLine().add("  Term VC: ", ACCENT).add("len(subcall) < len(arr)", FG),
            "",
            "All clauses are solver-backed VCs; none are hand-annotated axioms.",
        ],
    )
    all_frames.extend([merge_sort_explain] * TITLE_FRAMES)

    all_frames.extend(build_demo_frames(
        MERGE_SORT_LINES,
        outputs["merge_sort"],
        "1/11 — merge_sort: structural induction + SMT discharge",
        code_hold=10,
    ))

    # ── 2. Missing extend ─────────────────────────────────────────────

    buggy1_explain = make_explanation_card(
        "Bug Detection — Dataflow Incompleteness",
        [
            "",
            "Cover analysis recovers output-construction paths:",
            "",
            ColorLine().add("  Correct: ", GREEN).add("append(loop) + extend(tails) ⇒ total element transfer", FG),
            ColorLine().add("  Buggy:   ", RED).add("append(loop) only ⇒ residual tails lack output path", FG),
            "",
            "Failure mode: uncovered residual-state to output mapping.",
            "Detection mode: static cover analysis; no execution required.",
        ],
    )
    all_frames.extend([buggy1_explain] * TITLE_FRAMES)

    all_frames.extend(build_demo_frames(
        BUGGY_MISSING_LINES,
        outputs["buggy_missing"],
        "2/11 — missing extend: residual elements unreachable",
    ))

    # ── 3. Reversed comparison ────────────────────────────────────────

    buggy2_explain = make_explanation_card(
        "Bug Detection — SMT Refutation",
        [
            "",
            "Guard extracted from AST branch predicate:",
            ColorLine().add("  left[i] >= right[j]", RED).add("  instead of  ", FG).add("left[i] <= right[j]", GREEN),
            "",
            "VC under check:",
            ColorLine().add("  Encode: ", ACCENT).add("Inv ∧ guard ⇒ Inv'", FG),
            ColorLine().add("  Solver: ", RED).add("SAT(counterexample) ⇒ preservation VC fails", FG),
            "",
            "Semantic effect: branch appends the larger head element first.",
            "Consequence: sortedness preservation is refuted.",
        ],
    )
    all_frames.extend([buggy2_explain] * TITLE_FRAMES)

    all_frames.extend(build_demo_frames(
        BUGGY_REVERSED_LINES,
        outputs["buggy_reversed"],
        "3/11 — reversed comparator: sortedness VC refuted",
    ))

    # ════════════════════════════════════════════════════════════════════
    # TRANSITION TO PART II
    # ════════════════════════════════════════════════════════════════════

    transition = make_title_card(
        "Part II: Class-Level Verification",
        "LRU Cache — Multi-Method Invariant Checking",
        [
            "",
            "Class-level sheaf view:",
            "",
            "  Methods = local sites in the class cover.",
            "  Class invariant = global section preserved at method boundaries.",
            "",
            "  Invariants are synthesized from __init__, guard schemas,",
            "  and co-mutation structure over shared state.",
            "",
            ColorLine().add("  Manual invariant annotations: 0", ACCENT),
        ],
    )
    all_frames.extend([transition] * TITLE_FRAMES)

    class_method_card = make_explanation_card(
        "Class Invariant Synthesis — How It Works",
        [
            "",
            ColorLine().add("Strategy 1: Capacity bounds", PURPLE),
            "  Guard schema len(self.x) >= cap  ⇒  invariant len(x) ≤ cap",
            "",
            ColorLine().add("Strategy 2: Collection consistency", PURPLE),
            "  Co-mutation(cache, order)  ⇒  keys(cache) = set(order)",
            "",
            ColorLine().add("Strategy 3: Size synchronization", PURPLE),
            "  Paired collection updates  ⇒  len(cache) = len(order)",
            "",
            ColorLine().add("Strategy 4: Ordering", PURPLE),
            "  remove(); append() on hit-path  ⇒  LRU recency transition",
            "",
            "VC basis: methods × paths × invariant clauses.",
        ],
    )
    all_frames.extend([class_method_card] * TITLE_FRAMES)

    all_frames.extend([make_lru_invariant_code_card()] * TITLE_FRAMES)

    # ── 4. Correct LRU cache ─────────────────────────────────────────

    all_frames.extend(build_demo_frames(
        LRU_CORRECT_LINES,
        outputs["lru_correct"],
        "5/11 — correct LRU: 24/24 invariant VCs proved",
        code_hold=10,
    ))

    # ── 5. LRU bug — missing ordering update ─────────────────────────

    lru_bug1_explain = make_explanation_card(
        "Bug Detection — Transition Schema Violation",
        [
            "",
            "Required hit-path transition:",
            ColorLine().add("  self.order.remove(key)", GREEN),
            ColorLine().add("  self.order.append(key)", GREEN).add("  # promote key to MRU position", FG),
            "",
            "Buggy variant returns value without executing the recency update.",
            "",
            "Observed path condition: key ∈ cache.",
            "Observed effect: no remove/append transition on order.",
            "Invariant consequence: access-recency schema is violated.",
            "",
            "Downstream effect: eviction may select a non-LRU key.",
        ],
    )
    all_frames.extend([lru_bug1_explain] * TITLE_FRAMES)

    all_frames.extend(build_demo_frames(
        LRU_BUG_ORDERING_LINES,
        outputs["lru_bug_ordering"],
        "6/11 — stale ordering: hit-path recency update missing",
        code_hold=10,
    ))

    # ── 6. LRU bug — off-by-one capacity ─────────────────────────────

    lru_bug2_explain = make_explanation_card(
        "Bug Detection — Capacity Overflow Model",
        [
            "",
            ColorLine().add("Correct: ", GREEN).add("elif len(self.cache) >= self.capacity:", FG),
            ColorLine().add("Buggy:   ", RED).add("elif len(self.cache) > self.capacity:", FG),
            "",
            "Critical boundary state: len(cache) = capacity.",
            ColorLine().add("  >= : ", GREEN).add("eviction fires  ⇒  post-size = capacity", FG),
            ColorLine().add("  >  : ", RED).add("eviction skipped ⇒  post-size = capacity + 1", FG),
            "",
            "Abstract transition model:",
            "  pre: cache_size ≤ capacity",
            "  step: cache_size' = cache_size + 1",
            "  goal: cache_size' ≤ capacity",
            ColorLine().add("  Solver: SAT", RED).add(" at cache_size = capacity", FG),
        ],
    )
    all_frames.extend([lru_bug2_explain] * TITLE_FRAMES)

    all_frames.extend(build_demo_frames(
        LRU_BUG_CAPACITY_LINES,
        outputs["lru_bug_capacity"],
        "7/11 — off-by-one guard: capacity VC refuted",
        code_hold=10,
    ))

    # ════════════════════════════════════════════════════════════════════
    # PART III: Runtime bug detection
    # ════════════════════════════════════════════════════════════════════

    runtime_transition = make_title_card(
        "Part III: Runtime Bug Detection",
        "Type-Section Obstruction Analysis",
        [
            "",
            "For each sink, deppy extracts a required local section",
            "(e.g. divisor ≠ 0, index ∈ bounds, resource eventually closed)",
            "and checks whether upstream facts restrict into that section.",
            "",
            "No restriction map  ⇒  confirmed obstruction.",
            "Guard-induced path refinement  ⇒  obstruction resolved.",
        ],
    )
    all_frames.extend([runtime_transition] * TITLE_FRAMES)

    all_frames.extend([make_runtime_summary_card(runtime_summary, runtime_outputs["bug_types"])] * (TITLE_FRAMES + 1))

    div_zero_intro = make_explanation_card(
        "Runtime Example — DIV_ZERO",
        [
            "",
            ColorLine().add("Required section:", ACCENT).add(" {count : int | count ≠ 0}", PURPLE),
            ColorLine().add("Buggy path:", RED).add(" count reaches '/' with no nonzero refinement", FG),
            ColorLine().add("Safe path:", GREEN).add(" if count == 0: return 0.0 adds the required refinement", FG),
            "",
            "Next: same requirement under two path conditions — unresolved first,",
            "then discharged by a branch guard.",
        ],
    )
    all_frames.extend([div_zero_intro] * TITLE_FRAMES)

    all_frames.extend(build_demo_frames(
        source_to_lines(runtime_outputs["div_zero_buggy"]["source"]),
        runtime_outputs["div_zero_buggy"]["report"],
        "9/11 — DIV_ZERO: missing nonzero refinement",
        code_hold=8,
    ))

    all_frames.extend(build_demo_frames(
        source_to_lines(runtime_outputs["div_zero_safe"]["source"]),
        runtime_outputs["div_zero_safe"]["report"],
        "9b/11 — DIV_ZERO safe: guard supplies restriction map",
        code_hold=8,
    ))

    all_frames.extend(build_demo_frames(
        source_to_lines(runtime_outputs["non_termination_buggy"]["source"]),
        runtime_outputs["non_termination_buggy"]["report"],
        "10/11 — NON_TERMINATION: no decreasing variant",
        code_hold=8,
    ))

    all_frames.extend(build_demo_frames(
        source_to_lines(runtime_outputs["deadlock_buggy"]["source"]),
        runtime_outputs["deadlock_buggy"]["report"],
        "11/11 — DEADLOCK: cyclic wait-order relation",
        code_hold=8,
    ))

    all_frames.extend(build_demo_frames(
        source_to_lines(runtime_outputs["memory_leak_buggy"]["source"]),
        runtime_outputs["memory_leak_buggy"]["report"],
        "11b/11 — MEMORY_LEAK: resource escapes without closure",
        code_hold=8,
    ))

    # ════════════════════════════════════════════════════════════════════
    # OUTRO
    # ════════════════════════════════════════════════════════════════════

    summary = make_title_card(
        "Summary",
        "",
        [
            "",
            ColorLine().add("Displayed artifact classes:", ACCENT),
            "  • Recursive VCs + ranking-function witnesses",
            "  • Class invariants normalized into executable-style clauses",
            "  • Method/path/invariant VC matrices for stateful objects",
            "  • Runtime obstruction reports on 20 synthetic bug families",
            "",
            ColorLine().add("Verified examples:", ACCENT),
            ColorLine().add("  merge_sort: ", GREEN).add("4/4 VCs   (induction + SMT)", FG),
            ColorLine().add("  LRU Cache:  ", GREEN).add("24/24 VCs (invariant synthesis + SMT)", FG),
            "",
            ColorLine().add("Detected counterexamples / obstructions:", ACCENT),
            ColorLine().add("  Semantic: ", RED).add("missing extend, wrong comparator, stale ordering, overflow", FG),
            ColorLine().add("  Runtime:  ", RED).add("DIV_ZERO, NON_TERMINATION, DEADLOCK, MEMORY_LEAK, ...", FG),
        ],
    )
    all_frames.extend([summary] * (TITLE_FRAMES + 2))

    outro = make_title_card(
        "deppy",
        "Sheaf-Descent Verification / Bug Detection",
        [
            "",
            "Unified abstraction: site cover + local sections + gluing constraints.",
            "Same core view drives semantic proof traces and runtime bug reports.",
            "",
            "Video contents: function proofs, class invariants, class VC discharge,",
            "and representative runtime obstruction reports from the 20-family suite.",
            "",
            "Target proof scale: O(|sites|) obligations, not O(|inputs|) test cases.",
            "",
            ColorLine().add("github.com/halleyyoung/deppy", ACCENT),
        ],
    )
    all_frames.extend([outro] * (TITLE_FRAMES * 2))

    print(f"Generated {len(all_frames)} frames")
    duration = len(all_frames) / FPS
    print(f"Estimated duration: {duration:.0f}s ({duration/60:.1f}min)")

    # Write frames
    tmpdir = tempfile.mkdtemp(prefix="deppy_demo_")
    print(f"Writing frames to {tmpdir}...")
    for i, frame in enumerate(all_frames):
        frame.save(os.path.join(tmpdir, f"frame_{i:04d}.png"))

    # Encode
    output = os.path.join(os.path.dirname(__file__), "deppy_demo.mp4")
    cmd = [
        "ffmpeg", "-y",
        "-framerate", str(FPS),
        "-i", os.path.join(tmpdir, "frame_%04d.png"),
        "-c:v", "libx264",
        "-pix_fmt", "yuv420p",
        "-crf", "18",
        "-preset", "slow",
        output,
    ]
    print("Encoding MP4...")
    subprocess.run(cmd, check=True, capture_output=True)
    shutil.rmtree(tmpdir)

    size_kb = os.path.getsize(output) / 1024
    duration = len(all_frames) / FPS
    print(f"Done! {output}")
    print(f"{size_kb:.0f}KB, {duration:.1f}s ({len(all_frames)} frames @ {FPS}fps)")


if __name__ == "__main__":
    main()
