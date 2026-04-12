"""Generate slide-sized PNGs showing deppy equivalence checking demos."""

from PIL import Image, ImageDraw, ImageFont
import textwrap

# --- Configuration ---
WIDTH, HEIGHT = 1920, 1080
BG_COLOR = "#1a1b26"       # dark navy
CODE_BG = "#24283b"        # slightly lighter for code blocks
TITLE_COLOR = "#7aa2f7"    # blue
SUBTITLE_COLOR = "#9ece6a" # green
TEXT_COLOR = "#c0caf5"     # light text
COMMENT_COLOR = "#565f89"  # muted
KEYWORD_COLOR = "#bb9af7"  # purple
STRING_COLOR = "#9ece6a"   # green
FUNC_COLOR = "#7dcfff"     # cyan
NUM_COLOR = "#ff9e64"      # orange
EQUIV_COLOR = "#9ece6a"    # green (equivalent)
INEQUIV_COLOR = "#f7768e"  # red (inequivalent)
BORDER_COLOR = "#3b4261"
CMD_COLOR = "#e0af68"      # yellow for commands
ACCENT_LINE = "#7aa2f7"

def get_fonts():
    """Try to load good monospace fonts."""
    mono_paths = [
        "/System/Library/Fonts/SFMono-Regular.otf",
        "/System/Library/Fonts/Menlo.ttc",
        "/System/Library/Fonts/Monaco.dfont",
        "/Library/Fonts/SF-Mono-Regular.otf",
    ]
    sans_paths = [
        "/System/Library/Fonts/SFNSDisplay.ttf",
        "/System/Library/Fonts/Helvetica.ttc",
        "/System/Library/Fonts/HelveticaNeue.ttc",
    ]
    bold_paths = [
        "/System/Library/Fonts/SFNSDisplayBold.ttf",
        "/System/Library/Fonts/SFMono-Bold.otf",
        "/Library/Fonts/SF-Mono-Bold.otf",
    ]

    mono = None
    for p in mono_paths:
        try:
            mono = ImageFont.truetype(p, 20)
            break
        except (OSError, IOError):
            continue
    if mono is None:
        mono = ImageFont.load_default()

    mono_sm = None
    for p in mono_paths:
        try:
            mono_sm = ImageFont.truetype(p, 17)
            break
        except (OSError, IOError):
            continue
    if mono_sm is None:
        mono_sm = mono

    title_font = None
    for p in sans_paths + bold_paths:
        try:
            title_font = ImageFont.truetype(p, 36)
            break
        except (OSError, IOError):
            continue
    if title_font is None:
        title_font = mono

    subtitle_font = None
    for p in sans_paths:
        try:
            subtitle_font = ImageFont.truetype(p, 22)
            break
        except (OSError, IOError):
            continue
    if subtitle_font is None:
        subtitle_font = mono

    label_font = None
    for p in sans_paths + bold_paths:
        try:
            label_font = ImageFont.truetype(p, 18)
            break
        except (OSError, IOError):
            continue
    if label_font is None:
        label_font = mono

    verdict_font = None
    for p in sans_paths + bold_paths:
        try:
            verdict_font = ImageFont.truetype(p, 28)
            break
        except (OSError, IOError):
            continue
    if verdict_font is None:
        verdict_font = mono

    return mono, mono_sm, title_font, subtitle_font, label_font, verdict_font


def draw_rounded_rect(draw, xy, radius, fill=None, outline=None, width=1):
    """Draw a rounded rectangle."""
    x0, y0, x1, y1 = xy
    draw.rounded_rectangle(xy, radius=radius, fill=fill, outline=outline, width=width)


def draw_code_block(draw, x, y, w, h, lines, mono_font, label=None, label_font=None, highlight_line=None):
    """Draw a code block with syntax-like coloring."""
    # Background
    draw_rounded_rect(draw, (x, y, x+w, y+h), radius=10, fill=CODE_BG, outline=BORDER_COLOR, width=1)

    # Label
    text_y = y + 12
    if label and label_font:
        draw.text((x + 14, text_y), label, fill=SUBTITLE_COLOR, font=label_font)
        text_y += 28

    # Code lines
    line_height = 24
    for i, line in enumerate(lines):
        ly = text_y + i * line_height
        if highlight_line is not None and i == highlight_line:
            draw.rectangle((x+4, ly-2, x+w-4, ly+line_height-2), fill="#3b2020")
        # Simple syntax coloring
        color = TEXT_COLOR
        stripped = line.lstrip()
        if stripped.startswith("#"):
            color = COMMENT_COLOR
        elif stripped.startswith("def "):
            # Draw 'def' in keyword color, rest in func color
            indent = len(line) - len(stripped)
            draw.text((x + 14, ly), " " * indent + "def", fill=KEYWORD_COLOR, font=mono_font)
            rest = stripped[3:]
            # Find function name
            paren = rest.find("(")
            if paren > 0:
                fname = rest[:paren]
                draw.text((x + 14 + mono_font.getlength(" " * indent + "def"), ly), fname, fill=FUNC_COLOR, font=mono_font)
                draw.text((x + 14 + mono_font.getlength(" " * indent + "def" + fname), ly), rest[paren:], fill=TEXT_COLOR, font=mono_font)
            else:
                draw.text((x + 14 + mono_font.getlength(" " * indent + "def"), ly), rest, fill=TEXT_COLOR, font=mono_font)
            continue
        elif any(stripped.startswith(kw) for kw in ["if ", "for ", "return ", "else:", "elif "]):
            kw = stripped.split()[0].rstrip(":")
            if stripped.endswith(":"):
                kw_full = kw + ":"  if kw in ["else", "elif"] else kw
            else:
                kw_full = kw
            indent = len(line) - len(stripped)
            draw.text((x + 14, ly), " " * indent + kw_full, fill=KEYWORD_COLOR, font=mono_font)
            rest = stripped[len(kw_full):]
            draw.text((x + 14 + mono_font.getlength(" " * indent + kw_full), ly), rest, fill=TEXT_COLOR, font=mono_font)
            continue
        draw.text((x + 14, ly), line, fill=color, font=mono_font)

    return text_y + len(lines) * line_height


def draw_terminal_block(draw, x, y, w, h, cmd, output_lines, mono_font, label_font):
    """Draw a terminal-style block with command and output."""
    draw_rounded_rect(draw, (x, y, x+w, y+h), radius=10, fill="#1a1b26", outline=BORDER_COLOR, width=1)

    # Terminal dots
    dot_y = y + 12
    for i, color in enumerate(["#f7768e", "#e0af68", "#9ece6a"]):
        draw.ellipse((x+12 + i*22, dot_y, x+24 + i*22, dot_y+12), fill=color)

    text_y = y + 32

    # Command
    draw.text((x + 14, text_y), "$ ", fill=SUBTITLE_COLOR, font=mono_font)
    draw.text((x + 14 + mono_font.getlength("$ "), text_y), cmd, fill=CMD_COLOR, font=mono_font)
    text_y += 28

    # Separator
    draw.line((x+10, text_y, x+w-10, text_y), fill=BORDER_COLOR, width=1)
    text_y += 8

    # Output
    line_height = 22
    for line in output_lines:
        color = TEXT_COLOR
        if "inequivalent" in line.lower():
            color = INEQUIV_COLOR
        elif "equivalent" in line.lower() and "inequivalent" not in line.lower():
            color = EQUIV_COLOR
        elif line.strip().startswith("Program"):
            color = SUBTITLE_COLOR
        elif "Verdict" in line:
            if "inequivalent" in line.lower():
                color = INEQUIV_COLOR
            else:
                color = EQUIV_COLOR
        elif line.strip().startswith(("parse", "build", "align", "equiv", "z3", "mutation", "total")):
            color = COMMENT_COLOR
        draw.text((x + 14, text_y), line, fill=color, font=mono_font)
        text_y += line_height

    return text_y


def generate_fibonacci_slide():
    """Generate the fibonacci equivalence slide."""
    mono, mono_sm, title_font, subtitle_font, label_font, verdict_font = get_fonts()

    img = Image.new("RGB", (WIDTH, HEIGHT), BG_COLOR)
    draw = ImageDraw.Draw(img)

    # Title
    draw.text((60, 30), "deppy equiv", fill=TITLE_COLOR, font=title_font)
    draw.text((60, 72), "Sheaf-theoretic equivalence checking: detecting an off-by-one bug", fill=COMMENT_COLOR, font=subtitle_font)

    # Accent line
    draw.line((60, 105, WIDTH-60, 105), fill=ACCENT_LINE, width=2)

    # --- Left code block: fibonacci.py ---
    fib_lines = [
        "# fibonacci.py",
        "def fib(n):",
        "    if n <= 1:",
        "        return n",
        "    a, b = 0, 1",
        "    for _ in range(2, n + 1):",
        "        a, b = b, a + b",
        "    return b",
    ]

    code_w = 580
    code_h = 260
    draw_code_block(draw, 60, 125, code_w, code_h, fib_lines, mono,
                    label="fibonacci.py", label_font=label_font)

    # --- Right code block: fibonacci_bug.py ---
    bug_lines = [
        "# fibonacci_bug.py",
        "def fib(n):",
        "    if n <= 1:",
        "        return n",
        "    a, b = 0, 1",
        "    for _ in range(2, n):        # BUG: off-by-one",
        "        a, b = b, a + b",
        "    return b",
    ]

    draw_code_block(draw, 680, 125, code_w + 60, code_h, bug_lines, mono,
                    label="fibonacci_bug.py", label_font=label_font, highlight_line=5)

    # VS label between code blocks
    draw.text((650, 245), "vs", fill=COMMENT_COLOR, font=subtitle_font)

    # --- Terminal output ---
    cmd = "deppy equiv demo/fibonacci.py demo/fibonacci_bug.py --verbose"

    output_lines = [
        "  parse .......................... 0.001s",
        "  build_presheaves ............... 0.000s",
        "  align_covers ................... 0.000s",
        "  equivalence_check .............. 0.716s",
        "  z3_equivalence ................. 0.587s",
        "",
        "  +---------------------------------------------------------+",
        "  |          Sheaf Equivalence Checker                      |",
        "  +---------------------------------------------------------+",
        "",
        "  Program f: f (demo/fibonacci.py)",
        "  Program g: g (demo/fibonacci_bug.py)",
        "",
        "  Verdict: INEQUIVALENT",
        "  Strength: denotational",
        "",
        "  Site-by-Site Analysis:",
        "    X common_fib_fib [call_result]  fwd:pass  bwd:pass",
        "",
        "  total: 1.305s",
    ]

    term_w = WIDTH - 120
    term_h = 510
    draw_terminal_block(draw, 60, 410, term_w, term_h, cmd, output_lines, mono_sm, label_font)

    # Verdict badge
    badge_x = WIDTH - 380
    badge_y = 940
    draw_rounded_rect(draw, (badge_x, badge_y, badge_x+310, badge_y+55), radius=12,
                      fill="#3b2020", outline=INEQUIV_COLOR, width=2)
    draw.text((badge_x + 20, badge_y + 12), "INEQUIVALENT", fill=INEQUIV_COLOR, font=verdict_font)
    draw.text((badge_x + 230, badge_y + 18), "exit 1", fill=COMMENT_COLOR, font=label_font)

    # deppy logo/branding
    draw.text((60, HEIGHT - 40), "deppy  |  sheaf-descent semantic typing for Python", fill=COMMENT_COLOR, font=label_font)

    img.save("/Users/halleyyoung/Documents/div/mathdivergence/deppy/slide_fibonacci_equiv.png")
    print("Saved slide_fibonacci_equiv.png")


def generate_factorial_slide():
    """Generate the factorial equivalence slide."""
    mono, mono_sm, title_font, subtitle_font, label_font, verdict_font = get_fonts()

    img = Image.new("RGB", (WIDTH, HEIGHT), BG_COLOR)
    draw = ImageDraw.Draw(img)

    # Title
    draw.text((60, 30), "deppy equiv", fill=TITLE_COLOR, font=title_font)
    draw.text((60, 72), "Sheaf-theoretic equivalence checking: iterative vs recursive factorial", fill=COMMENT_COLOR, font=subtitle_font)

    # Accent line
    draw.line((60, 105, WIDTH-60, 105), fill=ACCENT_LINE, width=2)

    # --- Left code block: factorial_iterative.py ---
    iter_lines = [
        "# factorial_iterative.py",
        "def factorial(n):",
        "    result = 1",
        "    for i in range(2, n + 1):",
        "        result *= i",
        "    return result",
    ]

    code_w = 580
    code_h = 220
    draw_code_block(draw, 60, 125, code_w, code_h, iter_lines, mono,
                    label="factorial_iterative.py", label_font=label_font)

    # --- Right code block: factorial_recursive.py ---
    rec_lines = [
        "# factorial_recursive.py",
        "def factorial(n):",
        "    if n <= 1:",
        "        return 1",
        "    return n * factorial(n - 1)",
    ]

    draw_code_block(draw, 700, 125, code_w, code_h - 10, rec_lines, mono,
                    label="factorial_recursive.py", label_font=label_font)

    # VS label between code blocks
    draw.text((656, 225), "vs", fill=COMMENT_COLOR, font=subtitle_font)

    # --- Terminal output ---
    cmd = "deppy equiv demo/factorial_iterative.py demo/factorial_recursive.py --verbose"

    output_lines = [
        "  parse .......................... 0.001s",
        "  build_presheaves ............... 0.000s",
        "  align_covers ................... 0.000s",
        "  equivalence_check .............. 0.687s",
        "  z3_equivalence ................. 0.198s",
        "  mutation_analysis .............. 0.000s",
        "",
        "  +---------------------------------------------------------+",
        "  |          Sheaf Equivalence Checker                      |",
        "  +---------------------------------------------------------+",
        "",
        "  Program f: f (demo/factorial_iterative.py)",
        "  Program g: g (demo/factorial_recursive.py)",
        "",
        "  Verdict: EQUIVALENT",
        "  Strength: denotational",
        "",
        "  Site-by-Site Analysis:",
        "    V common_factorial_factorial [call_result]  fwd:pass  bwd:pass",
        "",
        "  total: 0.887s",
    ]

    term_w = WIDTH - 120
    term_h = 540
    draw_terminal_block(draw, 60, 370, term_w, term_h, cmd, output_lines, mono_sm, label_font)

    # Verdict badge
    badge_x = WIDTH - 380
    badge_y = 940
    draw_rounded_rect(draw, (badge_x, badge_y, badge_x+310, badge_y+55), radius=12,
                      fill="#1a2e1a", outline=EQUIV_COLOR, width=2)
    draw.text((badge_x + 30, badge_y + 12), "EQUIVALENT", fill=EQUIV_COLOR, font=verdict_font)
    draw.text((badge_x + 230, badge_y + 18), "exit 0", fill=COMMENT_COLOR, font=label_font)

    # deppy logo/branding
    draw.text((60, HEIGHT - 40), "deppy  |  sheaf-descent semantic typing for Python", fill=COMMENT_COLOR, font=label_font)

    img.save("/Users/halleyyoung/Documents/div/mathdivergence/deppy/slide_factorial_equiv.png")
    print("Saved slide_factorial_equiv.png")


if __name__ == "__main__":
    generate_fibonacci_slide()
    generate_factorial_slide()
