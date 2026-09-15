#!/usr/bin/env python3
"""Render the canonical Markdown reports as APA 7-style academic PDFs."""

from __future__ import annotations

import argparse
import html
import re
from pathlib import Path

from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_LEFT
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import inch
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (
    BaseDocTemplate,
    Frame,
    PageBreak,
    PageTemplate,
    Paragraph,
    Spacer,
    Table,
    TableStyle,
)

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "output" / "pdf"
FONT_DIR = Path("/usr/share/fonts/truetype/dejavu")


def register_fonts() -> None:
    regular = FONT_DIR / "DejaVuSerif.ttf"
    bold = FONT_DIR / "DejaVuSerif-Bold.ttf"
    if not regular.exists() or not bold.exists():
        raise FileNotFoundError("DejaVu Serif fonts are required for the PDF renderer")
    pdfmetrics.registerFont(TTFont("AcademicSerif", str(regular)))
    pdfmetrics.registerFont(TTFont("AcademicSerif-Bold", str(bold)))
    pdfmetrics.registerFontFamily(
        "AcademicSerif", normal="AcademicSerif", bold="AcademicSerif-Bold"
    )


def normalize_math(text: str) -> str:
    """Turn the small LaTeX vocabulary used in the reports into readable text."""

    # The Markdown reports preserve TeX commands with doubled backslashes.
    # Collapse those escapes before interpreting the small command vocabulary.
    text = text.replace("\\\\", "\\")
    replacements = [
        (r"\geq", "≥"),
        (r"\leq", "≤"),
        (r"\ge", "≥"),
        (r"\le", "≤"),
        (r"\to", "→"),
        (r"\mapsto", "↦"),
        (r"\in", "∈"),
        (r"\notin", "∉"),
        (r"\subseteq", "⊆"),
        (r"\cap", "∩"),
        (r"\cup", "∪"),
        (r"\times", "×"),
        (r"\cdot", "·"),
        (r"\Delta", "Δ"),
        (r"\Lambda", "Λ"),
        (r"\ell", "l"),
        (r"\mathbb{N}", "ℕ"),
        (r"\mathbb{R}", "ℝ"),
        (r"\mathbb{Z}", "ℤ"),
    ]
    for pattern, replacement in replacements:
        text = text.replace(pattern, replacement)

    text = text.replace(r"\left", "").replace(r"\right", "")
    text = text.replace(r"\begin{pmatrix}", "[")
    text = text.replace(r"\end{pmatrix}", "]")
    text = text.replace(r"\begin{bmatrix}", "[")
    text = text.replace(r"\end{bmatrix}", "]")
    text = re.sub(r"\\(?:begin|end)\{(?:aligned|align\*|equation)\}", "", text)
    text = re.sub(r"\\(?:qquad|quad)", " ", text)
    text = text.replace(r"\\", " ; ").replace("&", "   ")
    text = re.sub(r"\\(?:text|mathrm|operatorname|mathbf|mathbb)\{([^{}]*)\}", r"\1", text)
    text = re.sub(r"\\frac\{([^{}]*)\}\{([^{}]*)\}", r"(\1)/(\2)", text)
    text = re.sub(r"\\binom\{([^{}]*)\}\{([^{}]*)\}", r"C(\1,\2)", text)
    text = re.sub(r"\^\{([^{}]*)\}", r"^(\1)", text)
    text = re.sub(r"_\{([^{}]*)\}", r"_(\1)", text)
    text = re.sub(r"\\[a-zA-Z]+", "", text)
    text = text.replace(r"\[", "").replace(r"\]", "")

    text = (
        text.replace("‐", "-")
        .replace("‑", "-")
        .replace("‒", "-")
        .replace("–", "-")
        .replace("—", "-")
        .replace("−", "-")
        .replace("“", '"')
        .replace("”", '"')
        .replace("‘", "'")
        .replace("’", "'")
    )
    return text


def inline_markup(text: str) -> str:
    text = normalize_math(text)
    tokens: list[str] = []

    def token(value: str) -> str:
        tokens.append(value)
        return f"@@TOKEN{len(tokens) - 1}@@"

    text = re.sub(
        r"\[([^\]]+)\]\(([^)]+)\)",
        lambda match: token(html.escape(match.group(1), quote=False)),
        text,
    )
    text = re.sub(
        r"\*\*([^*]+)\*\*",
        lambda match: token(f"<b>{html.escape(match.group(1), quote=False)}</b>"),
        text,
    )
    text = re.sub(
        r"\x60([^\x60]+)\x60",
        lambda match: token(html.escape(match.group(1), quote=False)),
        text,
    )
    escaped = html.escape(text, quote=False)
    for index, value in enumerate(tokens):
        escaped = escaped.replace(f"@@TOKEN{index}@@", value)
    return escaped


def build_styles() -> dict[str, ParagraphStyle]:
    base = getSampleStyleSheet()
    return {
        "TitlePageTitle": ParagraphStyle(
            "TitlePageTitle",
            parent=base["Title"],
            fontName="AcademicSerif-Bold",
            fontSize=16,
            leading=24,
            alignment=TA_CENTER,
            spaceAfter=18,
        ),
        "TitlePageSubtitle": ParagraphStyle(
            "TitlePageSubtitle",
            parent=base["Normal"],
            fontName="AcademicSerif",
            fontSize=12,
            leading=24,
            alignment=TA_CENTER,
        ),
        "TitlePageMeta": ParagraphStyle(
            "TitlePageMeta",
            parent=base["Normal"],
            fontName="AcademicSerif",
            fontSize=12,
            leading=24,
            alignment=TA_CENTER,
        ),
        "BodyAPA": ParagraphStyle(
            "BodyAPA",
            parent=base["BodyText"],
            fontName="AcademicSerif",
            fontSize=12,
            leading=24,
            alignment=TA_LEFT,
            firstLineIndent=18,
            spaceAfter=0,
            spaceBefore=0,
        ),
        "AbstractAPA": ParagraphStyle(
            "AbstractAPA",
            parent=base["BodyText"],
            fontName="AcademicSerif",
            fontSize=12,
            leading=24,
            alignment=TA_LEFT,
            firstLineIndent=0,
            spaceAfter=0,
        ),
        "HeadingAPA1": ParagraphStyle(
            "HeadingAPA1",
            parent=base["Heading1"],
            fontName="AcademicSerif-Bold",
            fontSize=12,
            leading=24,
            alignment=TA_CENTER,
            spaceBefore=24,
            spaceAfter=0,
            keepWithNext=True,
        ),
        "HeadingAPA2": ParagraphStyle(
            "HeadingAPA2",
            parent=base["Heading2"],
            fontName="AcademicSerif-Bold",
            fontSize=12,
            leading=24,
            alignment=TA_LEFT,
            spaceBefore=24,
            spaceAfter=0,
            keepWithNext=True,
        ),
        "HeadingAPA3": ParagraphStyle(
            "HeadingAPA3",
            parent=base["Heading3"],
            fontName="AcademicSerif-Bold",
            fontSize=12,
            leading=24,
            alignment=TA_LEFT,
            leftIndent=18,
            spaceBefore=18,
            spaceAfter=0,
            keepWithNext=True,
        ),
        "EquationAPA": ParagraphStyle(
            "EquationAPA",
            parent=base["BodyText"],
            fontName="AcademicSerif",
            fontSize=12,
            leading=24,
            alignment=TA_CENTER,
            firstLineIndent=0,
            spaceBefore=0,
            spaceAfter=0,
        ),
        "ListAPA": ParagraphStyle(
            "ListAPA",
            parent=base["BodyText"],
            fontName="AcademicSerif",
            fontSize=12,
            leading=24,
            alignment=TA_LEFT,
            leftIndent=36,
            firstLineIndent=-18,
            spaceAfter=0,
        ),
        "TableAPA": ParagraphStyle(
            "TableAPA",
            parent=base["BodyText"],
            fontName="AcademicSerif",
            fontSize=8.5,
            leading=10,
            alignment=TA_LEFT,
            spaceAfter=0,
        ),
        "TableHeaderAPA": ParagraphStyle(
            "TableHeaderAPA",
            parent=base["BodyText"],
            fontName="AcademicSerif-Bold",
            fontSize=8.5,
            leading=10,
            alignment=TA_LEFT,
            spaceAfter=0,
        ),
    }


def is_heading(line: str) -> bool:
    return bool(re.match(r"^#{1,4}\s+", line))


def is_list_item(line: str) -> bool:
    return bool(re.match(r"^(?:[-*]|\d+\.)\s+", line))


def split_table_row(line: str) -> list[str]:
    stripped = line.strip()
    if stripped.startswith("|"):
        stripped = stripped[1:]
    if stripped.endswith("|"):
        stripped = stripped[:-1]
    return [cell.strip() for cell in stripped.split("|")]


def is_table_separator(line: str) -> bool:
    cells = split_table_row(line)
    return bool(cells) and all(re.fullmatch(r":?-+:?", cell) for cell in cells)


def make_table(lines: list[str], styles: dict[str, ParagraphStyle]) -> Table:
    rows = [split_table_row(line) for line in lines]
    if len(rows) >= 2 and is_table_separator(lines[1]):
        rows.pop(1)
    count = max(len(row) for row in rows)
    rows = [row + [""] * (count - len(row)) for row in rows]
    data = []
    for row_index, row in enumerate(rows):
        style = styles["TableHeaderAPA"] if row_index == 0 else styles["TableAPA"]
        data.append([Paragraph(inline_markup(cell), style) for cell in row])

    available = 6.5 * inch
    if count == 3:
        widths = [1.75 * inch, 1.45 * inch, 3.3 * inch]
    elif count == 4:
        widths = [0.9 * inch, 1.25 * inch, 1.35 * inch, 3.0 * inch]
    else:
        widths = [available / count] * count
    table = Table(data, colWidths=widths, repeatRows=1, hAlign="LEFT")
    table.setStyle(
        TableStyle(
            [
                ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#E8E8E8")),
                ("LINEBELOW", (0, 0), (-1, 0), 0.75, colors.black),
                ("LINEBELOW", (0, -1), (-1, -1), 0.5, colors.black),
                ("GRID", (0, 0), (-1, -1), 0.25, colors.HexColor("#777777")),
                ("VALIGN", (0, 0), (-1, -1), "TOP"),
                ("LEFTPADDING", (0, 0), (-1, -1), 5),
                ("RIGHTPADDING", (0, 0), (-1, -1), 5),
                ("TOPPADDING", (0, 0), (-1, -1), 5),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
            ]
        )
    )
    return table


def draw_page_number(canvas, _doc) -> None:
    canvas.saveState()
    canvas.setFont("AcademicSerif", 12)
    canvas.drawRightString(letter[0] - inch, letter[1] - 0.6 * inch, str(canvas.getPageNumber()))
    canvas.restoreState()


def heading_style(level: int, styles: dict[str, ParagraphStyle]) -> ParagraphStyle:
    if level <= 2:
        return styles["HeadingAPA1"]
    if level == 3:
        return styles["HeadingAPA2"]
    return styles["HeadingAPA3"]


def render_report(source: Path, output: Path, author: str, affiliation: str, date: str) -> None:
    lines = source.read_text(encoding="utf-8").splitlines()
    title = next((line[2:].strip() for line in lines if line.startswith("# ")), source.stem)
    subtitle = next((line[3:].strip() for line in lines if line.startswith("## ")), "")
    styles = build_styles()

    output.parent.mkdir(parents=True, exist_ok=True)
    frame = Frame(
        inch,
        inch,
        letter[0] - 2 * inch,
        letter[1] - 2 * inch,
        id="apa-body",
        leftPadding=0,
        rightPadding=0,
        topPadding=0,
        bottomPadding=0,
    )
    doc = BaseDocTemplate(
        str(output),
        pagesize=letter,
        leftMargin=inch,
        rightMargin=inch,
        topMargin=inch,
        bottomMargin=inch,
        title=title,
        author=author,
        subject="APA 7-style standardized mathematical research report",
    )
    doc.addPageTemplates([PageTemplate(id="apa", frames=[frame], onPage=draw_page_number)])

    story = [
        Spacer(1, 1.65 * inch),
        Paragraph(inline_markup(title), styles["TitlePageTitle"]),
        Paragraph(inline_markup(subtitle), styles["TitlePageSubtitle"]),
        Spacer(1, 0.65 * inch),
        Paragraph(inline_markup(author), styles["TitlePageMeta"]),
        Paragraph(inline_markup(affiliation), styles["TitlePageMeta"]),
        Paragraph(inline_markup(date), styles["TitlePageMeta"]),
        PageBreak(),
    ]

    body_started = False
    subtitle_skipped = False
    abstract_mode = False
    index = 0
    while index < len(lines):
        line = lines[index].rstrip()
        if line.startswith("# "):
            body_started = True
            index += 1
            continue
        if line.startswith("## ") and not subtitle_skipped:
            subtitle_skipped = True
            index += 1
            continue
        if not line.strip():
            index += 1
            continue

        if is_heading(line):
            match = re.match(r"^(#{1,4})\s+(.*)$", line)
            assert match
            level = len(match.group(1))
            heading_text = match.group(2).strip()
            abstract_mode = heading_text.lower() == "abstract"
            story.append(Paragraph(inline_markup(heading_text), heading_style(level, styles)))
            index += 1
            continue

        if line.startswith("|"):
            table_lines = []
            while index < len(lines) and lines[index].strip().startswith("|"):
                table_lines.append(lines[index].strip())
                index += 1
            story.append(Spacer(1, 8))
            story.append(make_table(table_lines, styles))
            story.append(Spacer(1, 8))
            continue

        if line.strip() in {r"\[", r"\begin{equation}", r"\begin{align*}"}:
            equation_lines = []
            index += 1
            while index < len(lines) and lines[index].strip() not in {
                r"\]",
                r"\end{equation}",
                r"\end{align*}",
            }:
                if lines[index].strip():
                    equation_lines.append(lines[index].strip())
                index += 1
            equation = " ".join(equation_lines)
            story.append(Paragraph(inline_markup(equation), styles["EquationAPA"]))
            continue

        if is_list_item(line):
            while index < len(lines) and is_list_item(lines[index].strip()):
                current = lines[index].strip()
                item = re.sub(r"^(?:[-*]|\d+\.)\s+", "", current)
                bullet = "•" if current.startswith(("-", "*")) else current.split(".", 1)[0] + "."
                story.append(Paragraph(f"{bullet} {inline_markup(item)}", styles["ListAPA"]))
                index += 1
            continue

        paragraph_lines = [line.strip()]
        index += 1
        while index < len(lines):
            candidate = lines[index].rstrip()
            if (
                not candidate.strip()
                or is_heading(candidate)
                or candidate.startswith("|")
                or candidate.strip() in {r"\[", r"\begin{equation}", r"\begin{align*}"}
                or is_list_item(candidate.strip())
            ):
                break
            paragraph_lines.append(candidate.strip())
            index += 1
        paragraph = " ".join(paragraph_lines)
        style = styles["AbstractAPA"] if abstract_mode else styles["BodyAPA"]
        story.append(Paragraph(inline_markup(paragraph), style))

    doc.build(story)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--author", default="Dylan Tague")
    parser.add_argument("--affiliation", default="Independent Capstone Research Project")
    parser.add_argument("--date", default="September 11, 2026")
    args = parser.parse_args()

    register_fonts()
    reports = [
        (
            ROOT / "docs/capstone/EXACT_LIST_EDGE_LABELINGS_FINAL_REPORT.md",
            args.out / "Exact_List_Edge_Labelings_Final_Report_APA7.pdf",
        ),
        (
            ROOT / "docs/capstone/CLAIMS_STATUS_REPORT.md",
            args.out / "Exact_List_Edge_Labelings_Claims_Status_APA7.pdf",
        ),
    ]
    for source, output in reports:
        render_report(source, output, args.author, args.affiliation, args.date)
        print(output)


if __name__ == "__main__":
    main()
