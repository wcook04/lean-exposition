#!/usr/bin/env python3
"""Build annotation reference destinations from a published reader's exact documents.

Run after the edition export and PDF copy, passing the reader's output directory.
Poppler's pdftotext provides printed destinations when available. A verified
byte-to-PDF point is also enough for a label. Each target always has a Markdown
line, with a PDF page and top coordinate only when they can be established.
A tone is emitted when the destination has one verified edition topic.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from html import unescape
from itertools import groupby
import json
import math
from pathlib import Path
import re
import subprocess
import unicodedata

ORDINAL = r"(?:[A-Z]\.)?(?:[A-Z]\.?)?\d+(?:\.\d+)*[a-z]?"
KINDS = r"theorem|lemma|proposition|corollary|definition|remark|example"
LABEL = re.compile(rf"(?P<kind>{KINDS}|fig(?:ure)?\.?|table)\s+(?P<number>{ORDINAL})(?![\w]|\.\w)", re.I)
HEADING = re.compile(r" {0,3}#{1,6}\s+(.+?)\s*#*\s*$")
SECTION = re.compile(rf"(?P<appendix>Appendix\s+)?(?P<number>{ORDINAL}|[A-Z])\.?\s+(?P<title>\S.*)", re.I)
DISPLAY = re.compile(r"(?<!\\)(?P<boundary>\$\$|\\\[|\\\])|(?<!\\)\\tag\*?\s*\{(?P<tag>[^{}]+)\}")
TAG = re.compile(rf"(?:{ORDINAL}|[A-Z])")
FENCE = re.compile(r" {0,3}(`{3,}|~{3,})")
INLINE_CODE = re.compile(r"(`+).*?\1")
HTML_COMMENT = re.compile(r"<!--.*?(?:-->|$)")
PDF_PAGE = re.compile(r'<page\b[^>]*\bwidth="([^"]+)"[^>]*\bheight="([^"]+)"[^>]*>(.*?)</page>', re.S)
PDF_LINE = re.compile(r'<line\b[^>]*\byMin="([^"]+)"[^>]*>(.*?)</line>', re.S)
PDF_WORD = re.compile(r'<word\b[^>]*\bxMin="([^"]+)"[^>]*\bxMax="([^"]+)"[^>]*>(.*?)</word>', re.S)


@dataclass(frozen=True)
class Reference:
    line: int
    start: int
    end: int
    hint: tuple[str, ...] = ()
    auxiliary: bool = False


@dataclass(frozen=True)
class Point:
    page: int
    y: float


def reference_key(kind: str, number: str) -> str:
    kind = kind.lower().rstrip(".")
    return f"{'figure' if kind == 'fig' else kind}:{number.lower()}"


def label_key(label: re.Match) -> str:
    return reference_key(label["kind"], label["number"])


def hint_words(text: str) -> tuple[str, ...]:
    # Stop at inline math, which can be broken into separate glyphs in a PDF.
    text = re.split(r"\$|\\\(", text, maxsplit=1)[0]
    text = unicodedata.normalize("NFKC", unescape(text)).casefold()
    return tuple(re.findall(r"[^\W\d_]+", text)[:5])


def source_references(text: str) -> dict[str, list[Reference]]:
    refs: dict[str, list[Reference]] = defaultdict(list)
    offset = 0
    fence = display = None
    auxiliary = False
    appendix: tuple[str, int] | None = None
    inside_comment = False
    for line, raw in enumerate(text.split("\n"), 1):
        row = raw.removesuffix("\r")
        start, offset = offset, offset + len(raw.encode("utf-8")) + 1
        end = start + len(row.encode("utf-8"))
        if not inside_comment and (marker := FENCE.match(row)):
            token = marker[1]
            if fence is None:
                fence = token
            elif token[0] == fence[0] and len(token) >= len(fence) and not row[marker.end():].strip():
                fence = None
            continue
        if fence:
            continue

        row = INLINE_CODE.sub(lambda match: " " * len(match[0]), row)
        if inside_comment:
            close = row.find("-->")
            if close == -1:
                continue
            row = " " * (close + 3) + row[close + 3:]
            inside_comment = False
        for comment in HTML_COMMENT.finditer(row):
            row = row[:comment.start()] + " " * len(comment[0]) + row[comment.end():]
            inside_comment = not comment[0].endswith("-->")

        if not display and (heading := HEADING.fullmatch(row)):
            title = heading[1]
            depth = len(row.lstrip().split(maxsplit=1)[0])
            if appendix and depth <= appendix[1]:
                appendix = None
            if title.startswith("Auxiliary note."):
                auxiliary = True
            if section := SECTION.fullmatch(title):
                number = section["number"]
                if len(number) > 1 or number.isdigit() or section["appendix"]:
                    ref = Reference(line, start, end, hint_words(section["title"]), auxiliary)
                    refs[reference_key("section", number)].append(ref)
                    if section["appendix"]:
                        appendix = (number.casefold(), depth)
                    if section["appendix"] or (appendix and number.casefold().startswith(f"{appendix[0]}.")):
                        refs[reference_key("appendix", number)].append(ref)
        opening = row.lstrip(" ")
        if not display and len(row) - len(opening) <= 3:
            emphasis = re.match(r"\*{1,2}|_{1,2}", opening)
            if emphasis:
                opening = opening[emphasis.end():]
            if label := LABEL.match(opening):
                tail = opening[label.end():]
                key = label_key(label)
                is_caption = key.startswith(("figure:", "table:"))
                if (is_caption and tail.startswith((".", ":"))) or (
                    emphasis and (tail.startswith((".", ":", emphasis[0])) or tail.lstrip().startswith("("))
                ):
                    # An independently emphasized label such as **Lemma 2.** may
                    # be followed by the useful identifying words on the same line.
                    prefix = len(row) - len(opening) + label.end()
                    label_end = start + len(raw[:prefix].encode("utf-8"))
                    refs[key].append(Reference(line, start, label_end, hint_words(tail), auxiliary))

        for token in DISPLAY.finditer(row):
            boundary = token["boundary"]
            if boundary:
                if boundary == display:
                    display = None
                elif display is None:
                    display = "\\]" if boundary == "\\[" else "$$" if boundary == "$$" else None
            elif display and TAG.fullmatch(token["tag"].strip()):
                tag = token["tag"].strip()
                tag_start = start + len(raw[:token.start()].encode("utf-8"))
                tag_end = start + len(raw[:token.end()].encode("utf-8"))
                refs[reference_key("equation", tag)].append(Reference(line, tag_start, tag_end, auxiliary=auxiliary))
    return refs


def choose_references(
    candidates: dict[str, list[Reference]], ties: dict, main_qualifier: bool,
) -> dict[str, Reference]:
    canonical: dict[str, set[int]] = defaultdict(set)
    for name, value in ties.get("canonical", {}).items():
        match = re.search(rf"(?:^|\.)({KINDS})-({ORDINAL})$", name, re.I)
        if match and isinstance(value, list) and len(value) == 3 and type(value[1]) is int:
            canonical[reference_key(*match.groups())].add(value[1])

    targets = {}
    for key, rows in candidates.items():
        if len(rows) == 1:
            targets[key] = rows[0]
        else:
            bound = [ref for ref in rows if any(ref.start <= at < ref.end for at in canonical[key])]
            if len(bound) == 1:
                targets[key] = bound[0]
        if main_qualifier and (primary := [ref for ref in rows if not ref.auxiliary]) and len(primary) == 1:
            kind, number = key.split(":")
            targets[f"{kind}:m.{number}"] = primary[0]
    return targets


def pdf_references(pdf: Path) -> tuple[list[tuple[float, float]], dict[str, list[tuple[Point, tuple[str, ...]]]]]:
    try:
        bbox = subprocess.run(
            ["pdftotext", "-bbox-layout", str(pdf), "-"],
            check=True, capture_output=True, text=True, encoding="utf-8",
        ).stdout
    except (FileNotFoundError, subprocess.CalledProcessError) as error:
        print(f"{pdf.name}: PDF label extraction unavailable ({error})")
        return [], {}

    pages = []
    references: dict[str, list[tuple[Point, tuple[str, ...]]]] = defaultdict(list)
    # Poppler can emit control characters from old embedded fonts, so read
    # its page, line and word elements without treating the output as strict XML.
    for page, (width, height, content) in enumerate(PDF_PAGE.findall(bbox), 1):
        width, height = float(width), float(height)
        pages.append((width, height))
        for y, line in PDF_LINE.findall(content):
            y = float(y)
            if not 0 <= y < height:
                continue
            words = [(float(x0), float(x1), unescape(word)) for x0, x1, word in PDF_WORD.findall(line)]
            if not words:
                continue
            point = Point(page, round(y, 2))
            source = " ".join(word for _, _, word in words)
            if label := LABEL.match(source):
                key = label_key(label)
                tail = source[label.end():].lstrip()
                punctuation = (".", ":") if key.startswith(("figure:", "table:")) else (".", ":", "(")
                if tail.startswith(punctuation):
                    references[key].append((point, hint_words(tail)))
            if (section := SECTION.fullmatch(source)) and not re.search(r"\.{3,}", source):
                key = reference_key("section", section["number"])
                references[key].append((point, hint_words(section["title"])))

            # A printed number is isolated, or separated by a gutter from
            # the equation. Parenthesized numbers in ordinary prose lack it.
            for i, (x0, x1, word) in enumerate(words):
                if len(word) < 3 or word[0] != "(" or word[-1] != ")" or not TAG.fullmatch(word[1:-1]):
                    continue
                at_left = i == 0 and (len(words) == 1 or words[1][0] - x1 >= 14)
                at_right = i == len(words) - 1 and (len(words) == 1 or x0 - words[i - 1][1] >= 14)
                if (at_left and x0 <= width * 0.26) or (at_right and x1 >= width * 0.74):
                    references[reference_key("equation", word[1:-1])].append((point, ()))
    return pages, references


def aligned_points(
    marks: dict, ties: dict, pages: list[tuple[float, float]], length: int,
) -> dict[int, Point]:
    """Reuse exact source-byte rows when the marks match this edition and PDF."""
    if not pages or len(marks.get("pages", [])) != len(pages):
        return {}
    if any(
        not isinstance(size, list) or len(size) != 2
        or any(type(n) not in (float, int) or not math.isfinite(n) or abs(n - actual) > 0.1
               for n, actual in zip(size, expected))
        for size, expected in zip(marks["pages"], pages)
    ):
        return {}
    marks_by_tie = marks.get("marks", {})
    verified_ranges = {row.get("phrase") or row.get("at"): row.get("at") for row in ties.get("ties", [])}
    if not marks_by_tie or any(
        name not in verified_ranges or verified_ranges[name] != mark.get("at")
        for name, mark in marks_by_tie.items()
    ):
        return {}
    points = {}
    previous = -1
    for item in marks.get("positions", []):
        if not isinstance(item, list) or len(item) != 3:
            return {}
        at, page, y = item
        if not (
            type(at) is int and previous < at < length and type(page) is int and 1 <= page <= len(pages)
            and type(y) in (int, float) and 0 <= y < pages[page - 1][1]
        ):
            return {}
        points[at] = Point(page, y)
        previous = at
    return points


def locate_reference(
    key: str, ref: Reference, candidates: list[tuple[Point, tuple[str, ...]]], aligned: Point | None,
) -> Point | None:
    kind = key.split(":")[0]
    if kind in {"section", "appendix", "figure", "table"}:
        # Section labels in a rendered table of contents or prose can match the
        # number. Require the printed title, then let exact alignment break ties.
        count = min(3 if kind in {"section", "appendix"} else 2, len(ref.hint))
        if count:
            candidates = [(point, words) for point, words in candidates if words[:count] == ref.hint[:count]]
        elif kind in {"section", "appendix"}:
            return aligned

    points = {point for point, _ in candidates}
    if aligned:
        near = {point for point in points if point.page == aligned.page and abs(point.y - aligned.y) <= 5}
        if len(near) == 1:
            return next(iter(near))
        if not near:
            return aligned
    if len(points) == 1:
        return next(iter(points))
    if kind in KINDS.split("|") and len(ref.hint) >= 2:
        matches = {point for point, hint in candidates if hint[:2] == ref.hint[:2]}
        if len(matches) == 1:
            return next(iter(matches))
    return aligned if not points else None


def topic_ranges(ties: dict, length: int) -> list[tuple[int, int, int | None]]:
    """Read topic assignments against this edition's byte ranges and palette."""
    topics = [
        (row.get("id"), row["tone"]) for row in ties.get("topics", [])
        if type(row.get("tone")) is int and row["tone"] >= 0 and row.get("light") and row.get("dark")
    ]
    palette = {
        name: tone for name, tone in topics
        if sum(other_name == name or other_tone == tone for other_name, other_tone in topics) == 1
    }
    ranges = []
    for tie in ties.get("ties", []):
        at = tie.get("at")
        if not isinstance(at, str) or not (match := re.fullmatch(r"b(\d+)-(\d+)", at)):
            continue
        start, end = map(int, match.groups())
        if not 0 <= start < end <= length:
            continue
        tone = tie.get("tone")
        topic = tie.get("topic")
        if tone is None and topic is None:
            continue
        verified = type(tone) is int and tone == palette.get(topic)
        ranges.append((start, end, tone if verified else None))
    return ranges


def destination_blocks(ties: dict, structure: dict, length: int) -> list[tuple[int, int]]:
    """Return exact containing ranges, from the smallest statement to the section."""
    paper = structure.get("paper", {})
    spans = []
    if paper.get("byte_length") == length:
        spans.extend(row.get("content_span", {}) for row in paper.get("passages", []))
        spans.extend(row.get("span", {}) for row in paper.get("sections", []))
    ranges = [(span.get("start_byte"), span.get("end_byte")) for span in spans]
    ranges.extend((span[1], span[2]) for span in ties.get("canonical", {}).values()
                  if isinstance(span, list) and len(span) == 3)
    valid = {
        (a, b) for a, b in ranges if type(a) is int and type(b) is int and 0 <= a < b <= length
    }
    return sorted(valid, key=lambda span: (span[1] - span[0], span[0]))


def destination_tone(
    ref: Reference, topics: list[tuple[int, int, int | None]], blocks: list[tuple[int, int]],
) -> int | None:
    if not topics:
        return None
    direct = {tone for a, b, tone in topics if a < ref.end and ref.start < b}
    if direct:
        return next(iter(direct)) if len(direct) == 1 else None

    # The smallest containing published block with topical evidence wins.
    # A shared label or block carrying several topics has no single colour.
    enclosing = ((start, end) for start, end in blocks if start <= ref.start and ref.end <= end)
    for _, group in groupby(enclosing, key=lambda span: span[1] - span[0]):
        local = set()
        for start, end in group:
            local.update(tone for a, b, tone in topics if start <= a and b <= end)
        if local:
            return next(iter(local)) if len(local) == 1 else None
    return None


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def edition_documents(dist: Path) -> dict[str, tuple[Path, Path, Path]]:
    edition = dist / "edition"
    documents = {}
    root_index = read_json(edition / "index.json")
    indexes = [(None, root_index)]
    indexes.extend((index.parent.name, read_json(index)) for index in sorted(edition.glob("docs/*/index.json")))
    for companion, index in indexes:
        for stage, filename in index["documents"].items():
            if companion and stage != "short":
                continue
            slot = companion or stage
            if not re.fullmatch(r"[a-z0-9-]+", slot):
                continue
            routes = index["responses"]
            structure = f"/papers/{stage}/structure"
            documents[slot] = (
                edition / filename,
                edition / routes.get(f"/ties/{stage}", ""),
                edition / routes.get(f"{structure}?representation=reader", routes.get(structure, "")),
            )
    return documents


def reader_pdf(dist: Path, slot: str, instance: dict) -> Path | None:
    output = dist / "pdf"
    doc = next((doc for doc in instance.get("documents", []) if doc.get("slot") == slot), None)
    if doc is not None:
        reading = doc.get("reading_pdf") if doc.get("adapted") else None
        pdf = reading or doc.get("pdf")
        if not pdf:
            return None
        name = pdf.get("name") or (pdf["file"] if reading else f"{doc.get('slug') or 'paper'}.pdf")
        path = output / name
        return path if path.is_file() else None

    # Older exports do not include an instance manifest. Only use the
    # public reader filenames that unambiguously identify a document.
    if slot == "adapted":
        candidates = [path for path in output.glob("*-adapted-v*.pdf") if re.search(r"-adapted-v\d+\.pdf$", path.name)]
    else:
        names = {"short": ("paper.pdf", "short-paper.pdf"), "long": ("long-record.pdf",),
                 "expository": ("exposition.pdf",)}.get(slot, (f"{slot}.pdf",))
        candidates = [output / name for name in names if (output / name).is_file()]
    return candidates[0] if len(candidates) == 1 else None


def build(dist: Path, output: Path, instance: dict) -> None:
    for slot, (markdown, tie_file, structure_file) in edition_documents(dist).items():
        data = markdown.read_bytes()
        text = data.decode("utf-8")
        ties = read_json(tie_file) if tie_file.is_file() else {}
        structure = read_json(structure_file) if structure_file.is_file() else {}
        topics = topic_ranges(ties, len(data))
        blocks = destination_blocks(ties, structure, len(data))
        candidates = source_references(text)
        targets = choose_references(candidates, ties, "References with prefix M refer to that paper." in text)
        pdf = reader_pdf(dist, slot, instance)
        pages, printed = pdf_references(pdf) if pdf and targets else ([], {})
        marks_path = dist / "pdf-marks" / f"{slot}.json"
        points = aligned_points(read_json(marks_path), ties, pages, len(data)) if marks_path.is_file() else {}
        result = {}
        for key, ref in sorted(targets.items()):
            kind, number = key.split(":")
            printed_kind = "section" if kind == "appendix" else kind
            original = f"{printed_kind}:{number.removeprefix('m.')}"
            aligned = None
            if kind != "equation":
                aligned = next((points[at] for at in range(ref.start, ref.end) if at in points), None)
            # The appendix is a separate article in some editions. Its own
            # numbers do not identify locations in the main paper's PDF.
            point = None if ref.auxiliary else locate_reference(key, ref, printed.get(original, []), aligned)
            result[key] = {"line": ref.line}
            if point:
                result[key].update(page=point.page, y=point.y)
            tone = destination_tone(ref, topics, blocks)
            if tone is not None:
                result[key]["tone"] = tone

        output.mkdir(parents=True, exist_ok=True)
        (output / f"{slot}.json").write_text(
            json.dumps({"schema": "paper-references/1", "targets": result}, separators=(",", ":")) + "\n",
            encoding="utf-8",
        )
        print(f"{dist.name}/{slot}: {len(result)} Markdown targets, "
              f"{sum('page' in row for row in result.values())} PDF targets, "
              f"{sum('tone' in row for row in result.values())} with a verified topic")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dist", type=Path, help="reader output containing edition/index.json")
    parser.add_argument("--output-dir", type=Path, help="write indexes here instead of <dist>/paper-references")
    parser.add_argument("--instance", type=Path, help="library instance manifest that names the reader's PDFs")
    args = parser.parse_args()
    instance_path = args.instance or args.dist / "library-instance.json"
    instance = read_json(instance_path) if args.instance or instance_path.is_file() else {}
    build(args.dist, args.output_dir or args.dist / "paper-references", instance)


if __name__ == "__main__":
    main()
