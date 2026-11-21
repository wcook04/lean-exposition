#!/usr/bin/env python3
"""Place each phrase tie of a paper on the authors' PDF, for the reader's PDF view.

    pdf_marks.py PAPER.pdf PAPER.md TIES.json OUT.json

TIES.json is the exported edition's `/ties/<stage>` file. The whole paper's plain words (formulas
and markup removed) are aligned once, in reading order, with the PDF's words (`pdftotext -bbox`);
a tie's mark is the boxes of the PDF words its own words align to, one per line. A tie that is a
numbered display is found by its tag, "(1.2)", after the last aligned word before it. A tie with
too few aligned words gets no mark and is listed in `unplaced`. Rerunning on the same files gives
the same output. Needs poppler's pdftotext.
"""
from __future__ import annotations

import html
import json
import re
import subprocess
import sys
from pathlib import Path

WORD = re.compile(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">(.*?)</word>')
PAGE = re.compile(r'<page width="([\d.]+)" height="([\d.]+)">')
MATH = re.compile(r"\$\$.*?\$\$|\$[^$]*\$", re.S)
TAG = re.compile(r"\\tag\{([^}]+)\}")


def norm(token: str) -> str:
    return re.sub(r"[^a-z0-9.]", "", token.lower().replace("ﬁ", "fi").replace("ﬂ", "fl")).strip(".")


def plain_words(text: str) -> list[str]:
    text = MATH.sub(" ", text)
    text = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"<[^>]+>", " ", text)
    text = text.replace("**", " ").replace("*", " ").replace("\\[", " ").replace("\\]", " ")
    return [w for w in (norm(t) for t in re.split(r"[\s–—/]+", text)) if len(w) >= 2 and not w.isdigit()]


def pdf_words(pdf: Path) -> tuple[list[tuple[float, float]], list[dict]]:
    out = subprocess.run(["pdftotext", "-bbox", str(pdf), "-"], capture_output=True, text=True, check=True).stdout
    sizes, words = [], []
    for page, chunk in enumerate(re.split(r"(?=<page )", out)[1:]):
        m = PAGE.search(chunk)
        sizes.append((float(m.group(1)), float(m.group(2))))
        for w in WORD.finditer(chunk):
            text = html.unescape(w.group(5))
            words.append({"page": page + 1, "box": [float(w.group(i)) for i in range(1, 5)], "text": text, "n": norm(text)})
    return sizes, words


def stream(words: list[dict]) -> list[dict]:
    """The words a phrase can match: the same filter as plain_words (no single letters, no bare numbers)."""
    return [w for w in words if len(w["n"]) >= 2 and not w["n"].isdigit()]


def lines(found: list[dict]) -> list[list]:
    """One box per printed line: the matched words grouped by page and baseline."""
    rows: list[list] = []
    for w in found:
        x0, y0, x1, y1 = w["box"]
        last = rows[-1] if rows else None
        if last and last[0] == w["page"] and abs(last[2] - y0) < 3 and x0 >= last[1] - 2:
            last[3], last[4] = max(last[3], x1), max(last[4], y1)
        else:
            rows.append([w["page"], x0, y0, x1, y1])
    return [[p, round(a, 1), round(b, 1), round(c, 1), round(d, 1)] for p, a, b, c, d in rows]


def find(words: list[dict], tokens: list[str], start: int, window: int) -> int | None:
    """Where the phrase starts: its first words in order, or failing that its first word with most of the next four close by."""
    head = tokens[: min(4, len(tokens))]
    stop = min(len(words), start + window)
    for i in range(start, stop):
        if words[i]["n"] == head[0] and all(i + k < len(words) and words[i + k]["n"] == t for k, t in enumerate(head)):
            return i
    if len(tokens) >= 4:
        for i in range(start, stop):
            if words[i]["n"] == tokens[0]:
                near = {w["n"] for w in words[i + 1:i + 9]}
                if sum(t in near for t in tokens[1:5]) >= 3:
                    return i
    return None


def md_tokens(text: str) -> list[tuple[str, int]]:
    """The paper's plain words with their character offsets: formulas, markup and tags blanked first."""
    blank = lambda m: " " * len(m.group(0))
    text = MATH.sub(blank, text)
    text = re.sub(r"\]\([^)]*\)", blank, text)
    text = re.sub(r"<[^>]+>", blank, text)
    out = []
    for m in re.finditer(r"[^\s–—/\[\]*()]+", text):
        n = norm(m.group(0))
        if len(n) >= 2 and not n.isdigit():
            out.append((n, m.start()))
    return out


def main() -> None:
    import difflib
    from bisect import bisect_left
    pdf, md, ties_path, out = map(Path, sys.argv[1:5])
    sizes, every = pdf_words(pdf)
    words = stream(every)
    text = md.read_text(encoding="utf-8")
    byte_at = [0]
    for ch in text:
        byte_at.append(byte_at[-1] + len(ch.encode("utf-8")))
    toks = md_tokens(text)
    tok_bytes = [byte_at[c] for _, c in toks]
    # One alignment of the whole paper's words against the PDF's, in reading order.
    matcher = difflib.SequenceMatcher(None, [t for t, _ in toks], [w["n"] for w in words], autojunk=False)
    to_pdf: dict[int, int] = {}
    for block in matcher.get_matching_blocks():
        for k in range(block.size):
            to_pdf[block.a + k] = block.b + k
    mapped = sorted(to_pdf)
    data = text.encode("utf-8")
    ties = json.loads(ties_path.read_text())["ties"]
    marks, unplaced = {}, []
    for tie in ties:
        a, b = (int(x) for x in tie["at"][1:].split("-"))
        lo, hi = bisect_left(tok_bytes, a), bisect_left(tok_bytes, b)
        hits = [to_pdf[i] for i in range(lo, hi) if i in to_pdf]
        tag = TAG.search(data[a:b].decode("utf-8"))
        matched = []
        if tag:
            # A display: its tag "(n)" on the PDF, after the last word before it that the alignment placed.
            k = bisect_left(mapped, lo) - 1
            begin = to_pdf[mapped[k]] if k >= 0 else 0
            label = f"({tag.group(1)})"
            for i in range(begin, min(len(words), begin + 400)):
                if words[i]["text"] == label:
                    matched = sorted((w for w in every if w["page"] == words[i]["page"] and abs(w["box"][1] - words[i]["box"][1]) < 4), key=lambda w: w["box"][0])
                    break
        elif hits and len(hits) >= max(1, 0.5 * (hi - lo)):
            first, last = min(hits), max(hits)
            if last - first <= 3 * (hi - lo) + 10:
                matched = words[first:last + 1]
        if not matched:
            unplaced.append(tie.get("phrase") or tie["at"])
            continue
        key = tie.get("phrase") or tie["at"]
        marks[key] = {"at": tie["at"], "tone": tie.get("tone"), "record": tie.get("record"), "boxes": lines(matched)}
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"schema": "pdf-marks/1", "pages": sizes, "marks": marks, "unplaced": unplaced},
                              ensure_ascii=False, separators=(",", ":")))
    print(f"pdf marks: {len(marks)} placed, {len(unplaced)} unplaced, {len(sizes)} pages")


if __name__ == "__main__":
    main()
