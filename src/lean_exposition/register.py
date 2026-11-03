"""Measure the prose register of a manuscript against the papers it cites.

A detector, never a gate. It reports how far the prose of a manuscript sits
from a corpus of human-written papers, feature by feature, in units of the
corpus inter-quartile range (IQR), and quotes the sentences that drive each
distance. Nothing here passes or fails a manuscript.

Standard library only, so the module can be copied into a review packet and
run with plain ``python3 -m`` or through ``lean-exposition register``.

Inputs
  * LaTeX (.tex): preamble, comments, math, citations, labels and cross
    references are stripped; commands keep their text arguments.
  * Markdown or plain text (.md, .txt), including pandoc output and pdftotext
    extractions (``extracted.md``): markup, extraction junk, reference lists
    and math-heavy lines are removed; two-column page layouts are split.
  * A directory: uses ``extracted.md`` if present, otherwise every
    .tex/.md/.txt file below it.

Distances: d = (value - corpus median) / scale, where scale is the corpus IQR,
floored for features the corpus almost never uses. |d| above the threshold
(default 1.5) is reported as outside the literature range. The profile also
records, per feature, the leave-one-out rate at which the corpus documents
themselves fall outside the range: a feature with a high rate is noisy even
for human papers.

Extraction limits: mathematics becomes the token MATH, cross references REF
and inline code CODE; a sentence that is a semicolon-separated catalogue of
short noun phrases is excluded as a list. ``register dump`` shows exactly what
was read.

The companion rule set is ``resources/register/rules.json``; see
``docs/register-stage.md`` for the stage that uses both.
"""
from __future__ import annotations

import json
import os
import random
import re
import statistics
import sys
from typing import Callable, Dict, List, Optional, Sequence, Tuple

VERSION = "lean_exposition.register/1"

# --------------------------------------------------------------------------
# Marker characters used inside the cleaned text stream.
#   SOFT   : a removed line break; counts as a source line, reads as a space
#   PBREAK : a forced paragraph break; does not count as a line
#   HEAD   : the paragraph that follows is a heading
#   ITEM   : a list item starts here
#   ABS_O / ABS_C : abstract begins / ends
# --------------------------------------------------------------------------
SOFT = "\x01"
HEAD = "\x02"
PBREAK = "\x03"
ABS_O = "\x05"
ABS_C = "\x06"
ITEM = "\x07"
DOLLAR = "\x0e"
MARKERS = SOFT + HEAD + PBREAK + ABS_O + ABS_C + ITEM


def _breaks(s: str) -> int:
    return s.count("\n") + s.count(SOFT)


def _soft(s: str) -> str:
    return SOFT * _breaks(s)


def _sub_keep(pattern, repl: str, text: str, flags: int = 0) -> str:
    """re.sub that keeps the source line count (removed newlines become SOFT)."""
    rx = pattern if hasattr(pattern, "sub") else re.compile(pattern, flags)
    return rx.sub(lambda m: repl + _soft(m.group(0)), text)


# ==========================================================================
# LaTeX extraction
# ==========================================================================

_TEX_DROP_ENVS = [
    "thebibliography", "figure", "figure*", "table", "table*", "tabular", "tabular*",
    "tabularx", "longtable", "tikzpicture", "tikzcd", "lstlisting", "verbatim",
    "Verbatim", "minted", "filecontents", "filecontents*", "comment", "quote",
    "quotation", "wrapfigure", "algorithm", "algorithmic", "picture", "lstlisting*",
    "tcolorbox", "forest",
]
_TEX_MATH_ENVS = [
    "equation", "equation*", "align", "align*", "alignat", "alignat*", "gather",
    "gather*", "multline", "multline*", "flalign", "flalign*", "eqnarray",
    "eqnarray*", "displaymath", "math", "dmath", "dmath*", "subequations",
]
_TEX_HEADINGS = {"part", "chapter", "section", "subsection", "subsubsection",
                 "paragraph", "subparagraph"}
_TEX_REFS = {"ref", "eqref", "cref", "Cref", "autoref", "pageref", "vref", "nameref",
             "lref", "lrefx"}
_TEX_DROP = {
    "cite", "citep", "citet", "citealp", "citeauthor", "citeyear", "nocite", "label",
    "url", "bibliographystyle", "bibliography", "input", "include", "includeonly",
    "hypertarget", "vspace", "hspace", "newcommand", "renewcommand", "providecommand",
    "DeclareMathOperator", "setlength", "addtolength", "addtocounter", "setcounter",
    "usepackage", "documentclass", "includegraphics", "footnote", "footnotemark",
    "footnotetext", "thispagestyle", "pagestyle", "maketitle", "tableofcontents",
    "title", "subtitle", "author", "date", "thanks", "address", "email", "keywords",
    "subjclass", "runninghead", "markboth", "markright", "hypersetup", "bibitem",
    "newtheorem", "theoremstyle", "numberwithin", "def", "let", "phantomsection",
    "addcontentsline", "enlargethispage", "caption", "DeclareResultEvidence",
    "papersectiontarget", "marginpar", "todo", "index", "glossary", "color",
    "definecolor", "pdfbookmark", "raisebox", "rule", "fbox",
}
_TEX_SYMBOLS = {
    "ldots": "...", "dots": "...", "cdots": "...", "textellipsis": "...",
    "textendash": "\u2013", "textemdash": "\u2014", "S": "\u00a7", "ss": "ss",
    "o": "o", "O": "O", "ae": "ae", "AE": "AE", "oe": "oe", "aa": "a", "AA": "A",
    "l": "l", "L": "L", "i": "i", "j": "j", "LaTeX": "LaTeX", "TeX": "TeX",
    "par": PBREAK, "newline": " ", "linebreak": " ", "quad": " ", "qquad": " ",
    "noindent": "", "indent": "", "medskip": PBREAK, "bigskip": PBREAK,
    "smallskip": PBREAK, "newpage": PBREAK, "clearpage": PBREAK, "centering": "",
    "raggedright": "", "item": PBREAK + ITEM, "appendix": PBREAK, "today": "today",
    "textbackslash": " ", "slash": "/", "enspace": " ", "thinspace": " ",
    "hfill": " ", "vfill": " ", "break": " ", "nobreak": "", "allowbreak": "",
    "protect": "", "relax": "", "leavevmode": "", "sloppy": "", "fussy": "",
    "small": "", "footnotesize": "", "scriptsize": "", "large": "", "Large": "",
    "normalsize": "", "bfseries": "", "itshape": "", "em": "", "rmfamily": "",
    "ttfamily": "", "sffamily": "", "scshape": "", "upshape": "", "mdseries": "",
    "noteprovenance": "", "paperprovenance": "", "tiny": "", "huge": "", "Huge": "",
}
_TEX_ACCENTS = set("\"'`^~=.") | {"H", "v", "u", "c", "d", "b", "t", "k", "r"}


def _read_group(text: str, i: int, open_c: str = "{", close_c: str = "}") -> Tuple[str, int]:
    """Read a balanced group starting at text[i] == open_c.  Returns (inner, end)."""
    depth = 0
    j = i
    n = len(text)
    while j < n:
        c = text[j]
        if c == "\\" and j + 1 < n:
            j += 2
            continue
        if c == open_c:
            depth += 1
        elif c == close_c:
            depth -= 1
            if depth == 0:
                return text[i + 1:j], j + 1
        elif open_c == "[" and c == "\n" and j + 1 < n and text[j + 1] == "\n":
            break  # an optional argument never spans a blank line
        j += 1
    return text[i + 1:], n


def _looks_nonprose(arg: str) -> bool:
    """An argument that is a URL, path, label, number or identifier, not prose."""
    a = arg.strip().strip(MARKERS)
    if not a:
        return True
    if re.search(r"\s", a):
        return bool(re.match(r"(https?://|www\.)", a))
    if re.search(r"[/:\\._#=@]", a):
        return True
    if re.search(r"[a-z][A-Z]", a):
        return True  # CamelCase identifier (e.g. a Lean declaration name)
    if re.fullmatch(r"[\w-]*\d[\w-]*", a):
        return True
    return False


def _collect_tex_macros(raw: str) -> Dict[str, str]:
    """Zero-argument \\newcommand / \\def definitions (used to expand prose macros)."""
    macros: Dict[str, str] = {}
    rx = re.compile(r"\\(?:re|provide)?newcommand\*?\s*\{?\\([A-Za-z@]+)\}?\s*(\[\d\])?\s*\{")
    for m in rx.finditer(raw):
        if m.group(2):
            continue
        body, _ = _read_group(raw, m.end() - 1)
        if "#" not in body and len(body) < 200:
            macros[m.group(1)] = body
    for m in re.finditer(r"\\def\\([A-Za-z@]+)\{", raw):
        body, _ = _read_group(raw, m.end() - 1)
        if "#" not in body and len(body) < 200:
            macros[m.group(1)] = body
    return macros


class _TexScanner:
    def __init__(self, macros: Dict[str, str]):
        self.macros = macros

    def scan(self, text: str, depth: int = 0) -> str:
        out: List[str] = []
        i = 0
        n = len(text)
        while i < n:
            c = text[i]
            if c == "\\":
                i = self._command(text, i, out, depth)
                continue
            if c in "{}":
                i += 1
                continue
            if c == "~":
                out.append(" ")
                i += 1
                continue
            out.append(c)
            i += 1
        return "".join(out)

    def _command(self, text: str, i: int, out: List[str], depth: int) -> int:
        n = len(text)
        if i + 1 >= n:
            return i + 1
        nxt = text[i + 1]
        if not (nxt.isalpha() or nxt == "@"):
            # control symbols
            if nxt == "\\":
                out.append(" ")
                j = i + 2
                if j < n and text[j] == "[":
                    grp, j = _read_group(text, j, "[", "]")
                    out.append(_soft(grp))
                return j
            if nxt in "&%$#_{}":
                out.append(nxt)
                return i + 2
            if nxt in _TEX_ACCENTS:
                j = i + 2
                if j < n and text[j] == "{":
                    grp, j = _read_group(text, j)
                    out.append(re.sub(r"[^A-Za-z]", "", grp)[:1] or "")
                    return j
                if j < n and text[j].isalpha():
                    out.append(text[j])
                    return j + 1
                return j
            if nxt in ",;:! >\n\t":
                out.append(" " if nxt != "\n" else " " + SOFT)
                return i + 2
            if nxt == "/":
                return i + 2
            return i + 2
        m = re.match(r"[A-Za-z@]+\*?", text[i + 1:])
        name = m.group(0)
        bare = name.rstrip("*")
        j = i + 1 + len(name)
        # accent commands with letter names (\H{o}, \v{c})
        if bare in _TEX_ACCENTS and j < n and text[j] in "{ ":
            k = j
            while k < n and text[k] == " ":
                k += 1
            if k < n and text[k] == "{":
                grp, k = _read_group(text, k)
                out.append(re.sub(r"[^A-Za-z]", "", grp)[:1])
                return k
            if k < n and text[k].isalpha():
                out.append(text[k])
                return k + 1
        if bare in self.macros and depth < 6:
            out.append(self.scan(self.macros[bare], depth + 1))
            # swallow an empty {} after a macro
            if text[j:j + 2] == "{}":
                j += 2
            return j
        if bare in _TEX_SYMBOLS:
            out.append(_TEX_SYMBOLS[bare])
            if text[j:j + 2] == "{}":
                j += 2
            if bare == "item" and j < n and text[j] == "[":
                grp, j = _read_group(text, j, "[", "]")
                out.append(_soft(grp))
            return j
        # collect arguments: [opt]* {arg}* (no whitespace between)
        opts: List[str] = []
        args: List[str] = []
        k = j
        while k < n and text[k] in "[{":
            if text[k] == "[":
                if bare in ("begin", "end") and not args:
                    break
                grp, k = _read_group(text, k, "[", "]")
                opts.append(grp)
            else:
                grp, k = _read_group(text, k)
                args.append(grp)
                if bare in ("begin", "end"):
                    break
        dropped = "".join(opts)
        if bare in ("begin", "end"):
            env = args[0] if args else ""
            if bare == "begin":
                # theorem title in [..] after \begin{env}
                while k < n and text[k] == "[":
                    grp, k = _read_group(text, k, "[", "]")
                    dropped += grp
                marker = PBREAK + (ABS_O if env == "abstract" else "")
            else:
                marker = (ABS_C if env == "abstract" else "") + PBREAK
            out.append(marker + _soft(dropped))
            return k
        if bare in _TEX_HEADINGS:
            title = args[-1] if args else ""
            out.append(PBREAK + HEAD + self.scan(title, depth + 1) + PBREAK
                       + _soft(dropped + "".join(args[:-1])))
            return k
        if bare in _TEX_REFS:
            out.append(" REF " + _soft(dropped + "".join(args)))
            return k
        if bare in _TEX_DROP:
            out.append(_soft(dropped + "".join(args)))
            return k
        # generic command: keep prose-like arguments, drop identifiers/URLs
        pieces = []
        for a in args:
            if _looks_nonprose(a):
                pieces.append(_soft(a))
            else:
                pieces.append(self.scan(a, depth + 1))
        out.append(" ".join(pieces) if len(pieces) > 1 else "".join(pieces))
        out.append(_soft(dropped))
        return k


def tex_to_stream(raw: str) -> str:
    """Convert LaTeX source to the marker stream (line count preserved)."""
    t = raw.replace("\r\n", "\n").replace("\r", "\n")
    macros = _collect_tex_macros(t)
    # comments: a comment eats its newline and the next line's indentation
    t = re.sub(r"(?<!\\)%[^\n]*(\n[ \t]*)?", lambda m: _soft(m.group(0)), t)
    t = t.replace("\\$", DOLLAR)
    # body only
    b = re.search(r"\\begin\{document\}", t)
    if b:
        t = _soft(t[:b.end()]) + t[b.end():]
    e = re.search(r"\\end\{document\}", t)
    if e:
        t = t[:e.start()] + _soft(t[e.start():])
    # dropped environments (non-prose)
    names = "|".join(re.escape(x) for x in _TEX_DROP_ENVS)
    t = _sub_keep(re.compile(r"\\begin\{(" + names + r")\}.*?\\end\{\1\}", re.S), PBREAK, t)
    # display math environments
    names = "|".join(re.escape(x) for x in _TEX_MATH_ENVS)
    t = _sub_keep(re.compile(r"\\begin\{(" + names + r")\}.*?\\end\{\1\}", re.S), " MATH ", t)
    t = _sub_keep(re.compile(r"\$\$.*?\$\$", re.S), " MATH ", t)
    t = _sub_keep(re.compile(r"(?<!\\)\\\[.*?\\\]", re.S), " MATH ", t)
    t = _sub_keep(re.compile(r"(?<!\\)\\\(.*?\\\)", re.S), " MATH ", t)
    t = _sub_keep(re.compile(r"\$(?:\\.|[^$\\])+?\$", re.S), " MATH ", t)
    t = re.sub(r"\\verb(.)(.*?)\1", " CODE ", t)
    t = _TexScanner(macros).scan(t)
    t = t.replace(DOLLAR, "$")
    t = t.replace("---", "\u2014").replace("--", "\u2013")
    t = t.replace("``", '"').replace("''", '"')
    return t


# ==========================================================================
# Markdown / plain-text / pdftotext extraction
# ==========================================================================

_LIGATURES = {"\ufb01": "fi", "\ufb02": "fl", "\ufb00": "ff", "\ufb03": "ffi",
              "\ufb04": "ffl", "\u2019": "'", "\u2018": "'", "\u201c": '"',
              "\u201d": '"', "\u00ad": "", "\u011f": "\u00a7", "\u00a0": " ",
              "\u2009": " ", "\u200b": "", "\u2002": " ", "\u2003": " "}
_WORDLIKE = re.compile(r"[(\"'\[]?(?:[A-Za-z][a-z]+(?:[-'][A-Za-z][a-z]*)*|a|A|I)[,.;:)\"'\]]*")
_REF_HEAD = re.compile(
    r"^(?:\d+(?:\.\d+)*\.?\s*|[IVX]+\.\s*)?(references|bibliography|works cited|literature cited|"
    r"acknowledge?ments?|funding|conflicts? of interest|data availability|author contributions)\b",
    re.I)
_JUNK_LINE = re.compile(
    r"^\s*(?:\d{1,4}|page \d+( of \d+)?|arxiv:\S+.*|https?://\S+|doi:?\s*\S+|"
    r"permission to make digital.*|.*\u00a9.*|copyright.*|acm isbn.*|isbn.*|issn.*|"
    r"licensed under.*|this work is licensed.*|received .*accepted.*|keywords?:.*|"
    r"(?:mathematics )?subject classification.*|msc ?20\d\d.*|\*?corresponding author.*|ccs concepts.*|"
    r"acm reference format.*|keywords\b.*|index terms\b.*|in proceedings of.*|proceedings of the .*|"
    r"preprint\b.*|submitted to .*|∗.*)\s*$", re.I)
_EMAIL = re.compile(r"\S+@\S+\.[a-z]{2,}", re.I)


def _mathy_line(line: str) -> bool:
    toks = line.split()
    if not toks:
        return False
    words = sum(1 for t in toks if _WORDLIKE.fullmatch(t))
    if len(toks) <= 2:
        return words == 0
    return words / len(toks) < 0.5


def _dedent(col: List[Tuple[int, str]]) -> List[Tuple[int, str]]:
    """Remove a column's common (modal) left margin, keeping paragraph indents."""
    ind = [len(l) - len(l.lstrip(" ")) for _, l in col if l.strip()]
    if not ind:
        return col
    base = statistics.mode(ind)
    return [(ln, l[min(base, len(l) - len(l.lstrip(" "))):]) for ln, l in col]


def _split_columns(page: List[Tuple[int, str]]) -> List[Tuple[int, str]]:
    """Split a pdftotext -layout page into left column then right column."""
    ne = [l for _, l in page if l.strip()]
    if len(ne) < 12:
        return _dedent(page)
    width = max(len(l) for l in ne)
    if width < 70:
        return _dedent(page)
    best_c, best = 0, 0
    for c in range(int(width * 0.3), int(width * 0.7)):
        cnt = 0
        for l in ne:
            if len(l) > c + 2 and l[c] == " " and l[c - 1] == " " and l[:c].strip() and l[c:].strip():
                cnt += 1
        if cnt > best:
            best, best_c = cnt, c
    if best < 0.35 * len(ne):
        return _dedent(page)
    left: List[Tuple[int, str]] = []
    right: List[Tuple[int, str]] = []
    for ln, l in page:
        if len(l) <= best_c or not l[best_c:].strip():
            left.append((ln, l))
            continue
        p = None
        for off in (0, -1, 1, -2, 2, -3, 3, -4, 4):
            q = best_c + off
            if 0 < q < len(l) and l[q] == " " and l[q - 1] == " ":
                p = q
                break
        if p is None:
            if not l[:best_c].strip():
                right.append((ln, l[best_c:]))
            else:
                left.append((ln, l))  # full-width line
            continue
        lt, rt = l[:p].rstrip(), l[p:]
        if lt.strip():
            left.append((ln, lt))
        if rt.strip():
            right.append((ln, rt))
    return _dedent(left) + _dedent(right)


def _heading_text(line: str, pdf: bool) -> Optional[str]:
    s = line.strip()
    m = re.match(r"^#{1,6}\s+(.*?)\s*(\{[#.][^}]*\})?\s*$", s)
    if m:
        return m.group(1).strip("* ")
    if not pdf:
        return None
    if len(s) > 80 or len(s) < 3 or s.endswith((".", ",", ";", ":")) and not re.match(r"^\d", s):
        return None
    if re.match(r"^(?:\d+(?:\.\d+)*\.?|[IVX]+\.|[A-Z]\.)\s+[A-Z][A-Za-z ,:&'\-\u2013()]{2,70}$", s):
        return s
    if re.fullmatch(r"[A-Z][A-Z &\-]{3,40}", s) and len(s.split()) <= 5:
        return s
    if re.fullmatch(r"(Abstract|Introduction|References|Bibliography|Acknowledge?ments?|Conclusions?)\.?", s):
        return s
    return None


def md_to_stream(raw: str) -> Tuple[str, List[int]]:
    """Convert markdown / pdftotext text to the marker stream.

    Returns (stream, line_map) where stream line k (counting \\n and SOFT) maps
    to source line line_map[k] (1-based).
    """
    t = raw.replace("\r\n", "\n").replace("\r", "\n")
    for a, b in _LIGATURES.items():
        t = t.replace(a, b)
    t = re.sub(r"[\x00-\x08\x0b\x0e-\x1f]", lambda m: "\f" if m.group(0) == "\f" else "", t)
    src = t.split("\n")
    lines = [(i + 1, l) for i, l in enumerate(src)]
    nonempty = [l for _, l in lines if l.strip()]
    med_len = statistics.median([len(l) for l in nonempty]) if nonempty else 0
    pandoc = bool(re.search(r"\$\$|\[@|^:::|\{reference-type=|^#{1,6} ", t, re.M))
    pdf = ("\f" in t) or (med_len < 130 and not pandoc)
    # pages and columns
    if pdf:
        pages: List[List[Tuple[int, str]]] = [[]]
        for ln, l in lines:
            if "\f" in l:
                pages.append([])
                l = l.replace("\f", "")
            pages[-1].append((ln, l.expandtabs()))
        lines = []
        for pg in pages:
            if pg:
                lines.extend(_split_columns(pg))
    out: List[Tuple[int, str]] = []
    in_code = False
    skip_refs = False
    skip_to_end = False
    abstract_state = 0  # 0 none, 1 expecting abstract paragraph, 2 inside
    prev_text = ""
    indents: List[int] = []
    for ln, l in lines:
        if l.strip():
            indents.append(len(l) - len(l.lstrip()))
    mode_indent = statistics.mode(indents) if indents else 0
    lens = [len(l.strip()) for _, l in lines if l.strip()]
    typical = statistics.median(lens) if lens else 0
    for ln, l in lines:
        s = l.strip()
        if skip_to_end:
            continue
        if s.startswith("```") or s.startswith("~~~"):
            in_code = not in_code
            continue
        if in_code:
            continue
        if not s:
            out.append((ln, ""))
            prev_text = ""
            continue
        head = _heading_text(l, pdf)
        if head is not None:
            if _REF_HEAD.match(head.strip("*# ")):
                skip_refs = True
                if pdf and re.match(r"^(\d+(\.\d+)*\.?\s*)?(references|bibliography)", head.strip("*# "), re.I) \
                        and ln > 0.5 * len(src):
                    skip_to_end = True  # a table-of-contents entry early on is not the reference list
                continue
            skip_refs = False
            if re.fullmatch(r"abstract\.?", head.strip("*# "), re.I):
                abstract_state = 1
                out.append((ln, PBREAK))
                prev_text = ""
                continue
            if abstract_state == 2:
                out.append((ln, ABS_C))
            abstract_state = 0
            out.append((ln, PBREAK + HEAD + head + PBREAK))
            prev_text = ""
            continue
        if skip_refs:
            continue
        if re.match(r"^:{3,}\s*(\{[^}]*(#refs|\.references)[^}]*\}|thebibliography|references)\b", s):
            skip_to_end = True  # pandoc bibliography block
            continue
        if s.startswith(":::") or re.match(r"^\[\^?[^\]]+\]:", s) or s.startswith("|") \
                or re.match(r"^[+|][-=+:| ]+$", s) or s.startswith("<!--"):
            continue
        if _JUNK_LINE.match(s) or (pdf and _EMAIL.search(s) and len(s.split()) < 12):
            continue
        if s.startswith(">"):
            continue  # quotations are someone else's voice
        if re.match(r"^\s*(\*\*|__)?abstract(\*\*|__)?[.:\u2014\-]", s, re.I):
            s = re.sub(r"^\s*(\*\*|__)?abstract(\*\*|__)?[.:\u2014\-]\s*", "", s, flags=re.I)
            out.append((ln, PBREAK + ABS_O + s))
            abstract_state = 2
            prev_text = s
            continue
        prefix = ""
        if abstract_state == 1:
            prefix = ABS_O
            abstract_state = 2
        elif abstract_state == 2 and not prev_text:
            out.append((ln, ABS_C))
            abstract_state = 0
        item = re.match(r"^([-*+\u2022\u25e6\u2023\u25aa]|\d{1,2}[.)]|\([ivx]{1,4}\)|\([a-z]\))\s+", s)
        if item:
            prefix += PBREAK + ITEM
            s = s[item.end():]
        elif pdf:
            ind = len(l) - len(l.lstrip())
            short_prev = prev_text and len(prev_text) < 0.7 * typical and prev_text.rstrip().endswith((".", "?", "!", ":"))
            if prev_text and (mode_indent + 2 <= ind <= mode_indent + 14 or short_prev):
                prefix += PBREAK
            if "$" not in s and _mathy_line(s):
                s = "MATH"
        out.append((ln, prefix + s))
        prev_text = s
    if abstract_state == 2:
        out.append((out[-1][0] if out else 1, ABS_C))
    # dehyphenate across lines (pdf wraps)
    for k in range(len(out) - 1):
        ln, s = out[k]
        if re.search(r"[a-z]-$", s):
            m2 = k + 1
            nxt = out[m2][1]
            mm = re.match(r"^([a-z][\w']*)([,.;:)]*)\s*(.*)$", nxt)
            if mm:
                out[k] = (ln, s[:-1] + mm.group(1) + mm.group(2))
                out[m2] = (out[m2][0], mm.group(3))
    line_map = [ln for ln, _ in out]
    stream = "\n".join(s for _, s in out)
    stream = _clean_md_inline(stream)
    return stream, line_map


def _clean_md_inline(t: str) -> str:
    t = t.replace("\\$", DOLLAR)
    # raw LaTeX figures, tables and drawings embedded in Markdown are layout, not prose
    t = _sub_keep(re.compile(r"\\begin\{(figure\*?|table\*?|tikzpicture|tikzcd|tabular)\}.*?\\end\{\1\}", re.S), PBREAK, t)
    t = _sub_keep(re.compile(r"\$\$.*?\$\$", re.S), " MATH ", t)
    t = _sub_keep(re.compile(r"(?<!\\)\\\[.*?\\\]", re.S), " MATH ", t)
    t = _sub_keep(re.compile(r"(?<!\\)\\\(.*?\\\)", re.S), " MATH ", t)
    t = _sub_keep(re.compile(r"\$(?:\\.|[^$\\\n]|\n(?!\n))+?\$", re.S), " MATH ", t)
    t = _sub_keep(re.compile(r"\\begin\{(equation|align|gather|multline)\*?\}.*?\\end\{\1\*?\}", re.S), " MATH ", t)
    # citations and cross references
    t = _sub_keep(re.compile(r"\[-?@[^\]]*\]"), "", t)
    t = _sub_keep(re.compile(r"\[(?:\\.|[^\]\\])*\]\(#[^)]*\)(?:\{[^}]*\})?"), " REF ", t)
    t = re.sub(r"\[((?:\\.|[^\]\\\n])*)\]\((?:https?:|mailto:)[^)\s]*\)(?:\{[^}]*\})?", r"\1", t)
    # reference-style and relative links keep their text; HTML tags are layout
    t = re.sub(r"\[((?:\\.|[^\]\\\n])*)\]\[[^\]\n]*\]", r"\1", t)
    t = re.sub(r"\[((?:\\.|[^\]\\\n])*)\]\((?!#)[^)\s]*\)(?:\{[^}]*\})?", r"\1", t)
    t = re.sub(r"<(?:/?[A-Za-z][\w-]*)(?:\s[^<>]*)?/?>", "", t)
    t = re.sub(r"(?<![\w.])@[A-Za-z][\w:.\-]*[\w]", "", t)
    # numeric and author-year citations left by PDF extraction
    t = re.sub(r"\[\d+(?:\s*[,–\-]\s*\d+)*(?:,\s*[^\]\n]{0,20})?\]", "", t)
    t = re.sub(r"\[[A-Z][A-Za-z+\-]{0,8}\d{2}[a-z]?(?:\s*[,;]\s*[A-Z][A-Za-z+\-]{0,8}\d{2}[a-z]?)*"
               r"(?:,\s*[^\]\n]{0,25})?\]", "", t)
    t = re.sub(r"\((?:(?:see |cf\. |e\.g\., )?[A-Z][A-Za-z'\-]+(?: et al\.)?(?:,? (?:and|&) [A-Z][A-Za-z'\-]+)?,? "
               r"(?:19|20)\d\d[a-z]?(?:[;,] ?)?)+\)", "", t)
    t = re.sub(r"\[\^[^\]]+\]", "", t)
    t = re.sub(r"\{[#.][\w:.\-]+(?:\s[^}]*)?\}", "", t)
    t = re.sub(r"\{reference-type=[^}]*\}", "", t)
    # emphasis markup
    t = t.replace("**", "").replace("__", "")
    t = re.sub(r"(?<![\w*])\*(?=\S)|(?<=\S)\*(?![\w*])", "", t)
    t = re.sub(r"(?<![\w])_(?=\w)|(?<=\w)_(?![\w])", "", t)
    t = re.sub(r"`[^`\n]*`", " CODE ", t)
    t = t.replace("\\", " ")
    t = t.replace(DOLLAR, "$")
    t = re.sub(r"[\u25a1\u220e\u25a0]|\bQ\.?E\.?D\.?", "", t)
    t = re.sub(r"\(\s*[,;]?\s*\)", "", t)
    return t


# ==========================================================================
# Paragraphs and sentences
# ==========================================================================

_ABBREV = {
    "e.g", "i.e", "cf", "viz", "resp", "vs", "al", "fig", "figs", "eq", "eqs", "eqn", "eqns",
    "thm", "thms", "prop", "props", "lem", "cor", "def", "defn", "rem", "sec", "secs",
    "sect", "ch", "chap", "eds", "ref", "refs", "dr", "mr", "mrs", "ms", "prof", "st",
    "jr", "sr", "approx", "ca", "conj", "ibid", "cit", "loc", "a.e", "a.s", "w.r.t",
    "s.t", "wlog", "i.i.d", "o.g", "n.b", "fn", "ex",
}
# abbreviations that end a word only when a number follows ("p. 12", "no. 3")
_ABBREV_NUM = {"p", "pp", "no", "nos", "vol", "vols", "art", "ed", "app", "eq", "thm", "sec", "ch",
               "fig", "§", "lemma", "theorem", "section", "chapter", "part"}
_TOKEN = re.compile(r"MATH|REF|CODE|[A-Za-z\u00c0-\u024f][A-Za-z\u00c0-\u024f'\-]*|\d+(?:\.\d+)?")
_PLACEHOLDERS = {"MATH", "REF", "CODE"}


class Sentence:
    __slots__ = ("text", "line", "para", "index", "tokens", "alpha", "first", "pos")

    def __init__(self, text: str, line: int, para: int, index: int, pos: str = "mid"):
        self.text = text
        self.line = line
        self.para = para
        self.index = index
        self.pos = pos
        self.tokens = _TOKEN.findall(text)
        self.alpha = [w for w in self.tokens if w not in _PLACEHOLDERS and not w[0].isdigit()]
        self.first = self.alpha[0].lower() if self.alpha and self.tokens and self.tokens[0] == self.alpha[0] else ""

    @property
    def n(self) -> int:
        return len(self.tokens)


class Paragraph:
    __slots__ = ("text", "line", "kind", "sentences", "abstract", "after_heading", "items")

    def __init__(self, text: str, line: int, kind: str):
        self.text = text
        self.line = line
        self.kind = kind
        self.sentences: List[Sentence] = []
        self.abstract = False
        self.after_heading = False
        self.items = 0


def split_sentences(text: str) -> List[Tuple[int, int]]:
    """Split prose into sentence spans (start, end).  Robust to common
    mathematical abbreviations (e.g., i.e., cf., Thm., Prop., et al., Fig., Sec.),
    initials, and decimals."""
    spans: List[Tuple[int, int]] = []
    start = 0
    n = len(text)
    for m in re.finditer(r"([.!?]+)([\"')\]]*)(\s+)", text):
        end_punct = m.end(2)
        nxt_i = m.end()
        if nxt_i >= n:
            break
        nxt = text[nxt_i]
        if not (nxt.isupper() or nxt.isdigit() or nxt in "(\"'[\u00a7"):
            continue
        punct = m.group(1)
        if punct.endswith(".") and not m.group(2):
            before = text[start:m.start()].split()
            tok = before[-1] if before else ""
            core = tok.lstrip("([\"'").lower()
            if core in _ABBREV or re.fullmatch(r"(?:[a-z]\.)+[a-z]", core):
                continue
            if re.fullmatch(r"[A-Z]", tok.lstrip("([\"'")):
                continue  # initial: "G. H. Hardy"
            if nxt.isdigit() and core in _ABBREV_NUM:
                continue
            if core in ("et", "al") or (core == "al" and before[-2:-1] == ["et"]):
                continue
        spans.append((start, end_punct))
        start = nxt_i
    if start < n and text[start:].strip():
        spans.append((start, n))
    return spans


_LABEL = re.compile(
    r"^\s*(?:Theorem|Lemma|Proposition|Corollary|Definition|Remark|Example|Conjecture|Claim|"
    r"Problem|Question|Proof|Notation|Hypothesis|Assumption|Fact|Observation|Exercise|Main Theorem)"
    r"(?:\s+[\dA-Z][\w.]*)?(?:\s*\([^)]{0,80}\))?\s*[.:]\s*")


class Document:
    def __init__(self, path: str, paragraphs: List[Paragraph], abstract_words: Optional[int],
                 list_items: int, fmt: str, catalogue: int = 0):
        self.path = path
        self.catalogue = catalogue
        self.paragraphs = paragraphs
        self.abstract_words = abstract_words
        self.list_items = list_items
        self.fmt = fmt
        self.sentences = [s for p in paragraphs if p.kind == "para" for s in p.sentences]
        self.headings = sum(1 for p in paragraphs if p.kind == "heading")
        self.alpha_words = sum(len(s.alpha) for s in self.sentences)
        self.tokens = sum(s.n for s in self.sentences)


def _build_paragraphs(stream: str, line_map: Optional[List[int]] = None) -> Tuple[List[Paragraph], Optional[int], int]:
    sep = re.compile(r"\n[ \t" + SOFT + r"]*\n[\s" + SOFT + r"]*|" + PBREAK + r"[\s" + SOFT + PBREAK + r"]*")
    paras: List[Paragraph] = []
    catalogue = [0]
    in_abs = False
    abs_words: Optional[int] = None
    items = 0
    pos = 0
    lineno = 0

    def to_line(k: int) -> int:
        if line_map is None:
            return k + 1
        if not line_map:
            return 1
        return line_map[min(k, len(line_map) - 1)]

    def emit(seg: str, start_line: int):
        nonlocal in_abs, abs_words, items
        lead = len(seg) - len(seg.lstrip(" \t\n" + SOFT))
        start_line += _breaks(seg[:lead])
        seg = seg[lead:]
        if ABS_O in seg:
            in_abs = True
            abs_words = abs_words or 0
        is_item = ITEM in seg
        if is_item:
            items += seg.count(ITEM)
        closes = ABS_C in seg
        is_head = seg.startswith(HEAD)
        # same-length normalisation for offset -> line mapping
        norm = "".join(" " if ch in "\n\t" + MARKERS else ch for ch in seg)
        if not norm.strip():
            if closes:
                in_abs = False
            return
        if is_head:
            p = Paragraph(re.sub(r"\s+", " ", norm).strip(), to_line(start_line), "heading")
            paras.append(p)
            if closes:
                in_abs = False
            return
        lm = _LABEL.match(norm)
        if lm:
            norm = " " * lm.end() + norm[lm.end():]
        p = Paragraph(re.sub(r"\s+", " ", norm).strip(), to_line(start_line), "para")
        p.abstract = in_abs
        p.items = 1 if is_item else 0
        spans = split_sentences(norm)
        k = len(paras)
        for si, (a, b) in enumerate(spans):
            txt = re.sub(r"\s+", " ", norm[a:b]).strip()
            if not txt:
                continue
            s = Sentence(txt, to_line(start_line + _breaks(seg[:a])), k, 0)
            if len(s.alpha) >= 3 and len(s.alpha) >= 0.34 * s.n:
                if _catalogue(txt):
                    catalogue[0] += 1  # a list typeset as one sentence, not prose
                    continue
                p.sentences.append(s)
        if p.sentences:
            p.sentences[0].pos = "first"
            if len(p.sentences) > 1:
                p.sentences[-1].pos = "last"
        if in_abs and abs_words is not None:
            abs_words += sum(len(s.alpha) + sum(1 for t in s.tokens if t in _PLACEHOLDERS) for s in p.sentences)
        paras.append(p)
        if closes:
            in_abs = False

    for m in sep.finditer(stream):
        emit(stream[pos:m.start()], lineno)
        lineno += _breaks(stream[pos:m.end()])
        pos = m.end()
    emit(stream[pos:], lineno)
    prev_head = False
    idx = 0
    for p in paras:
        if p.kind == "heading":
            prev_head = True
            continue
        if not p.sentences:
            continue
        p.after_heading = prev_head
        prev_head = False
        for s in p.sentences:
            s.index = idx
            idx += 1
    _build_paragraphs.last_catalogue = catalogue[0]
    return paras, abs_words, items


def _catalogue(txt: str) -> bool:
    """A semicolon-separated catalogue of short noun phrases (e.g. a list of
    formal results typeset as one sentence) is a list, not a sentence."""
    segs = [x for x in txt.split(";") if x.strip()]
    if len(segs) < 5:
        return False
    return statistics.mean(len(_TOKEN.findall(x)) for x in segs) <= 8


def load_document(path: str) -> Document:
    with open(path, encoding="utf-8", errors="replace") as fh:
        raw = fh.read()
    return document_from_text(raw, path)


def document_from_text(raw: str, path: str = "<text>", fmt: Optional[str] = None) -> Document:
    if fmt is None:
        fmt = "tex" if path.endswith(".tex") or (
            "\\begin{document}" in raw or re.search(r"\\(?:section|documentclass)\{", raw)) else "md"
    if fmt == "tex":
        stream = tex_to_stream(raw)
        paras, abs_words, items = _build_paragraphs(stream, None)
    else:
        stream, line_map = md_to_stream(raw)
        paras, abs_words, items = _build_paragraphs(stream, line_map)
    return Document(path, paras, abs_words if abs_words else None, items, fmt,
                    getattr(_build_paragraphs, "last_catalogue", 0))


# ==========================================================================
# Features
# ==========================================================================

def _rx(p: str, flags: int = re.I):
    return re.compile(p, flags)


RX = {
    "em_dash": _rx("\u2014"),
    "en_dash": _rx(r"(?<=\s)\u2013(?=\s)"),
    "contrast": [
        _rx(r"\bnot\b(?!\s+only\b)[^.;:?!]{1,80}?,\s*but\b"),
        _rx(r"\bnot\b(?!\s+only\b)[^.;:?!,]{1,60}?\s+but\b(?!\s+also)"),
        _rx(r",\s+not\s+(?!only\b|necessarily\b|all\b|to\b|even\b|least\b|just\b(?!\s+\w+\s+but))\w+"),
        _rx(r"\brather than\b"),
        _rx(r"\binstead of\b"),
    ],
    "meta_any": _rx(
        r"\b(?:here is|here are|the point is|the point here|the (?:key|main|crucial|central|real) "
        r"(?:idea|point|step|observation|insight|input|move|difficulty|ingredient)|it is worth|in other words|"
        r"we now turn|now we turn|the hard step|the hard part|the mechanism|the upshot|put differently|"
        r"said differently|what matters)\b"),
    "meta_open": _rx(r"^(?:(?:But|And|So|Thus|Here),?\s+)?(?:Crucially|Importantly|Concretely|Notably|Specifically|"
                     r"This (?:section|subsection|appendix|part|paper|note|record|report)\b)", 0),
    "note_that": _rx(r"\bnote that\b"),
    "intensifier": _rx(
        r"\b(?:precisely|exactly|genuinely|crucially|essentially|fundamentally|truly|entirely|directly|"
        r"explicitly|sharply|strictly(?!\s+(?:increasing|decreasing|positive|negative|less|greater|larger|"
        r"smaller|bigger|between|convex|concave|monotone|monotonic|contained|inside|stronger|weaker|below|"
        r"above|lower|upper|dominat\w*|subadditive|superadditive|bounded)))\b"),
    "hedge": _rx(
        r"\b(?:do(?:es)? not (?:establish|decide|settle|claim|assert|resolve)|(?:is|are) not (?:a claim|claimed|"
        r"a proof|evidence|asserted)|not a proof|remains? open|(?:is|are) left open|leaves? (?:\w+ )?open|"
        r"we (?:do not|don't|make no) claim|no (?:priority |further )?claim|not evidence|"
        r"none of (?:these|this|the) [^.]{0,40}?decides?|without claiming|is not (?:yet )?(?:proved|known) here)\b"),
    "status_ci": _rx(
        r"\b(?:Comparator|receipts?|formal(?:ly|i[sz]ed|i[sz]ation|i[sz]ations)?(?!\s+(?:power|Laurent|series|sum|"
        r"group|scheme|neighbou?rhood|completion|variable|derivative|solution|expansion|identity|groups|"
        r"character))|checked|verified|verification|verifier|records?|recorded|ledgers?|pipelines?|"
        r"evidence class(?:es)?|machine-checked|kernel-checked|audit(?:s|ed|ing)?|provenance)\b"),
    "status_cs": _rx(r"\bLean\b", 0),
    "ai_lexicon": _rx(
        r"\b(?:delv(?:e|es|ed|ing)|leverag(?:e|es|ed|ing)|showcas(?:e|es|ed|ing)|underscor(?:e|es|ed|ing)|"
        r"pivotal|seamless(?:ly)?|robust(?:ly|ness)?|notably|crucial(?:ly)?|intricate|intricacies|landscape|"
        r"realm|tapestry|navigat(?:e|es|ed|ing)|foster(?:s|ed|ing)?|streamlin(?:e|es|ed|ing)|"
        r"holistic(?:ally)?|nuanced?|comprehensive(?:ly)?|multifaceted|utili[sz](?:e|es|ed|ing|ation))\b"),
    "we": _rx(r"\bwe\b"),
    "i": _rx(r"(?<!Part )(?<!Type )(?<!Case )(?<!Class )(?<!Step )\bI(?:'m|'ve|'d|'ll)?\b(?=\s+(?:am|was|have|had|think|"
             r"believe|would|will|could|can|do|did|thank|suspect|expect|know|found|learned|learnt|mean|want|"
             r"guess|hope|claim|prove|show|use|call|write|shall|should|must|also|first|then|only|see|feel|"
             r"prefer|am|wish|owe|tried|noticed|realised|realized|recall|remember)\b)", 0),
    "passive": _rx(
        r"\b(?:is|are|was|were|be|been|being)\s+(?:not\s+)?(?:\w+ly\s+)?(?:\w+ed|shown|given|known|proved|proven|"
        r"written|chosen|taken|seen|made|found|done|built|drawn|meant|held|kept|left|obtained|defined|begun|"
        r"understood|thought|brought|sought|told|won|laid|paid|read|set|put)\b"),
    "summary_open": _rx(r"^(?:Thus|Hence|So|Therefore|Consequently|In short|In summary|In sum|Altogether|"
                        r"This is why|That is why|Taken together|Together)\b", 0),
    "let_open": _rx(r"^(?:Let|Suppose|Fix|Assume|Consider)\b", 0),
    "this_open": _rx(r"^(?:This|These|That|Those)\b", 0),
    "self_ref": _rx(r"\b(?:this|the present|our) (?:paper|note|record|revision|manuscript|article|report|work)\b"),
    "triad": _rx(
        r"(?<![\w-])((?:[A-Za-z][\w'-]*\s+){0,2}[A-Za-z][\w'-]*),\s+((?:[A-Za-z][\w'-]*\s+){0,2}[A-Za-z][\w'-]*),?\s+"
        r"(?:and|or)\s+([A-Za-z][\w'-]*)", 0),
    "paren": _rx(r"\(([^()]*)\)", 0),
    "apparatus": _rx(r"\bCODE\b|(?<![\w/])(?=[0-9a-f]*[a-f])(?=[0-9a-f]*\d)[0-9a-f]{12,64}\b|https?://\S+|"
                     r"\b(?:lake build|lake env|pip install|python -m|git clone|sha-?256|SHA-?256|commit [0-9a-f]{7,})\b", 0),
    "nominal": _rx(r"\b[A-Za-z]{3,}(?:tion|sion|ment|ness|ity|ance|ence|ism)s?\b"),
    "negation": _rx(r"\b(?:not|no|never|none|neither|nor|cannot|without)\b|n't\b"),
    "connective_open": _rx(
        r"^(?:Thus|Hence|Then|Indeed|Moreover|Furthermore|However|Now|In particular|Therefore|Consequently|"
        r"Finally|Also|Similarly|Conversely|On the other hand|Namely|Nevertheless|Nonetheless|Still|Yet|"
        r"Of course|In fact|Clearly|Obviously|Otherwise|Accordingly|Likewise|In addition|Next)\b", 0),
    "result_announce": _rx(
        r"\b(?:we (?:prove|show|establish|obtain|give|deduce|derive|construct)|our (?:main )?(?:result|theorem)s?|"
        r"the (?:main )?(?:result|theorem)s? of this (?:paper|note)|in this (?:paper|note|article|section) we)\b"),
}
_TRIAD_STOP = {"moreover", "thus", "however", "hence", "then", "also", "finally", "indeed", "now", "here",
               "first", "second", "third", "furthermore", "therefore", "so", "but", "and", "in", "if",
               "since", "when", "where", "while", "for", "as", "that", "which", "is", "are"}
_TRIAD_INNER_STOP = {"not", "whereas", "does", "do", "did", "is", "are", "was", "were", "we", "may", "can",
                     "will", "which", "that", "if", "then", "has", "have", "had", "be", "it", "course",
                     "recently", "however"}


def _count_contrast(s: Sentence) -> int:
    return sum(len(r.findall(s.text)) for r in RX["contrast"])


def _count_meta(s: Sentence) -> int:
    return len(RX["meta_any"].findall(s.text)) + (1 if RX["meta_open"].match(s.text) else 0)


def _count_status(s: Sentence) -> int:
    return len(RX["status_ci"].findall(s.text)) + len(RX["status_cs"].findall(s.text))


def _count_triad(s: Sentence) -> int:
    c = 0
    for m in RX["triad"].finditer(s.text):
        w1 = m.group(1).split()
        cut = max([i + 1 for i, w in enumerate(w1) if w.lower() in _TRIAD_INNER_STOP] or [0])
        if cut >= len(w1):
            continue
        items = [" ".join(w1[cut:]), m.group(2), m.group(3)]
        firsts = [it.split()[0] for it in items]
        if any(f in _PLACEHOLDERS for f in firsts) or any(it.split()[-1] in _PLACEHOLDERS for it in items[:2]):
            continue
        if firsts[0].lower() in _TRIAD_STOP or firsts[1].lower() in _TRIAD_STOP:
            continue
        words = [w.lower() for it in items for w in it.split()]
        if any(w in _TRIAD_INNER_STOP for w in words):
            continue  # a clause boundary, not a list
        if all(f[:1].isupper() for f in firsts):
            continue  # author lists and titles ("Kim, Kovac and Zhang")
        c += 1
    return c


def _count_paren(s: Sentence) -> int:
    c = 0
    for m in RX["paren"].finditer(s.text):
        inner = [w for w in _TOKEN.findall(m.group(1)) if w not in _PLACEHOLDERS and not w[0].isdigit() and len(w) > 1]
        if inner:
            c += 1
    return c


class Feature:
    def __init__(self, name: str, kind: str, desc: str, fn: Optional[Callable] = None,
                 floor: float = 0.0, exploratory: bool = False):
        self.name = name
        self.kind = kind          # rate | share | stat | para_share | doc
        self.desc = desc
        self.fn = fn
        self.floor = floor
        self.exploratory = exploratory


def _cnt(key: str) -> Callable[[Sentence], int]:
    rx = RX[key]
    return lambda s: len(rx.findall(s.text))


def _match(key: str) -> Callable[[Sentence], int]:
    rx = RX[key]
    return lambda s: 1 if rx.match(s.text) else 0


FEATURES: List[Feature] = [
    Feature("sent_len_mean", "stat", "mean sentence length in tokens (math placeholder = 1 token)", floor=1.0),
    Feature("sent_len_sd", "stat", "standard deviation of sentence length", floor=1.0),
    Feature("sent_len_cv", "stat", "coefficient of variation of sentence length (sd/mean)", floor=0.03),
    Feature("short_sent_share", "stat", "share of sentences with < 10 tokens", floor=0.02),
    Feature("long_sent_share", "stat", "share of sentences with > 30 tokens", floor=0.02),
    Feature("para_len_mean", "stat", "mean paragraph length in tokens", floor=5.0, exploratory=True),
    Feature("para_len_cv", "stat", "coefficient of variation of paragraph length", floor=0.05),
    Feature("em_dash_rate", "rate", "em dashes per 1000 words", _cnt("em_dash"), floor=0.5),
    Feature("en_dash_rate", "rate", "spaced en dashes used as dashes per 1000 words", _cnt("en_dash"), floor=0.5),
    Feature("contrast_rate", "rate", "contrastive framing ('not X, but Y', 'X, not Y', 'rather than', 'instead of') per 1000 words",
            _count_contrast, floor=0.5),
    Feature("meta_narration_rate", "rate", "meta-narration ('Here is', 'The point is', 'The key idea', 'Crucially', "
            "'Importantly', 'This section ...', 'The mechanism', 'The hard step', ...) per 1000 words", _count_meta, floor=0.3),
    Feature("note_that_rate", "rate", "'note that' per 1000 words", _cnt("note_that"), floor=0.3),
    Feature("intensifier_rate", "rate", "intensifiers (precisely, exactly, genuinely, directly, explicitly, ...) per 1000 words",
            _cnt("intensifier"), floor=0.5),
    Feature("hedge_rate", "rate", "boundary disclaimers ('does not establish', 'remains open', 'no claim', ...) per 1000 words",
            _cnt("hedge"), floor=0.3),
    Feature("status_vocab_rate", "rate", "workflow/status words (Lean, Comparator, receipt, formal, checked, verified, "
            "record, ledger, pipeline, evidence class) per 1000 words", _count_status, floor=0.5),
    Feature("ai_lexicon_rate", "rate", "AI-lexicon words (delve, leverage, robust, notably, crucial, landscape, ...) per 1000 words",
            _cnt("ai_lexicon"), floor=0.3),
    Feature("we_rate", "rate", "'we' per 1000 words", _cnt("we"), floor=1.0),
    Feature("i_rate", "rate", "first-person 'I' per 1000 words", _cnt("i"), floor=0.3),
    Feature("passive_share", "share", "share of sentences with a passive construction (proxy)", _cnt("passive"), floor=0.02),
    Feature("same_opener_share", "stat", "share of sentences opening with the same word as the previous sentence", floor=0.01),
    Feature("colon_rate", "rate", "colons per 1000 words (prose only)", lambda s: s.text.count(":"), floor=0.5),
    Feature("semicolon_rate", "rate", "semicolons per 1000 words", lambda s: s.text.count(";"), floor=0.5),
    Feature("para_summary_end_share", "para_share", "share of paragraphs (>= 3 sentences) whose last sentence opens "
            "with Thus/Hence/So/Therefore/In short/...", None, floor=0.02),
    Feature("paren_rate", "rate", "parentheticals containing words per 1000 words", _count_paren, floor=0.5),
    Feature("question_share", "share", "share of sentences that are questions", lambda s: 1 if s.text.rstrip("\"') ").endswith("?") else 0,
            floor=0.005),
    Feature("let_open_share", "share", "share of sentences opening with Let/Suppose/Fix/Assume/Consider", _match("let_open"),
            floor=0.01),
    Feature("triad_rate", "rate", "rule-of-three lists 'A, B, and C' per 1000 words", _count_triad, floor=0.3),
    Feature("this_open_share", "share", "share of sentences opening with This/These/That/Those", _match("this_open"),
            floor=0.01, exploratory=True),
    Feature("self_reference_rate", "rate", "'this paper/note/record/revision/...' per 1000 words", _cnt("self_ref"),
            floor=0.3, exploratory=True),
    Feature("list_item_rate", "doc", "list items per 1000 words", None, floor=0.5, exploratory=True),
    Feature("heading_rate", "doc", "headings per 1000 words", None, floor=0.3, exploratory=True),
    Feature("word_len_mean", "stat", "mean letters per word", floor=0.05, exploratory=True),
    Feature("nominalization_rate", "rate", "nominalisations (-tion, -ment, -ness, -ity, -ance, -ence, -ism) per 1000 words",
            _cnt("nominal"), floor=2.0, exploratory=True),
    Feature("negation_rate", "rate", "negations (not, no, never, none, cannot, without, n't) per 1000 words",
            _cnt("negation"), floor=1.0, exploratory=True),
    Feature("connective_open_share", "share", "share of sentences opening with a discourse connective "
            "(Thus, Hence, Then, Indeed, Moreover, However, In particular, ...)", _match("connective_open"),
            floor=0.01, exploratory=True),
    Feature("apparatus_rate", "rate", "repository apparatus in prose (inline code, hex hashes, bare URLs, shell "
            "commands, SHA-256 mentions) per 1000 words", _cnt("apparatus"), floor=0.3),
    Feature("abstract_words", "doc", "abstract length in tokens (missing when the document has no abstract)", None, floor=15.0),
]
FEATURE_BY_NAME = {f.name: f for f in FEATURES}


def _cv(xs: Sequence[float]) -> Optional[float]:
    if len(xs) < 2:
        return None
    m = statistics.mean(xs)
    return statistics.pstdev(xs) / m if m else None


def compute_features(doc: Document) -> Dict[str, Optional[float]]:
    sents = doc.sentences
    words = max(doc.alpha_words, 1)
    lens = [s.n for s in sents]
    out: Dict[str, Optional[float]] = {}
    out["sent_len_mean"] = statistics.mean(lens) if lens else None
    out["sent_len_sd"] = statistics.pstdev(lens) if len(lens) > 1 else None
    out["sent_len_cv"] = _cv(lens)
    out["short_sent_share"] = sum(1 for x in lens if x < 10) / len(lens) if lens else None
    out["long_sent_share"] = sum(1 for x in lens if x > 30) / len(lens) if lens else None
    plens = [sum(s.n for s in p.sentences) for p in doc.paragraphs if p.kind == "para" and p.sentences and not p.items]
    out["para_len_mean"] = statistics.mean(plens) if plens else None
    out["para_len_cv"] = _cv(plens)
    same = tot = 0
    prev = None
    for p in doc.paragraphs:
        if p.kind == "heading":
            prev = None
            continue
        for s in p.sentences:
            if prev is not None and s.first and prev.first:
                tot += 1
                same += s.first == prev.first
            prev = s
    out["same_opener_share"] = same / tot if tot else None
    long_paras = [p for p in doc.paragraphs if p.kind == "para" and len(p.sentences) >= 3]
    out["para_summary_end_share"] = (sum(1 for p in long_paras if RX["summary_open"].match(p.sentences[-1].text))
                                     / len(long_paras)) if long_paras else None
    out["list_item_rate"] = 1000.0 * doc.list_items / words
    out["heading_rate"] = 1000.0 * doc.headings / words
    out["abstract_words"] = float(doc.abstract_words) if doc.abstract_words else None
    alpha = [w for s in sents for w in s.alpha]
    out["word_len_mean"] = statistics.mean(len(w) for w in alpha) if alpha else None
    for f in FEATURES:
        if f.kind == "rate":
            out[f.name] = 1000.0 * sum(f.fn(s) for s in sents) / words
        elif f.kind == "share":
            out[f.name] = sum(1 for s in sents if f.fn(s)) / len(sents) if sents else None
    return {f.name: out.get(f.name) for f in FEATURES}


# --------------------------------------------------------------------------
# specimen selection
# --------------------------------------------------------------------------

def _uniform_window(sents: List[Sentence], w: int = 5) -> List[Sentence]:
    best, best_sd = [], None
    for k in range(0, max(0, len(sents) - w + 1)):
        win = sents[k:k + w]
        if len({s.para for s in win}) > 2:
            continue
        sd = statistics.pstdev([s.n for s in win])
        if best_sd is None or sd < best_sd:
            best, best_sd = win, sd
    return best


def contributing_sentences(doc: Document, name: str, direction: int, limit: int = 5) -> List[Sentence]:
    """Sentences of `doc` that push feature `name` in `direction` (+1 above corpus, -1 below)."""
    f = FEATURE_BY_NAME[name]
    sents = doc.sentences
    if f.kind in ("rate", "share") and direction > 0:
        scored = [(f.fn(s), s) for s in sents]
        scored = [(c, s) for c, s in scored if c]
        scored.sort(key=lambda cs: (-cs[0], cs[1].index))
        return [s for _, s in scored[:limit]]
    if name == "para_summary_end_share" and direction > 0:
        return [p.sentences[-1] for p in doc.paragraphs if p.kind == "para" and len(p.sentences) >= 3
                and RX["summary_open"].match(p.sentences[-1].text)][:limit]
    if name == "same_opener_share" and direction > 0:
        res = []
        for a, b in zip(sents, sents[1:]):
            if a.first and a.first == b.first and a.para == b.para:
                res.append(b)
        return res[:limit]
    if name in ("sent_len_mean", "long_sent_share") :
        key = (lambda s: -s.n) if direction > 0 else (lambda s: s.n)
        return sorted(sents, key=key)[:limit]
    if name == "short_sent_share":
        key = (lambda s: s.n) if direction > 0 else (lambda s: -s.n)
        return sorted(sents, key=key)[:limit]
    if name in ("sent_len_sd", "sent_len_cv"):
        if direction < 0:
            return _uniform_window(sents, min(limit, 5))
        return sorted(sents, key=lambda s: -abs(s.n - (statistics.mean([x.n for x in sents]) if sents else 0)))[:limit]
    if name in ("para_len_cv", "para_len_mean"):
        paras = [p for p in doc.paragraphs if p.kind == "para" and p.sentences]
        if name == "para_len_mean":
            key = (lambda p: sum(s.n for s in p.sentences)) if direction < 0 else (lambda p: -sum(s.n for s in p.sentences))
            return [p.sentences[0] for p in sorted(paras, key=key)[:limit]]
        firsts = [p.sentences[0] for p in paras]
        return firsts[:limit]
    if name == "word_len_mean":
        def mwl(s):
            return statistics.mean(len(w) for w in s.alpha) if s.alpha else 0
        pool = [s for s in sents if len(s.alpha) >= 8]
        return sorted(pool, key=lambda s: -mwl(s) if direction > 0 else mwl(s))[:limit]
    if name == "list_item_rate" and direction > 0:
        return [p.sentences[0] for p in doc.paragraphs if p.items and p.sentences][:limit]
    if name == "abstract_words":
        return [s for p in doc.paragraphs if p.abstract for s in p.sentences][:limit]
    return []


_SPECIAL_SPECIMENS = {
    "section_opening": "first sentence after a heading",
    "paragraph_opening": "first sentence of a paragraph",
    "paragraph_ending": "last sentence of a paragraph with >= 3 sentences",
    "result_announcement": "sentences announcing a result ('we prove', 'our main result', 'in this paper we')",
    "short_sentence": "sentences under 10 tokens",
    "long_sentence": "sentences over 30 tokens (truncated)",
}


def human_specimens(doc: Document, feature: str) -> List[Sentence]:
    paras = [p for p in doc.paragraphs if p.kind == "para" and p.sentences]
    if feature == "section_opening":
        return [p.sentences[0] for p in paras if p.after_heading]
    if feature == "paragraph_opening":
        return [p.sentences[0] for p in paras]
    if feature == "paragraph_ending":
        return [p.sentences[-1] for p in paras if len(p.sentences) >= 3]
    if feature == "result_announcement":
        return [s for s in doc.sentences if RX["result_announce"].search(s.text)]
    if feature in ("short_sentence", "short_sent_share"):
        return [s for s in doc.sentences if s.n < 10]
    if feature in ("long_sentence", "long_sent_share"):
        return [s for s in doc.sentences if s.n > 30]
    if feature == "para_summary_end_share":
        return [p.sentences[-1] for p in paras if len(p.sentences) >= 3 and RX["summary_open"].match(p.sentences[-1].text)]
    if feature == "same_opener_share":
        return [b for a, b in zip(doc.sentences, doc.sentences[1:]) if a.first and a.first == b.first]
    f = FEATURE_BY_NAME.get(feature)
    if f is None:
        raise ValueError("unknown feature %r; see `register features --list`" % feature)
    if f.fn is not None:
        return [s for s in doc.sentences if f.fn(s)]
    if f.name in ("sent_len_mean", "sent_len_sd", "sent_len_cv", "para_len_cv", "para_len_mean"):
        return [p.sentences[0] for p in paras if len(p.sentences) >= 3]
    return []


# ==========================================================================
# Corpus profile and comparison
# ==========================================================================

def expand_paths(paths: Sequence[str]) -> List[str]:
    files: List[str] = []
    for p in paths:
        if os.path.isdir(p):
            ex = os.path.join(p, "extracted.md")
            if os.path.isfile(ex):
                files.append(ex)
                continue
            for root, _, names in sorted(os.walk(p)):
                for nm in sorted(names):
                    if nm.endswith((".tex", ".md", ".txt")):
                        files.append(os.path.join(root, nm))
        elif os.path.isfile(p):
            files.append(p)
        else:
            print("warning: no such path %s" % p, file=sys.stderr)
    return files


def _quartiles(xs: List[float]) -> Tuple[float, float, float]:
    xs = sorted(xs)
    if len(xs) == 1:
        return xs[0], xs[0], xs[0]
    q = statistics.quantiles(xs, n=4, method="inclusive")
    return q[0], statistics.median(xs), q[2]


def _stats(values: List[float]) -> Dict[str, float]:
    q1, med, q3 = _quartiles(values)
    return {"median": med, "q1": q1, "q3": q3, "iqr": q3 - q1, "n": len(values),
            "min": min(values), "max": max(values)}


def _label(path: str) -> str:
    base = os.path.basename(path)
    if base in ("extracted.md", "index.md"):
        return os.path.basename(os.path.dirname(path))
    return base


def build_profile(paths: Sequence[str], min_words: int = 800, loo: bool = True, name: str = "") -> Dict:
    docs = []
    for fp in expand_paths(paths):
        d = load_document(fp)
        if d.alpha_words < min_words:
            print("skip (only %d prose words): %s" % (d.alpha_words, fp), file=sys.stderr)
            continue
        docs.append((fp, d, compute_features(d)))
    if not docs:
        raise ValueError("no corpus documents with >= %d prose words" % min_words)
    feats: Dict[str, Dict] = {}
    for f in FEATURES:
        vals = [fv[f.name] for _, _, fv in docs if fv[f.name] is not None]
        if not vals:
            continue
        st = _stats(vals)
        st["scale"] = max(st["iqr"], f.floor)
        st["floor"] = f.floor
        st["values"] = {_label(fp): fv[f.name] for fp, _, fv in docs if fv[f.name] is not None}
        st["desc"] = f.desc
        st["exploratory"] = f.exploratory
        if loo and len(vals) >= 5:
            out = 0
            for fp, _, fv in docs:
                if fv[f.name] is None:
                    continue
                rest = [v[f.name] for p2, _, v in docs if p2 != fp and v[f.name] is not None]
                q1, med, q3 = _quartiles(rest)
                d = (fv[f.name] - med) / max(q3 - q1, f.floor)
                out += abs(d) > 1.5
            st["loo_outside_rate"] = out / len(vals)
        feats[f.name] = st
    return {
        "version": VERSION,
        "name": name,
        "documents": [{"path": fp, "label": _label(fp), "prose_words": d.alpha_words,
                       "sentences": len(d.sentences), "format": d.fmt} for fp, d, _ in docs],
        "features": feats,
    }


def distances(values: Dict[str, Optional[float]], profile: Dict) -> Dict[str, Dict]:
    res = {}
    for f in FEATURES:
        st = profile["features"].get(f.name)
        v = values.get(f.name)
        if st is None or v is None:
            continue
        d = (v - st["median"]) / st["scale"] if st["scale"] else 0.0
        cv = list(st.get("values", {}).values())
        pct = ((sum(1 for x in cv if x < v) + 0.5 * sum(1 for x in cv if x == v)) / len(cv)) if cv else None
        res[f.name] = {"value": v, "median": st["median"], "q1": st["q1"], "q3": st["q3"],
                       "min": st["min"], "max": st["max"], "percentile": pct,
                       "beyond_corpus": v < st["min"] or v > st["max"],
                       "scale": st["scale"], "iqr_floored": st["scale"] > st["iqr"], "d": d}
    return res


def _fmt(v: Optional[float]) -> str:
    if v is None:
        return "-"
    a = abs(v)
    if a >= 100:
        return "%.0f" % v
    if a >= 10:
        return "%.1f" % v
    return "%.2f" % v if a >= 0.1 or a == 0 else "%.3f" % v


def _wrap_specimen(s: Sentence, max_words: int = 30) -> str:
    words = s.text.split()
    t = " ".join(words[:max_words]) + (" ..." if len(words) > max_words else "")
    return t


def compare_one(path: str, profile: Dict, baseline: Optional[str], threshold: float, worst: int,
                n_spec: int) -> Dict:
    doc = load_document(path)
    vals = compute_features(doc)
    dist = distances(vals, profile)
    base = None
    if baseline:
        bdoc = load_document(baseline)
        base = distances(compute_features(bdoc), profile)
        for k, row in dist.items():
            b = base.get(k)
            if b:
                row["baseline_value"] = b["value"]
                row["baseline_d"] = b["d"]
                row["moved_toward"] = abs(row["d"]) < abs(b["d"])
    for row in dist.values():
        row["outside"] = abs(row["d"]) > threshold
    ranked = sorted(dist, key=lambda k: -abs(dist[k]["d"]))
    specs = {}
    for k in ranked[:worst]:
        direction = 1 if dist[k]["d"] > 0 else -1
        ss = contributing_sentences(doc, k, direction, n_spec)
        specs[k] = [{"line": s.line, "text": _wrap_specimen(s, 45)} for s in ss]
    return {"manuscript": path, "prose_words": doc.alpha_words, "sentences": len(doc.sentences),
            "catalogue_sentences_excluded": doc.catalogue,
            "baseline": baseline, "threshold": threshold, "features": dist, "ranked": ranked,
            "specimens": specs,
            "summary": {"outside": sum(1 for r in dist.values() if r["outside"]),
                        "mean_abs_d": statistics.mean([abs(r["d"]) for r in dist.values()]) if dist else 0.0}}


def print_compare(res: Dict, profile: Dict) -> None:
    print("manuscript: %s  (%d prose words, %d sentences; %d catalogue sentences excluded)"
          % (res["manuscript"], res["prose_words"], res["sentences"], res.get("catalogue_sentences_excluded", 0)))
    print("corpus: %s  (n=%d documents)" % (profile.get("name") or "profile", len(profile["documents"])))
    if res["baseline"]:
        print("baseline: %s" % res["baseline"])
    print()
    hdr = "%-24s %9s %22s %7s" % ("feature", "ours", "corpus median [IQR]", "d")
    if res["baseline"]:
        hdr += " %9s %7s %s" % ("before", "d_before", "moved")
    print(hdr)
    print("-" * len(hdr))
    for k in res["ranked"]:
        r = res["features"][k]
        rng = "%s [%s, %s]%s" % (_fmt(r["median"]), _fmt(r["q1"]), _fmt(r["q3"]), "*" if r["iqr_floored"] else "")
        line = "%-24s %9s %22s %+7.2f" % (k, _fmt(r["value"]), rng, r["d"])
        if res["baseline"] and "baseline_d" in r:
            line += " %9s %+7.2f %s" % (_fmt(r["baseline_value"]), r["baseline_d"],
                                         "toward" if r["moved_toward"] else ("same" if abs(r["d"]) == abs(r["baseline_d"]) else "away"))
        if r["outside"]:
            line += "   << outside the literature range"
        if r.get("rules"):
            line += "  [%s]" % ", ".join(r["rules"])
        print(line)
    print("\n* scale floored (corpus IQR smaller than the feature floor)")
    s = res["summary"]
    print("outside the literature range: %d features; mean |d| = %.2f" % (s["outside"], s["mean_abs_d"]))
    for k, spec in res["specimens"].items():
        d = res["features"][k]["d"]
        print("\n== %s (d=%+.2f, %s the corpus): specimens from the manuscript" % (k, d, "above" if d > 0 else "below"))
        if not spec:
            print("   (no single sentence carries this; the feature is under-used or distributional."
                  " Run `specimens --feature %s` on the corpus for human examples.)" % k)
        for sp in spec:
            print("   L%-5d %s" % (sp["line"], sp["text"]))


def matrix_rows(results: List[Dict], profile: Dict, threshold: float) -> List[Dict]:
    """Per-feature consistency of the distances across several manuscripts."""
    rows = []
    for f in FEATURES:
        rs = [r["features"].get(f.name) for r in results]
        present = [x for x in rs if x is not None]
        if not present:
            continue
        ds = [x["d"] for x in present]
        med = statistics.median(ds)
        sign = 1 if med >= 0 else -1
        st = profile["features"][f.name]
        rows.append({
            "feature": f.name,
            "exploratory": f.exploratory,
            "d": [None if x is None else x["d"] for x in rs],
            "median_d": med,
            "n": len(present),
            "outside_same_side": sum(1 for d in ds if abs(d) > threshold and d * sign > 0),
            "beyond_iqr_same_side": sum(1 for x in present
                                        if (x["value"] > st["q3"] if sign > 0 else x["value"] < st["q1"])),
            "beyond_range_same_side": sum(1 for x in present
                                          if (x["value"] > st["max"] if sign > 0 else x["value"] < st["min"])),
            "median_percentile": statistics.median([x["percentile"] for x in present if x.get("percentile") is not None])
            if any(x.get("percentile") is not None for x in present) else None,
            "median_value": statistics.median([x["value"] for x in present]),
            "corpus_median": st["median"], "corpus_q1": st["q1"], "corpus_q3": st["q3"],
            "iqr_floored": st["scale"] > st["iqr"],
            "corpus_n": st["n"],
            "loo_outside_rate": st.get("loo_outside_rate"),
        })
    rows.sort(key=lambda r: (-r["beyond_iqr_same_side"], -abs(r["median_d"])))
    return rows


def print_matrix(results: List[Dict], profile: Dict, threshold: float) -> None:
    labels = [_label(r["manuscript"]) for r in results]
    short = [os.path.splitext(l)[0][:10] for l in labels]
    print("distance d (IQR units) per manuscript; corpus n=%d" % len(profile["documents"]))
    print("columns: median d | #|d|>%.1f same side | #beyond corpus IQR same side | #beyond corpus min/max |"
          " median percentile | leave-one-out |d|>1.5 rate among corpus docs" % threshold)
    hdr = "%-23s" % "feature" + "".join(" %10s" % s for s in short) + " %7s %5s %5s %5s %5s %5s" % (
        "med d", ">thr", ">IQR", ">rng", "pct", "loo")
    print(hdr)
    print("-" * len(hdr))
    for r in matrix_rows(results, profile, threshold):
        n = r["n"]
        print("%-23s" % (r["feature"] + ("*" if r["iqr_floored"] else "")) +
              "".join(" %10s" % ("-" if d is None else "%+.2f" % d) for d in r["d"]) +
              " %+7.2f %5s %5s %5s %5s %5s" % (
                  r["median_d"], "%d/%d" % (r["outside_same_side"], n), "%d/%d" % (r["beyond_iqr_same_side"], n),
                  "%d/%d" % (r["beyond_range_same_side"], n),
                  "-" if r["median_percentile"] is None else "%.2f" % r["median_percentile"],
                  "-" if r["loo_outside_rate"] is None else "%.2f" % r["loo_outside_rate"]))
    print("* scale floored: the corpus IQR is below the feature floor, so d is measured against the floor")


# ==========================================================================
# CLI


# ==========================================================================
# Text renderings (the JSON results stay authoritative)
# ==========================================================================

def _captured(fn, *args) -> str:
    import contextlib
    import io
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        fn(*args)
    return buf.getvalue().rstrip("\n")


def render_compare(results: List[Dict], profile: Dict) -> str:
    return ("\n\n" + "=" * 78 + "\n\n").join(_captured(print_compare, r, profile) for r in results)


def render_matrix(results: List[Dict], profile: Dict, threshold: float) -> str:
    return _captured(print_matrix, results, profile, threshold)


def render_profile(profile: Dict) -> str:
    lines = ["profile: %s (%d documents)" % (profile.get("name") or "unnamed", len(profile["documents"])),
             "%-24s %9s %9s %9s %5s %6s" % ("feature", "q1", "median", "q3", "n", "loo")]
    for k, st in profile["features"].items():
        lines.append("%-24s %9s %9s %9s %5d %6s" % (
            k, _fmt(st["q1"]), _fmt(st["median"]), _fmt(st["q3"]), st["n"],
            "-" if "loo_outside_rate" not in st else "%.2f" % st["loo_outside_rate"]))
    return "\n".join(lines)


def render_dump(path: str, show_all: bool = False) -> str:
    """Show exactly what prose the profiler reads, with source lines."""
    d = load_document(path)
    out = ["# %s: %d prose words, %d sentences, %d paragraphs, %d headings, abstract=%s, "
           "catalogue sentences excluded=%d"
           % (path, d.alpha_words, len(d.sentences), sum(1 for p in d.paragraphs if p.kind == "para"),
              d.headings, d.abstract_words, d.catalogue)]
    for p in d.paragraphs:
        if p.kind == "heading":
            out.append("\n## L%d %s" % (p.line, p.text))
            continue
        if not p.sentences:
            if show_all:
                out.append("   L%-5d [no prose] %s" % (p.line, p.text[:100]))
            continue
        out.append("")
        for s in p.sentences:
            out.append("   L%-5d %s%s" % (s.line, "[abs] " if p.abstract else "", s.text))
    return "\n".join(out)


def feature_list() -> List[Dict]:
    rows = [{"name": f.name, "kind": f.kind, "description": f.desc, "exploratory": f.exploratory}
            for f in FEATURES]
    rows += [{"name": k, "kind": "specimen_selector", "description": v, "exploratory": False}
             for k, v in _SPECIAL_SPECIMENS.items()]
    return rows


def features_of(paths: Sequence[str]) -> Dict[str, Dict]:
    rows = {}
    for fp in expand_paths(paths):
        d = load_document(fp)
        rows[fp] = {"prose_words": d.alpha_words, "sentences": len(d.sentences), "features": compute_features(d)}
    return rows


def collect_specimens(paths: Sequence[str], feature: str, limit: int = 12, max_words: int = 30,
                      grep: Optional[str] = None, seed: int = 0) -> Dict:
    """Example sentences from a human corpus, interleaved across documents."""
    if feature not in _SPECIAL_SPECIMENS and feature not in FEATURE_BY_NAME:
        raise ValueError("unknown feature %r; see `register features --list`" % feature)
    rng = random.Random(seed)
    pools = []
    for fp in expand_paths(paths):
        ss = human_specimens(load_document(fp), feature)
        if grep:
            rx = re.compile(grep, re.I)
            ss = [s for s in ss if rx.search(s.text)]
        ss = [s for s in ss if feature in ("long_sentence", "long_sent_share") or s.n <= max_words]
        rng.shuffle(ss)
        if ss:
            pools.append((fp, ss))
    shown: List[Dict] = []
    k = 0
    while len(shown) < limit and pools:
        for fp, ss in pools:
            if len(shown) >= limit:
                break
            if k < len(ss):
                shown.append({"source": _label(fp), "line": ss[k].line, "text": _wrap_specimen(ss[k], max_words)})
        pools = [(fp, ss) for fp, ss in pools if k + 1 < len(ss)]
        k += 1
    desc = _SPECIAL_SPECIMENS.get(feature) or FEATURE_BY_NAME[feature].desc
    return {"feature": feature, "description": desc,
            "note": "Imitate the move, never the text.", "specimens": shown}


# ==========================================================================
# Register rules
# ==========================================================================

STAGE_SCOPES = ("short", "expository", "long")
RULE_STATUSES = ("adopted", "candidate")
MAX_SPECIMEN_WORDS = 25
_PRIVATE_MARKERS = re.compile(r"/Users/|/home/|\\Users\\|annex/|ai_workflow|memory|scratchpad|custody", re.I)


def load_rules(path: Optional[str] = None) -> Dict:
    """The packaged general rule set, or a local copy of it."""
    if path is None:
        from importlib.resources import files
        raw = files("lean_exposition").joinpath("resources/register/rules.json").read_text(encoding="utf-8")
    else:
        with open(path, encoding="utf-8") as fh:
            raw = fh.read()
    return json.loads(raw)


def validate_rules(data: Dict) -> Dict:
    """Structural checks on a rule set; returns counts or raises ValueError."""
    problems: List[str] = []
    ids = set()
    for rule in data.get("rules", []):
        rid = rule.get("id", "?")
        if rid in ids:
            problems.append("%s: duplicate id" % rid)
        ids.add(rid)
        if rule.get("status") not in RULE_STATUSES:
            problems.append("%s: status must be one of %s" % (rid, RULE_STATUSES))
        scopes = rule.get("scopes") or []
        if not scopes or any(s not in STAGE_SCOPES for s in scopes):
            problems.append("%s: scopes must be a non-empty subset of %s" % (rid, STAGE_SCOPES))
        for key in ("rule", "limit", "provenance"):
            if not rule.get(key):
                problems.append("%s: missing %s" % (rid, key))
        text = json.dumps(rule, ensure_ascii=False)
        if "\u2014" in rule.get("rule", "") + rule.get("limit", ""):
            problems.append("%s: em dash in the rule text" % rid)
        for spec in rule.get("specimens", []):
            if len(spec.get("quote", "").split()) > MAX_SPECIMEN_WORDS:
                problems.append("%s: specimen over %d words" % (rid, MAX_SPECIMEN_WORDS))
            if not spec.get("source"):
                problems.append("%s: specimen without a source" % rid)
        if _PRIVATE_MARKERS.search(text):
            problems.append("%s: private path or reference" % rid)
        for name in (rule.get("detector") or {}).get("features", []):
            if name not in FEATURE_BY_NAME:
                problems.append("%s: unknown detector feature %s" % (rid, name))
    for row in data.get("history", []):
        if _PRIVATE_MARKERS.search(json.dumps(row, ensure_ascii=False)):
            problems.append("history %s: private path or reference" % row.get("id", "?"))
    if problems:
        raise ValueError("register rules: " + "; ".join(problems))
    rules = data.get("rules", [])
    return {"rules": len(rules),
            "by_status": {s: sum(1 for r in rules if r["status"] == s) for s in RULE_STATUSES},
            "by_scope": {s: sum(1 for r in rules if s in r["scopes"]) for s in STAGE_SCOPES},
            "history": len(data.get("history", []))}


def select_rules(data: Dict, scope: Optional[str] = None, status: Optional[str] = None) -> List[Dict]:
    if scope is not None and scope not in STAGE_SCOPES:
        raise ValueError("scope must be one of %s" % (STAGE_SCOPES,))
    return [r for r in data["rules"]
            if (scope is None or scope in r["scopes"]) and (status is None or r["status"] == status)]


def rules_by_feature(data: Dict) -> Dict[str, List[str]]:
    out: Dict[str, List[str]] = {}
    for r in data["rules"]:
        for name in (r.get("detector") or {}).get("features", []):
            out.setdefault(name, []).append(r["id"])
    return out


def render_rules(rules: List[Dict], title: str = "Register rules") -> str:
    """Markdown for writers and reviewers: rule, limit, detector and specimens."""
    lines = ["# " + title, "",
             "Each rule names a move from the literature, with short specimens to imitate and never to copy.",
             "A detector points at sentences to reread; it never passes or fails a paper.", ""]
    for r in rules:
        lines.append("## %s (%s; %s)" % (r["id"], r["status"], ", ".join(r["scopes"])))
        lines += ["", r["rule"], "", "*Limit.* " + r["limit"]]
        det = r.get("detector") or {}
        if det.get("features"):
            lines.append("*Detector.* " + ", ".join("`%s`" % f for f in det["features"]))
        if r.get("example"):
            lines += ["*Before.* " + r["example"]["before"], "*After.* " + r["example"]["after"]]
        for s in r.get("specimens", [])[:6]:
            lines.append('- "%s" (%s%s)' % (s["quote"], s["source"], ", " + s["locator"] if s.get("locator") else ""))
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def annotate_with_rules(result: Dict, data: Dict) -> Dict:
    """Attach the ids of rules whose detector names each measured feature."""
    index = rules_by_feature(data)
    for name, row in result["features"].items():
        if name in index:
            row["rules"] = index[name]
    return result


# ==========================================================================
# Review-packet inputs
# ==========================================================================

def build_packet_inputs(drafts: Dict[str, str], literature: Sequence[str], out: str, title: str,
                        job: str = "", min_words: int = 800, threshold: float = 1.5) -> Dict:
    """Write the register inputs every critique packet carries.

    ``drafts`` maps a stage (short, expository, long) to a manuscript path.
    Writes ``register/register_rules.json``, ``register/REGISTER_RULES.md``,
    ``register/profile.json``, ``register/measurement.json``,
    ``register/measurement.txt`` and ``request.md`` (from the packaged
    critique-request template) under ``out``; refuses to overwrite. A packet
    builder calls this once per round, after the drafts are frozen.
    """
    from importlib.resources import files
    for stage in drafts:
        if stage not in STAGE_SCOPES:
            raise ValueError("draft stage must be one of %s" % (STAGE_SCOPES,))
    names = ["register/register_rules.json", "register/REGISTER_RULES.md", "register/profile.json",
             "register/measurement.json", "register/measurement.txt", "request.md"]
    if any(os.path.exists(os.path.join(out, n)) for n in names):
        raise ValueError("packet register files already exist in %s" % out)
    os.makedirs(os.path.join(out, "register"), exist_ok=True)
    data = load_rules()
    validate_rules(data)
    profile = build_profile(literature, min_words=min_words, name="cited literature")
    results = []
    for stage, path in drafts.items():
        res = annotate_with_rules(compare_one(path, profile, None, threshold, 5, 5), data)
        res["stage"] = stage
        res["manuscript"] = os.path.basename(path)  # packets never carry local paths
        results.append(res)
    for row in profile["documents"]:
        row["path"] = row["label"]
    text = render_compare(results, profile)
    if len(results) > 1:
        text += "\n\n" + render_matrix(results, profile, threshold)
    relevant = [r for r in data["rules"] if any(s in r["scopes"] for s in drafts)]
    template = files("lean_exposition").joinpath("resources/templates/critique-request.md").read_text(encoding="utf-8")
    documents = "\n".join("- %s: `%s`" % (stage, os.path.basename(path)) for stage, path in drafts.items())
    request = (template.replace("{title}", title).replace("{documents}", documents)
               .replace("{job}", job or "No additional assignment for this packet."))

    def write(name: str, content: str) -> None:
        with open(os.path.join(out, name), "w", encoding="utf-8") as fh:
            fh.write(content)

    write("register/register_rules.json", json.dumps(data, indent=1, ensure_ascii=False) + "\n")
    write("register/REGISTER_RULES.md", render_rules(relevant, "Register rules for these drafts"))
    write("register/profile.json", json.dumps(profile, indent=1, ensure_ascii=False) + "\n")
    write("register/measurement.json", json.dumps(results, indent=1, ensure_ascii=False) + "\n")
    write("register/measurement.txt", text + "\n")
    write("request.md", request)
    return {"out": out, "files": names, "corpus_documents": len(profile["documents"]),
            "drafts": {r["stage"]: {"outside": r["summary"]["outside"], "mean_abs_d": r["summary"]["mean_abs_d"]}
                       for r in results}}
