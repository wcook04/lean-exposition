#!/usr/bin/env python3
"""Transcribe the three pinned Erdős #257 papers into the reader's Markdown dialect.

Usage: convert.py SOURCE_EXPORT_ROOT AUX_DIR OUTPUT_DIR

SOURCE_EXPORT_ROOT is a read-only export of wcook04/plectis-erdos at COMMIT, AUX_DIR holds
the .aux files of a Tectonic compile of exactly those sources, and OUTPUT_DIR is
papers/erdos257. The script uses the standard library only and is deterministic: it reads
no clock, no environment and no network, and running it twice gives identical bytes.

The words come from the pinned full-text Markdown (docs/papers/full-text/*.md). Only the
rules listed in ../README.md change it; everything else is copied. Printed numbers come from
the .aux files, bibliography labels from the TeX thebibliography and \\bibcite, and the front
matter from the TeX \\title, \\subtitle, \\author, \\date and provenance note.
"""

import hashlib
import json
import re
import shutil
import sys
import unicodedata
import urllib.parse
from pathlib import Path

COMMIT = "a5e7700e30374e3aaeeeff0284ec2ec0d2322fc3"
REPO = "wcook04/plectis-erdos"
BLOB = f"https://github.com/{REPO}/blob/{COMMIT}/"
PAGES = "https://wcook04.github.io/practical-formal-verification/papers/"

PAPERS = [
    {"level": "short", "stem": "erdos-257-mersenne-support-subseries", "out": "short/paper.md",
     "pdf": "short/paper.pdf", "parts": {1: "section", 2: "subsection", 3: "subsubsection", 4: "paragraph"},
     "abstract": True, "split_long_sections": False,
     "tex_extra": ["paper/problem-note-preamble.tex", "paper/paper-house-style.sty", "paper/paper-evidence.tex"]},
    {"level": "expository", "stem": "erdos257-expository-sums-never-fractions", "out": "expository/main.md",
     "pdf": "expository/main.pdf", "parts": {1: "section", 2: "subsection", 3: "subsubsection", 4: "paragraph"},
     "abstract": False, "split_long_sections": False,
     "tex_extra": ["paper/paper-house-style.sty", "paper/257/figures/cycle-mean.tex"]},
    {"level": "long", "stem": "erdos257-mersenne-reasoning-surface", "out": "long/reasoning-record.md",
     "pdf": "long/reasoning-record.pdf",
     "parts": {1: "part", 3: "section", 4: "subsection", 5: "subsubsection", 6: "paragraph"},
     "abstract": True, "split_long_sections": True,
     "tex_extra": ["paper/paper-house-style.sty", "paper/paper-evidence.tex",
                   "paper/reasoning-parts/erdos257/preamble.tex"]},
]
OUT_LEVEL = {"part": 2, "section": 2, "subsection": 3, "subsubsection": 4, "paragraph": 5}
OUT_LEVEL_LONG = {"part": 2, "section": 3, "subsection": 4, "subsubsection": 5, "paragraph": 6}
THEOREM_CLASSES = {"theorem", "problem", "corollary", "proposition", "lemma", "thm", "lem", "prop", "cor",
                   "defn", "rem", "obs", "readercheck", "exercise"}
LONG_SECTION_LINES = 300
PDF_BY_STEM = {p["stem"]: p for p in PAPERS}


# ----------------------------------------------------------------------------- TeX helpers

def brace_group(s, i):
    """Return (body, end) for the balanced {...} group starting at s[i] (skipping spaces)."""
    while s[i] in " \t\n":
        i += 1
    if s[i] != "{":
        raise ValueError(f"expected '{{' at {i}: {s[i:i + 40]!r}")
    depth = 0
    j = i
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    raise ValueError("unbalanced group")


def groups(s, i, n):
    out = []
    for _ in range(n):
        body, i = brace_group(s, i)
        out.append(body)
    return out, i


def strip_outer_braces(s):
    while len(s) >= 2 and s[0] == "{" and s[-1] == "}":
        try:
            body, end = brace_group(s, 0)
        except ValueError:
            break
        if end != len(s):
            break
        s = body
    return s


def parse_aux(text):
    labels, toc, bib = {}, [], []
    for m in re.finditer(r"\\newlabel\{", text):
        (label, body), _ = groups(text, m.end() - 1, 2)
        if label.endswith("@cref") or label.startswith("sub@"):
            continue
        (num, page, title, target, _extra), _ = groups(body, 0, 5)
        labels[label] = {"printed": strip_outer_braces(num), "page": page, "title": title, "target": target}
    for m in re.finditer(r"\\@writefile\{toc\}\{\\contentsline \{", text):
        (kind, title, page, target), _ = groups(text, m.end() - 1, 4)
        num = None
        nm = re.match(r"\\numberline \{([^}]*)\}", title)
        if nm:
            num, title = nm.group(1), title[nm.end():]
        toc.append({"kind": kind, "number": num, "title": title, "page": page, "target": target})
    for m in re.finditer(r"\\bibcite\{([^}]*)\}\{([^}]*)\}", text):
        bib.append((m.group(1), m.group(2)))
    return labels, toc, bib


ACCENTS = {"H": "\u030b", '"': "\u0308", "v": "\u030c", "'": "\u0301", "`": "\u0300", "^": "\u0302",
           "~": "\u0303", "c": "\u0327", "u": "\u0306", "=": "\u0304", ".": "\u0307", "k": "\u0328"}


def tex_accents(s):
    def rep(m):
        cmd, letter = m.group(1), m.group(2) or m.group(3)
        return unicodedata.normalize("NFC", letter + ACCENTS[cmd])
    s = re.sub(r"\\([Hv\"'`^~cuk=.])\s*(?:\{(\w)\}|(\w))", rep, s)
    return re.sub(r"\\l(?:\{\}|\s+|(?![A-Za-z]))", "ł", s)


def norm_title(s):
    """Comparable letters of a TeX or Markdown title."""
    s = tex_accents(s)
    s = unicodedata.normalize("NFKD", s)
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = re.sub(r"\\[A-Za-z]+", "", s)
    return re.sub(r"[^a-z0-9]", "", s.lower())


def tex_text_to_md(s):
    """The few TeX constructs used in front-matter strings, to Markdown. Math stays TeX."""
    out = []
    pieces = re.split(r"(\$[^$]*\$)", s)
    for k, piece in enumerate(pieces):
        if k % 2 == 1:
            out.append(piece)
            continue
        t = tex_accents(piece)
        t = re.sub(r"\\emph\{([^{}]*)\}", r"*\1*", t)
        t = t.replace("\\\\", "\x01").replace("~", " ").replace("\\#", "#")
        t = re.sub(r"\s+", " ", t).replace("\x01", "\\\n")
        out.append(t)
    text = "".join(out)
    text = re.sub(r"[ \t]+", " ", text).strip()
    if re.search(r"\\[A-Za-z]", re.sub(r"\$[^$]*\$", "", text)):
        raise ValueError(f"unconverted TeX in front matter: {text!r}")
    return text


# ----------------------------------------------------------------------------- the converter

NOTE_LINE = re.compile(r'^<a id="(paper-table-note-[0-9a-f]+)"></a> \*\*Detail note \d+\.\*\* (.*)$')
NOTE_LINK = re.compile(r'\[detail note \d+\]\(#(paper-table-note-[0-9a-f]+)\)')


def source_fixes(text):
    """Rule 8: undo two things the full text does that the PDF does not.

    The full text moves long table cells into "Detail note N." paragraphs after the table and
    links each cell to its note; the PDF prints the content in the cell. Each note's content goes
    back into its cell and the paragraph is dropped. And Pandoc's empty separator comment after
    an inline formula (`$`x`$<!-- -->1246`) becomes a space, because the reader does not close a
    formula that a digit follows.
    """
    lines = text.split("\n")
    notes, kept, k = {}, [], 0
    while k < len(lines):
        m = NOTE_LINE.match(lines[k])
        if not m:
            kept.append(lines[k])
            k += 1
            continue
        # A note is one paragraph, which may run over several lines: join them with spaces.
        body = [m.group(2).strip()]
        k += 1
        while k < len(lines) and lines[k].strip():
            body.append(lines[k].strip())
            k += 1
        notes[m.group(1)] = " ".join(body)
        while k < len(lines) and not lines[k].strip() and kept and not kept[-1].strip():
            k += 1
    out = [NOTE_LINK.sub(lambda m: notes[m.group(1)], line) for line in kept] if notes else kept
    return "\n".join(out).replace("`$<!-- -->", "`$ ")


class Converter:
    def __init__(self, paper, root, aux_dir, out_dir):
        self.p = paper
        self.root = root
        self.out_dir = out_dir
        self.src_path = root / "docs/papers/full-text" / (paper["stem"] + ".md")
        self.tex_path = root / "paper/257" / (paper["stem"] + ".tex")
        self.aux_path = aux_dir / (paper["stem"] + ".aux")
        self.source = source_fixes(self.src_path.read_text(encoding="utf-8"))
        self.tex = self.tex_path.read_text(encoding="utf-8")
        self.labels, self.toc, self.bibcite = parse_aux(self.aux_path.read_text(encoding="utf-8"))
        self.bibnum = dict(self.bibcite)
        self.toc_pos = 0
        self.section_number = None
        self.counters = {}
        self.eq_counter = 0
        self.evidence = {}
        self.blocks = []          # theorem-like blocks: label, kind, number, line
        self.headings = []        # output headings
        self.notes = []           # anything worth reporting
        self.links = []           # (kind, target)

    # ---------------------------------------------------------------- numbers

    def printed(self, label):
        entry = self.labels.get(label)
        return None if entry is None else entry["printed"]

    def toc_match(self, kind, title):
        want = norm_title(title)
        for k in range(self.toc_pos, min(self.toc_pos + 3, len(self.toc))):
            entry = self.toc[k]
            if norm_title(entry["title"]) == want:
                if entry["kind"] != kind:
                    raise ValueError(f"toc kind {entry['kind']} != {kind} for {title!r}")
                self.toc_pos = k + 1
                return entry
        return None

    # ---------------------------------------------------------------- math

    def expand_macros(self, tex):
        # \ensuremath{X} in math mode is X (the long record's \m shorthand, expanded by pandoc).
        while True:
            m = re.search(r"\\ensuremath\s*\{", tex)
            if not m:
                break
            body, end = brace_group(tex, m.end() - 1)
            before = tex[:m.start()]
            wrap = before.rstrip().endswith(("^", "_"))
            if wrap:
                body = "{" + body + "}"
            elif re.search(r"\\[A-Za-z]+$", before) and re.match(r"[A-Za-z]", body):
                body = " " + body        # keep a control word apart from the letter that follows
            tex = before + body + tex[end:]
        def ref(m):
            num = self.printed(m.group(1))
            if num is None:
                raise ValueError(f"\\ref to unknown label {m.group(1)}")
            return num
        return re.sub(r"\\ref\{([^}]*)\}", ref, tex)

    def display_math(self, body):
        tex = self.expand_macros(body)
        labels = re.findall(r"\\label\{([^}]*)\}", tex)
        tex = re.sub(r"[ \t]*\\label\{[^}]*\}", "", tex)
        tex = "\n".join(l for l in tex.split("\n") if l.strip())
        m = re.fullmatch(r"\s*\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}(.*)\\end\{\1\}\s*", tex, re.S)
        tags = re.findall(r"\\tag\{((?:[^{}]|\{[^{}]*\})*)\}", tex)
        if m is None:
            if labels:
                raise ValueError(f"label outside an environment: {labels}")
            return tex.strip("\n")
        env, inner = m.group(1), m.group(2)
        if env == "equation":
            if not tags:
                self.eq_counter += 1
                number = str(self.eq_counter)
                for label in labels:
                    if self.printed(label) != number:
                        raise ValueError(f"equation {label}: aux {self.printed(label)} != counted {number}")
                inner = inner.rstrip() + "\n\\tag{" + number + "}"
            else:
                for label in labels:
                    if self.printed(label) != tags[0]:
                        raise ValueError(f"equation {label}: aux {self.printed(label)} != tag {tags[0]}")
            return inner.strip("\n")
        if env == "equation*":
            for label in labels:
                if tags and self.printed(label) != tags[0]:
                    raise ValueError(f"equation* {label}: aux {self.printed(label)} != tag {tags[0]}")
            return inner.strip("\n")
        if env in ("align*", "gather*", "multline*", "multline"):
            new = {"align*": "aligned", "gather*": "gathered", "multline*": "gathered", "multline": "gathered"}[env]
            if env == "multline":
                self.eq_counter += 1
                return f"\\begin{{{new}}}{inner}\\end{{{new}}}\n\\tag{{{self.eq_counter}}}"
            return f"\\begin{{{new}}}{inner}\\end{{{new}}}"
        # Numbered align/gather: KaTeX accepts them with a \tag on each row.
        rows = re.split(r"(\\\\)", inner)
        out = []
        for k in range(0, len(rows), 2):
            row = rows[k]
            sep = rows[k + 1] if k + 1 < len(rows) else ""
            if row.strip() and not re.search(r"\\(tag|notag|nonumber)\b", row):
                self.eq_counter += 1
                row = row.rstrip() + f"\\tag{{{self.eq_counter}}}\n"
            out.append(row + sep)
        if labels:
            self.notes.append(f"labels in numbered {env} not checked individually: {labels}")
        return f"\\begin{{{env}}}{''.join(out)}\\end{{{env}}}".strip("\n")

    # ---------------------------------------------------------------- inline text

    def link_target(self, url):
        """Rewrite a link destination. Returns the new destination."""
        if url.startswith("#"):
            frag = urllib.parse.unquote(url[1:])
            self.links.append(("fragment", frag))
            return "#" + frag
        if re.match(r"[a-z]+:", url):
            return url
        path, _, frag = url.partition("#")
        repo_path = Path("docs/papers/full-text") / path
        parts = []
        for seg in repo_path.parts:
            if seg == "..":
                parts.pop()
            else:
                parts.append(seg)
        rel = "/".join(parts)
        stem = Path(rel).stem
        if rel.startswith("paper/257/") and rel.endswith(".pdf") and stem in PDF_BY_STEM:
            target = PDF_BY_STEM[stem]
            if frag.startswith("nameddest="):
                anchor = urllib.parse.unquote(frag[len("nameddest="):])
                if target["level"] == self.p["level"]:
                    self.links.append(("fragment", anchor))
                    return "#" + anchor
                href = f"../{target['out']}#{anchor}"
                self.links.append(("companion", target["level"], anchor))
                return href
            return PAGES + Path(rel).name + (f"#{frag}" if frag else "")
        if not (self.root / rel).exists():
            self.notes.append(f"relative link to {rel}, absent from the export, linked at the pinned commit")
        return BLOB + rel + (f"#{frag}" if frag else "")

    def cite(self, m):
        content = m.group(1)
        segments = [s.strip() for s in content.split(";")]
        rendered = []
        for seg in segments:
            key, _, note = seg.partition(",")
            key = key.strip()
            if key not in self.bibnum:
                return m.group(0)
            item = f"[{self.bibnum[key]}](#ref-{key})"
            if note.strip():
                item += "," + note
            rendered.append(item)
        return "\\[" + ", ".join(rendered) + "\\]"

    def inline(self, line):
        maths = []

        def keep(m):
            maths.append("$" + self.expand_macros(m.group(1)) + "$")
            return f"\x00{len(maths) - 1}\x00"
        text = re.sub(r"\$`(.*?)`\$", keep, line, flags=re.S)
        if "$`" in text:
            raise ValueError(f"unclosed inline math: {line[:80]!r}")

        # Equation references [\[eq:x\]](#eq%3Ax) -> [(n)](#eq:x)
        def eqref(m):
            label = m.group(1)
            target = urllib.parse.unquote(m.group(2))
            num = self.printed(label)
            if num is None or target != label:
                raise ValueError(f"equation reference {label} -> {target}: no printed number")
            self.links.append(("fragment", target))
            return f"[({num})](#{target})"
        text = re.sub(r"\[\\\[([A-Za-z]+:[^\]\\]+)\\\]\]\(#([^)\s]+)\)", eqref, text)

        # Numbered references [2](#res%3Ax) -> printed number from the aux.
        def numref(m):
            shown, target = m.group(1), urllib.parse.unquote(m.group(2))
            num = self.printed(target)
            if num is None:
                self.notes.append(f"number-like link text {shown!r} to non-label anchor #{target} kept")
                return m.group(0)
            return f"[{num}](#{target})"
        text = re.sub(r"\[([0-9]+(?:\.[0-9]+)*)\]\(#([^)\s]+)\)", numref, text)

        # Link destinations: unescape fragments, map companion and repository links.
        def dest(m):
            return "](" + self.link_target(m.group(1)) + ")"
        text = re.sub(r"\]\(([^)\s]+)\)", dest, text)

        # Citations \[key, note\] -> \[[n](#ref-key), note\]
        text = re.sub(r"\\\[([a-z][a-z0-9]*(?:[,;][^\]]*?)?)\\\]", self.cite, text)
        leftover = re.findall(r"\\\[([a-z][a-z0-9]*)[,;\\]", text)
        if any(k in self.bibnum for k in leftover):
            raise ValueError(f"unconverted citation in {line[:80]!r}")

        return re.sub(r"\x00(\d+)\x00", lambda m: maths[int(m.group(1))], text)

    # ---------------------------------------------------------------- blocks

    def theorem_head(self, line, label, cls):
        m = re.match(r"^(\*\*|\*)([A-Z][a-z]+) (\d+)\1(.*)$", line, re.S)
        if not m:
            raise ValueError(f"theorem-like block without a head: {line[:80]!r}")
        kind, rest = m.group(2), m.group(4)
        title = ""
        if rest.startswith(" ("):
            depth, j = 0, 1
            while j < len(rest):
                if rest.startswith("$`", j):
                    j = rest.index("`$", j + 2) + 2
                    continue
                if rest[j] == "(":
                    depth += 1
                elif rest[j] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            title, rest = rest[:j + 1], rest[j + 1:]
        if not rest.startswith("."):
            raise ValueError(f"theorem head without a period: {line[:80]!r}")
        rest = rest[1:]
        if self.p["level"] == "expository":
            self.counters[cls] = self.counters.get(cls, 0) + 1
            number = str(self.counters[cls])
        else:
            if self.section_number is None:
                raise ValueError(f"theorem before a numbered section: {line[:60]!r}")
            self.counters["thm"] = self.counters.get("thm", 0) + 1
            number = f"{self.section_number}.{self.counters['thm']}"
        if label is not None:
            aux = self.printed(label)
            if aux != number:
                raise ValueError(f"{label}: aux {aux} != counted {number}")
        self.blocks.append({"label": label, "kind": kind, "class": cls, "number": number})
        return f"**{kind} {number}{title}.**{rest}"

    def heading(self, level, title, anchor):
        kind = self.p["parts"].get(level)
        if kind is None:
            raise ValueError(f"unexpected heading level {level}: {title!r}")
        entry = self.toc_match(kind, title)
        number = entry["number"] if entry else None
        if kind == "section" and number is not None:
            self.section_number = number
            self.counters["thm"] = 0
        if anchor and anchor in self.labels and number is not None and self.labels[anchor]["printed"] != number:
            raise ValueError(f"heading {anchor}: aux {self.labels[anchor]['printed']} != toc {number}")
        out_level = (OUT_LEVEL_LONG if self.p["level"] == "long" else OUT_LEVEL)[kind]
        text = self.inline(title)
        if number is not None:
            text = (f"{number}. " if kind == "section" else f"{number} ") + text
        self.headings.append({"anchor": anchor, "kind": kind, "level": out_level, "number": number,
                              "title": text})
        return "#" * out_level + " " + text

    def bibliography(self, blob_lines):
        blob = "\n".join(blob_lines).strip()
        blob = re.sub(r"^9+\s+", "", blob)
        tex = self.tex[self.tex.index("\\begin{thebibliography}"):self.tex.index("\\end{thebibliography}")]
        items = list(re.finditer(r"\\bibitem\{([^}]*)\}", tex))
        keys = [m.group(1) for m in items]
        if keys != [k for k, _ in self.bibcite]:
            raise ValueError("bibitem order differs from \\bibcite order")
        starts = []
        pos = 0
        for k, m in enumerate(items):
            end = items[k + 1].start() if k + 1 < len(items) else len(tex)
            head = tex_accents(tex[m.end():end])
            head = re.sub(r"\\(?:emph|href\{[^}]*\}|textit|url)\s*", "", head)
            head = head.replace("~", " ").replace("\\#", "#")
            words = re.findall(r"[^\W\d_]+", head)[:5]
            pattern = r"(?<![^\s])" + r"[^\w]{0,6}".join(re.escape(w) for w in words)
            mm = re.compile(pattern).search(blob, pos)
            if mm is None:
                raise ValueError(f"bibliography entry {keys[k]} not found ({words})")
            # step back over markup opening the entry (e.g. "[*")
            start = mm.start()
            starts.append(start)
            pos = mm.end()
        if starts[0] != 0:
            raise ValueError("text before the first bibliography entry: " + blob[:starts[0]])
        out = []
        for k, key in enumerate(keys):
            end = starts[k + 1] if k + 1 < len(starts) else len(blob)
            entry = blob[starts[k]:end].strip()
            entry = re.sub(r"\s*\n\s*\n\s*", " ", entry)
            out.append(f'<a id="ref-{key}"></a>\\[{self.bibnum[key]}\\] {self.inline(entry)}')
            out.append("")
        return out

    def figure(self, caption_html):
        """The exposition's single TikZ figure, in the ```{=latex} form the reader extracts."""
        tex = self.tex
        start = tex.index("\\begin{figure}")
        end = tex.index("\\end{figure}") + len("\\end{figure}")
        env = tex[start:end]
        inp = re.search(r"\\input\{([^}]*)\}", env)
        picture = (self.root / "paper" / inp.group(1)).read_text(encoding="utf-8").rstrip("\n")
        env = env.replace(inp.group(0), picture)
        number = self.printed("fig:cycle-mean")
        page = self.labels["fig:cycle-mean"]["page"]
        pdf = PAGES + self.p["stem"] + f".pdf#page={page}"
        return (["```{=latex}"] + env.split("\n") + ["```", "",
                f"[Figure {number} on page {page} of the PDF]({pdf}) · [SVG rendering](figures/cycle-mean.svg)"])

    def front_matter(self):
        def arg(cmd):
            m = re.search(r"\\" + cmd + r"\{", self.tex)
            return brace_group(self.tex, m.end() - 1)[0]
        title = tex_text_to_md(arg("title"))
        subtitle = tex_text_to_md(arg("subtitle"))
        author = tex_text_to_md(arg("author"))
        date = tex_text_to_md(arg("date"))
        lines = [f"# {title}", ""]
        sub = subtitle.split("\\\n")
        lines.append("\\\n".join(f"*{s.strip()}*" for s in sub))
        lines += ["", f"{author}\\*\\", date, ""]
        if self.p["level"] != "expository":
            sty = (self.root / "paper/paper-house-style.sty").read_text(encoding="utf-8")
            m = re.search(r"\\newcommand\{\\paperprovenance\}\{\\provenancenote\{", sty)
            body = brace_group(sty, m.end() - 1)[0]
            lines += ["\\* " + tex_text_to_md(body), ""]
        return lines

    # ---------------------------------------------------------------- main pass

    @staticmethod
    def special(line):
        """A line that ends a run of paragraph text."""
        s = line.strip()
        return bool(re.match(r"^(\s*``` math\s*$|<a id=\"[^\"]+\"></a>$|</?div\b|<p class=\"evidence-marks\"|#{1,6} |<figure)", s)
                    or re.match(r"^\s*``` math\s*$", line))

    def convert(self):
        src = self.source.split("\n")
        out = []        # (type, text) with type in front, anchor, heading, blank, body
        i = 0
        pending = None   # (label, class) of a theorem-like block awaiting its head
        last_anchor = None
        abstract_next = False
        seen_title = False
        n = len(src)
        while i < n:
            line = src[i]
            stripped = line.strip()
            # title -> front matter from the TeX
            if not seen_title and line.startswith("# "):
                seen_title = True
                out += [("front", x) if x else ("blank", x) for x in "\n".join(self.front_matter()).split("\n")]
                i += 1
                continue
            # abstract head
            if stripped == '<div class="center">' and i + 2 < n and "smallcaps\">Abstract<" in src[i + 2]:
                j = i
                while src[j].strip() != "</div>":
                    j += 1
                i = j + 1
                abstract_next = True
                continue
            # display math
            fm = re.match(r"^(\s*)``` math\s*$", line)
            if fm:
                indent = fm.group(1)
                j = i + 1
                body = []
                while src[j].rstrip() != indent + "```":
                    body.append(src[j])
                    j += 1
                tex = self.display_math("\n".join(body))
                out.append(("body", indent + "$$"))
                for b in tex.split("\n"):
                    out.append(("body", b))
                out.append(("body", indent + "$$"))
                i = j + 1
                continue
            # anchors
            am = re.match(r'^<a id="([^"]+)"></a>$', stripped)
            if am:
                last_anchor = am.group(1)
                out.append(("anchor", line))
                i += 1
                continue
            # figure
            if stripped.startswith("<figure"):
                j = i
                while "</figure>" not in src[j]:
                    j += 1
                out += [("body", x) for x in self.figure("\n".join(src[i:j + 1]))]
                i = j + 1
                continue
            # bibliography
            if stripped == '<div class="thebibliography">':
                j = i + 1
                blob = []
                while src[j].strip() != "</div>":
                    blob.append(src[j])
                    j += 1
                out.append(("anchor", '<a id="references"></a>'))
                out.append(("blank", ""))
                out.append(("heading", "## References"))
                self.headings.append({"anchor": "references", "kind": "section", "level": 2, "number": None,
                                      "title": "References"})
                out.append(("blank", ""))
                out += [("body", x) if x else ("blank", x) for x in self.bibliography(blob)]
                i = j + 1
                continue
            # div wrappers
            dm = re.match(r'^\s*<div(?: id="([^"]+)")?(?: class="([^"]+)")?>\s*$', line)
            if dm:
                label, cls = dm.group(1), dm.group(2)
                if label:
                    out.append(("anchor", f'<a id="{label}"></a>'))
                    last_anchor = label
                if cls in THEOREM_CLASSES:
                    pending = (label, cls)
                elif cls not in (None, "center", "proof", "minipage"):
                    raise ValueError(f"unknown div class {cls}")
                i += 1
                continue
            if re.match(r"^\s*</div>\s*$", line):
                i += 1
                continue
            # evidence marks
            if stripped.startswith('<p class="evidence-marks">'):
                if pending is None or pending[0] is None:
                    raise ValueError("evidence marks outside a labelled block")
                self.evidence[pending[0]] = re.findall(r'href="([^"]+)"', stripped)
                i += 1
                continue
            # headings
            hm = re.match(r"^(#{1,6}) (.*)$", line)
            if hm:
                out.append(("heading", self.heading(len(hm.group(1)), hm.group(2), last_anchor)))
                last_anchor = None
                i += 1
                continue
            if not stripped:
                out.append(("blank", ""))
                i += 1
                continue
            j = i + 1
            while j < n and src[j].strip() and not self.special(src[j]):
                j += 1
            line = "\n".join(src[i:j])
            if pending is not None:
                line = self.theorem_head(line, *pending)
                pending = None
            text = self.inline(line)
            if abstract_next:
                text = "**Abstract.** " + text
                abstract_next = False
            if seen_title and not any(t == "heading" for t, _ in out) and self.p["level"] == "expository" \
                    and text.startswith("*Authorship and AI use.*"):
                out += [("front", x) for x in ("\\* " + text).split("\n")]
            else:
                out += [("body", x) for x in text.split("\n")]
            i = j
        if pending is not None:
            raise ValueError("theorem-like block without a head at end")
        return self.assemble(out)

    # ---------------------------------------------------------------- passages

    def assemble(self, items):
        # collapse blank runs
        clean = []
        for t, x in items:
            if t == "blank" and clean and clean[-1][0] == "blank":
                continue
            clean.append((t, x))
        while clean and clean[-1][0] == "blank":
            clean.pop()
        levels = [int(re.match(r"#+", x).end()) if t == "heading" else None for t, x in clean]
        heads = [k for k, lv in enumerate(levels) if lv is not None]
        top = 3 if self.p["level"] == "long" else 2
        boundaries = set(k for k in heads if levels[k] <= top)
        if self.p["split_long_sections"]:
            ordered = sorted(boundaries)
            for a, b in zip(ordered, ordered[1:] + [len(clean)]):
                if levels[a] == top and b - a > LONG_SECTION_LINES:
                    boundaries |= {k for k in heads if a < k < b and levels[k] == top + 1}
        # each passage: content after a boundary heading up to the next boundary's anchor group
        starts = sorted(boundaries)
        first_heading = heads[0] if heads else len(clean)
        regions = []
        abstract = [k for k, (t, x) in enumerate(clean) if x.startswith("**Abstract.**")]
        if abstract:
            regions.append(("abstract", "Abstract", abstract[0], first_heading))
        for idx, k in enumerate(starts):
            nxt = starts[idx + 1] if idx + 1 < len(starts) else len(clean)
            anchor = None
            back = k - 1
            while back >= 0 and clean[back][0] in ("anchor", "blank"):
                if clean[back][0] == "anchor":
                    anchor = re.search(r'id="([^"]+)"', clean[back][1]).group(1)
                back -= 1
            regions.append((anchor, clean[k][1].lstrip("# "), k + 1, nxt))
        markers_before, markers_after = {}, {}
        passages = []
        used = set()
        for name, heading, a, b in regions:
            # stop before the anchors and blanks that introduce the next heading
            while b > a and clean[b - 1][0] in ("anchor", "blank"):
                b -= 1
            while a < b and clean[a][0] == "blank":
                a += 1
            if a >= b:
                continue
            if any(clean[k][0] == "heading" and k in boundaries for k in range(a, b)):
                raise ValueError("passage spans a boundary")
            safe = re.sub(r"[^A-Za-z0-9_.-]", "-", name or "passage")
            base, n = safe, 1
            while safe in used:
                n += 1
                safe = f"{base}-{n}"
            used.add(safe)
            markers_before[a] = safe
            markers_after[b - 1] = safe
            passages.append({"name": safe, "heading": heading, "start": a, "end": b - 1})
        lines = []
        index_of = {}
        for k, (t, x) in enumerate(clean):
            if k in markers_before:
                lines.append(f"<!-- passage:{markers_before[k]} -->")
            index_of[k] = len(lines)
            lines.append(x)
            if k in markers_after:
                lines.append(f"<!-- /passage:{markers_after[k]} -->")
        text = "\n".join(lines) + "\n"
        rows = []
        for p in passages:
            first = index_of[p["start"]]       # 0-based line of first content
            last = index_of[p["end"]]
            body = "\n".join(lines[first:last + 1])
            labels = [re.sub(r'.*id="([^"]+)".*', r"\1", l) for l in lines[first:last + 1]
                      if re.match(r'^<a id="[^"]+"></a>$', l.strip())]
            result_labels = [l for l in labels if any(b["label"] == l for b in self.blocks)]
            rows.append({"name": p["name"], "heading": p["heading"], "marker_line": first,
                         "first_line": first + 1, "last_line": last + 1, "end_marker_line": last + 2,
                         "results": result_labels,
                         "text_sha256": hashlib.sha256(body.encode()).hexdigest()})
        return text, rows


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def kind_of(target):
    head = target.split(".")[0]
    return {"section": "section", "subsection": "subsection", "subsubsection": "subsubsection",
            "appendix": "appendix", "equation": "equation", "AMS": "equation", "figure": "figure",
            "table": "table", "readercheck": "question", "exercise": "exercise", "theorem": "result",
            "thm": "result", "paragraph*": "paragraph"}.get(head, head)


def main(argv):
    if len(argv) != 4:
        sys.exit(__doc__)
    root, aux_dir, out_dir = Path(argv[1]), Path(argv[2]), Path(argv[3])
    numbering, evidence, sources, report = {}, {}, {"repository": f"https://github.com/{REPO}",
                                                     "commit": COMMIT, "papers": {}}, {}
    converters = {}
    for paper in PAPERS:
        conv = Converter(paper, root, aux_dir, out_dir)
        text, passages = conv.convert()
        out_path = out_dir / paper["out"]
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(text, encoding="utf-8")
        (out_path.parent / "passages.json").write_text(
            json.dumps(passages, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
        pdf_src = root / "paper/257" / (paper["stem"] + ".pdf")
        shutil.copyfile(pdf_src, out_dir / paper["pdf"])
        classes = {b["label"]: b for b in conv.blocks if b["label"]}
        nb = {}
        for label, e in sorted(conv.labels.items()):
            row = {"printed": e["printed"], "page": int(e["page"]), "kind": kind_of(e["target"]),
                   "title": e["title"]}
            if label in classes:
                row["kind"] = classes[label]["kind"].lower()
            nb[label] = row
        numbering[paper["level"]] = {
            "labels": nb,
            "unlabelled_results": [{"kind": b["kind"].lower(), "printed": b["number"]}
                                   for b in conv.blocks if not b["label"]],
            "anchors": "Anchor ids are the TeX labels unchanged; the reader accepts a colon in an id.",
        }
        evidence[paper["level"]] = dict(sorted(conv.evidence.items()))
        files = {"full_text_markdown": paper_rel(root, conv.src_path), "tex": paper_rel(root, conv.tex_path)}
        hashes = {"full_text_markdown": sha(conv.src_path), "tex": sha(conv.tex_path),
                  "aux": sha(conv.aux_path), "pdf": sha(pdf_src)}
        extra = {}
        for rel in paper["tex_extra"] + [f"paper/evidence/{paper['stem']}.tex"]:
            if (root / rel).exists():
                extra[rel] = sha(root / rel)
        sources["papers"][paper["level"]] = {
            "title": conv.headings and None or None,
            "source_files": {**files, "aux": conv.aux_path.name, "pdf": f"paper/257/{paper['stem']}.pdf"},
            "sha256": hashes,
            "tex_inputs_sha256": extra,
            "outputs_sha256": {paper["out"]: sha(out_path), paper["pdf"]: sha(out_dir / paper["pdf"]),
                               str(Path(paper["out"]).parent / "passages.json"):
                                   sha(out_path.parent / "passages.json")},
        }
        del sources["papers"][paper["level"]]["title"]
        report[paper["level"]] = sorted(set(conv.notes))
        converters[paper["level"]] = conv
    svg = out_dir / "expository/figures/cycle-mean.svg"
    if svg.exists():
        sources["papers"]["expository"]["outputs_sha256"]["expository/figures/cycle-mean.svg"] = sha(svg)
    (out_dir / "numbering.json").write_text(json.dumps(numbering, indent=1, ensure_ascii=False) + "\n",
                                            encoding="utf-8")
    (out_dir / "evidence-marks.json").write_text(json.dumps(evidence, indent=1, ensure_ascii=False) + "\n",
                                                 encoding="utf-8")
    sources["notes"] = report
    (out_dir / "SOURCES.json").write_text(json.dumps(sources, indent=1, ensure_ascii=False) + "\n",
                                          encoding="utf-8")
    for level, notes in report.items():
        for note in notes:
            print(f"{level}: {note}")


def paper_rel(root, path):
    return str(Path(path).relative_to(root))


if __name__ == "__main__":
    main(sys.argv)
