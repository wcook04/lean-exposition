#!/usr/bin/env python3
"""Verify the Erdős #257 transcriptions against their pinned sources.

Usage: check.py SOURCE_EXPORT_ROOT AUX_DIR OUTPUT_DIR [SCRATCH_DIR]

Checks (exit status 1 if any fails):
  a. word fidelity: the source full text and each output, with markup and math delimiters
     removed, give the same token sequence once the places the rules change are canonicalised
     on both sides (reference numbers, citation labels, heading numbers, evidence marks,
     link URLs, \\label/\\tag/equation wrappers). Every remaining difference is printed.
     The front matter is compared with the TeX \\title, \\subtitle, \\author, \\date and note.
  b. every math span, located by the reader's own protectMath (site/src/reader/math.ts),
     renders with the reader's renderTex (KaTeX, throwOnError); $ balance per passage; the
     number of spans equals the number in the source.
  c. every internal and cross-paper link resolves to an explicit anchor in its target file.
  d. every printed number in headings, result heads and equation tags equals the aux (and the
     toc for unlabelled headings); paper_evidence.json labels have anchors and equal numbers.
  e. passages: every non-blank body line lies in exactly one passage; passages.json agrees.
  f. determinism: with SCRATCH_DIR, convert.py runs twice there and both runs equal OUTPUT_DIR.
"""

import difflib
import hashlib
import json
import re
import subprocess
import sys
import urllib.parse
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import convert  # noqa: E402  (shared constants and the aux parser only)

SITE = HERE.parents[2] / "site"
FAILURES = []


def fail(msg):
    FAILURES.append(msg)
    print("  FAIL " + msg)


# ----------------------------------------------------------------------------- (a) words

MATH_TOKEN = re.compile(r"\\[A-Za-z]+\*?|\\.|[A-Za-z0-9]+|\S")
WORD_TOKEN = re.compile(r"[^\W_]+(?:['’][^\W_]+)*|[^\w\s]")
NUMLIKE = r"(?:[0-9]+(?:\.[0-9]+)*|[A-Z](?:\.[0-9]+)*)"
HEADNUM = r"(?:[0-9]+(?:\.[0-9]+)*\.?|[A-Z]\.|[A-Z](?:\.[0-9]+)+)"


def math_tokens(tex, aux):
    tex = re.sub(r"\\label\{[^}]*\}", " ", tex)
    tex = re.sub(r"\\tag\{((?:[^{}]|\{[^{}]*\})*)\}", " ", tex)
    tex = re.sub(r"\\(begin|end)\{(equation\*?)\}", " ", tex)
    tex = re.sub(r"\\(begin|end)\{align\*\}", r"\\\1{aligned}", tex)
    tex = re.sub(r"\\(begin|end)\{gather\*\}", r"\\\1{gathered}", tex)
    tex = re.sub(r"\\ensuremath\s*", " ", tex)
    tex = re.sub(r"\\ref\{([^}]*)\}", lambda m: aux[m.group(1)]["printed"], tex)
    toks = MATH_TOKEN.findall(tex)
    return [t for t in toks if t not in ("{", "}")]   # \ensuremath{X} braces


def canon_text(text, side, aux, bibkeys):
    """Rule-governed places become fixed tokens, then markup is removed."""
    if side == "source":
        text = re.sub(r"\[\\\[[A-Za-z]+:[^\]\\]+\\\]\]\(#[^)\s]+\)", " \x02REF\x03 ", text)
        def cite(m):
            segs = m.group(1).split(";")
            if not all(s.split(",")[0].strip() in bibkeys for s in segs):
                return m.group(0)
            notes = [s.partition(",")[2] for s in segs]
            return " \x02CITE\x03 " + " ".join(notes) + " "
        text = re.sub(r"\\\[([a-z][a-z0-9]*(?:[,;][^\]]*?)?)\\\]", cite, text)
    else:
        def cite(m):
            inner = m.group(1)
            if not re.match(r"\[\d+\]\(#ref-", inner):
                return m.group(0)
            notes = re.sub(r"\[\d+\]\(#ref-[^)]+\)", "", inner)
            notes = re.sub(r"^(,\s*)+", "", notes.strip())
            notes = re.sub(r"(?:^|,\s*)(?=,)", "", notes)
            return " \x02CITE\x03 " + notes + " "
        text = re.sub(r"\\\[((?:\[\d+\]\(#ref-[^)]+\)(?:,\s*)?)+[^\]]*?)\\\]", cite, text)
        text = re.sub(r"\[\(" + r"[^)\]]+" + r"\)\]\(#[^)\s]+\)", " \x02REF\x03 ", text)
    text = re.sub(r"\[" + NUMLIKE + r"\]\((#[^)\s]+|\.\./[^)\s]+)\)", " \x02REF\x03 ", text)
    # theorem-like heads: "Kind N" in bold or italic
    text = re.sub(r"(\*\*|\*)(Theorem|Lemma|Proposition|Corollary|Definition|Remark|Observation|Problem|"
                  r"Question|Exercise) " + NUMLIKE + r"(?=[\s*(.])", lambda m: m.group(1) + m.group(2) + " \x02NUM\x03", text)
    return text


def strip_markup(text):
    text = re.sub(r"<[^>\n]+>", " ", text)                     # HTML tags, autolinks kept below
    while True:
        new = re.sub(r"\[([^\[\]]*)\]\([^)\s]*\)", r"\1", text)  # links -> text (innermost first)
        if new == text:
            break
        text = new
    text = text.replace("\\*", " ").replace("\\[", "[").replace("\\]", "]").replace("\\#", "#")
    text = re.sub(r"\\\n", "\n", text)
    text = re.sub(r"[*`]", " ", text)
    text = re.sub(r"^#{1,6} ", " ", text, flags=re.M)
    return text


def tokens(md, side, aux, bibkeys):
    """Token list of a document; math spans become math tokens, text becomes words."""
    out = []
    md = canon_text(md, side, aux, bibkeys)
    md = re.sub(r"\]\([^)\s]+\)", "]", md)       # link destinations are rule-governed
    # display math
    if side == "source":
        pattern = re.compile(r"^([ \t]*)``` math\n(.*?)\n\1```\s*$|\$`(.*?)`\$", re.S | re.M)
    else:
        pattern = re.compile(r"^([ \t]*)\$\$\n(.*?)\n\1\$\$[ \t]*$|(?<!\\)\$(?!\$)((?:[^$\\]|\\.)+)\$", re.S | re.M)
    pos = 0
    for m in pattern.finditer(md):
        out += text_tokens(md[pos:m.start()], side, aux, bibkeys)
        tex = m.group(2) if m.group(2) is not None else m.group(3)
        out += ["⟨" + t for t in math_tokens(tex, aux)]
        pos = m.end()
    out += text_tokens(md[pos:], side, aux, bibkeys)
    return out


def text_tokens(text, side, aux, bibkeys):
    text = strip_markup(text)
    toks = []
    for t in re.findall(r"\x02[A-Z]+\x03|https?://\S+|" + WORD_TOKEN.pattern, text):
        toks.append(t.strip("\x02\x03") if t.startswith("\x02") else t)
    return toks


def prepare_source(src, level):
    """Remove what the rules remove (title, evidence marks, bibliography marker)."""
    lines = src.split("\n")
    out = []
    title_done = False
    for line in lines:
        if not title_done and line.startswith("# "):
            title_done = True
            continue
        if line.strip().startswith('<p class="evidence-marks">'):
            continue
        out.append(line)
    text = "\n".join(out)
    text = re.sub(r'(<div class="thebibliography">\s*)9+\s', r"\1", text)
    if level != "expository":
        text = text.replace('<span class="smallcaps">Abstract</span>', "Abstract")
    return text


def prepare_output(md, level):
    """Remove rule-added material: front matter, passage markers, labels, figure art."""
    lines = md.split("\n")
    # front matter: up to the abstract (short, long) or the first section anchor (expository)
    k = next(i for i, l in enumerate(lines) if l.startswith("<!-- passage:") or l.startswith('<a id="sec:'))
    front = lines[:k]
    body = lines[k:]
    if level == "expository":
        prov = [l for l in front if l.startswith("\\* *Authorship")]
        body = prov + body
    text = "\n".join(l for l in body if not re.match(r"^<!-- /?passage:", l))
    text = text.replace("**Abstract.** ", "Abstract ")
    first = 3 if level == "long" else 2     # the long record's level-2 headings are parts
    text = re.sub(r"^(#{%d,6}) " % first + HEADNUM + r" ", r"\1 ", text, flags=re.M)
    text = re.sub(r'<a id="references"></a>\s*## References', "", text)
    text = re.sub(r'(<a id="ref-[^"]+"></a>)\\\[\d+\\\] ', r"\1", text)
    def figure(m):
        cap = re.search(r"\\caption\{(.*?)\}\n\\label", m.group(0), re.S).group(1)
        return "\n" + cap + "\n"
    text = re.sub(r"```\{=latex\}\n.*?\n```\n\n\[Figure [^\n]*\n", figure, text, flags=re.S)
    return front, text


def figure_source(text):
    # the full text's <figcaption> carries pandoc's MathML-free HTML for the inline maths
    def cap(m):
        inner = m.group(1)
        inner = re.sub(r'<span class="math inline">(.*?)</span>',
                       lambda mm: "$`" + re.sub(r"<[^>]+>", "", mm.group(1)).replace(" ", "") + "`$", inner)
        return inner
    return re.sub(r"<figure[^>]*>\s*<figcaption>(.*?)</figcaption>\s*</figure>", cap, text, flags=re.S)


def check_words(paper, root, aux, bibkeys, out_dir):
    # Rule 8 (detail notes back in their cells, Pandoc's separator comment) on the source side.
    src = convert.source_fixes((root / "docs/papers/full-text" / (paper["stem"] + ".md")).read_text(encoding="utf-8"))
    md = (out_dir / paper["out"]).read_text(encoding="utf-8")
    src_text = figure_source(prepare_source(src, paper["level"]))
    front, out_text = prepare_output(md, paper["level"])
    a = tokens(src_text, "source", aux, bibkeys)
    b = tokens(out_text, "output", aux, bibkeys)
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    diffs = [op for op in sm.get_opcodes() if op[0] != "equal"]
    for tag, i1, i2, j1, j2 in diffs[:40]:
        fail(f"{paper['level']} word difference ({tag}): source {' '.join(a[max(0, i1 - 4):i2 + 4])!r} "
             f"-> output {' '.join(b[max(0, j1 - 4):j2 + 4])!r}")
    # front matter against the TeX
    tex = (root / "paper/257" / (paper["stem"] + ".tex")).read_text(encoding="utf-8")
    expected = []
    for cmd in ("title", "subtitle", "author", "date"):
        m = re.search(r"\\" + cmd + r"\{", tex)
        expected.append(convert.brace_group(tex, m.end() - 1)[0])
    if paper["level"] != "expository":
        sty = (root / "paper/paper-house-style.sty").read_text(encoding="utf-8")
        m = re.search(r"\\newcommand\{\\paperprovenance\}\{\\provenancenote\{", sty)
        expected.append(convert.brace_group(sty, m.end() - 1)[0])
    exp_text = convert.tex_accents(" ".join(expected))
    exp_text = re.sub(r"\\emph\{([^{}]*)\}", r"\1", exp_text).replace("~", " ").replace("\\\\", " ")
    exp_tok = tokens(exp_text.replace("\\#", "#"), "output", aux, bibkeys)
    keep = [l for l in front if not l.startswith("<a id=")
            and not (paper["level"] == "expository" and l.startswith("\\* *Authorship"))]
    front_text = "\n".join(keep).replace("# ", "", 1)
    got_tok = tokens(front_text, "output", aux, bibkeys)
    if got_tok != exp_tok:
        fail(f"{paper['level']} front matter differs from TeX: {got_tok[:30]} vs {exp_tok[:30]}")
    return len(a), len(b), len(diffs), len(exp_tok)


# ----------------------------------------------------------------------------- (b) KaTeX

NODE = r"""
const [mathTs, ...files] = process.argv.slice(1);
const m = await import(mathTs);
const fs = await import('fs');
const out = {};
for (const f of files) {
  let text = fs.readFileSync(f, 'utf8');
  // As the reader: whole-line comments vanish; raw LaTeX figures are taken out, captions kept.
  const captions = [];
  text = text.replace(/^```\{=latex\}\n([\s\S]*?)^```$/gm, (_all, body) => {
    const c = /\\caption\{([\s\S]*?)\}\n\\label/.exec(body); if (c) captions.push(c[1]); return '';
  });
  const passages = [...text.matchAll(/<!-- passage:([^\s>]+) -->\n([\s\S]*?)\n<!-- \/passage:\1 -->/g)];
  text = text.replace(/^[ \t]*<!--[\s\S]*?-->[ \t]*(?:\r?\n|$)/gm, '');
  const spans = [];
  m.protectMath(text, spans);
  for (const c of captions) m.protectMath(c, spans);
  const errors = [];
  let inline = 0, display = 0;
  for (const s of spans) {
    s.display ? display++ : inline++;
    const r = m.renderTex(s.tex, s.display);
    if (r.error) errors.push({tex: s.tex.slice(0, 120), error: r.error.slice(0, 160)});
  }
  const unbalanced = [];
  for (const p of passages) {
    const r = m.protectMath(p[2], []);
    const stray = r.text.replace(/\\\$/g, '').replace(/`[^`]*`/g, '');
    if (stray.includes('$')) unbalanced.push(p[1]);
  }
  out[f] = {spans: spans.length, inline, display, errors, passages: passages.length, unbalanced};
}
console.log(JSON.stringify(out));
"""


def source_math_count(src):
    inline = len(re.findall(r"\$`.*?`\$", src, re.S))
    display = len(re.findall(r"^\s*``` math\s*$", src, re.M))
    return inline + display


# ----------------------------------------------------------------------------- (c, d, e)

def anchors_of(md):
    return set(re.findall(r'<a id="([^"]+)"></a>', md))


def check_links(paper, md, all_md):
    own = anchors_of(md)
    frag = cross = ext = 0
    for m in re.finditer(r"\]\(([^)\s]+)\)", md):
        url = m.group(1)
        if url.startswith("#"):
            frag += 1
            if urllib.parse.unquote(url[1:]) not in own:
                fail(f"{paper['level']}: unresolved #{url[1:]}")
        elif url.startswith("../"):
            cross += 1
            path, _, anchor = url.partition("#")
            target = next((p for p in convert.PAPERS if "../" + p["out"] == path), None)
            if target is None or anchor not in anchors_of(all_md[target["level"]]):
                fail(f"{paper['level']}: unresolved cross-paper link {url}")
        elif re.match(r"https?://", url):
            ext += 1
        elif url == "figures/cycle-mean.svg":
            if not (Path(paper["_out_dir"]) / "expository/figures/cycle-mean.svg").exists():
                fail("missing figure SVG")
        else:
            fail(f"{paper['level']}: unexpected link {url}")
    return frag, cross, ext


def check_numbers(paper, md, aux, toc, evidence_rows):
    lines = md.split("\n")
    checked = 0
    # result heads following their anchors
    last = None
    heads = {}
    order = []
    for k, line in enumerate(lines):
        am = re.match(r'^<a id="([^"]+)"></a>$', line.strip())
        if am:
            last = am.group(1)
            continue
        hm = re.match(r"^\*\*(Theorem|Lemma|Proposition|Corollary|Definition|Remark|Observation|Problem|Question|"
                      r"Exercise) (" + NUMLIKE + r")[ .]", line)
        if hm:
            label = last if last and last in aux and aux[last]["target"].split(".")[0] in (
                "theorem", "thm", "readercheck", "exercise") else None
            order.append((hm.group(1), hm.group(2), label))
            if label:
                heads[label] = hm.group(2)
                checked += 1
                if aux[label]["printed"] != hm.group(2):
                    fail(f"{paper['level']}: {label} printed {hm.group(2)} != aux {aux[label]['printed']}")
        if line.strip():
            if not am and not line.startswith("<!--"):
                last = None if not line.startswith("$$") else last
        # equation tags right after an equation anchor
        if line == "$$" and k >= 2 and re.match(r'^<a id="(eq:[^"]+)"></a>$', lines[k - 2]):
            label = re.match(r'^<a id="(eq:[^"]+)"></a>$', lines[k - 2]).group(1)
            j = k + 1
            body = []
            while lines[j] != "$$":
                body.append(lines[j])
                j += 1
            tag = re.findall(r"\\tag\{((?:[^{}]|\{[^{}]*\})*)\}", "\n".join(body))
            checked += 1
            if label in aux and (not tag or tag[0] != aux[label]["printed"]):
                fail(f"{paper['level']}: {label} tag {tag} != aux {aux[label]['printed']}")
    for label, e in aux.items():
        if e["target"].split(".")[0] in ("theorem", "thm", "readercheck", "exercise") and label not in heads:
            fail(f"{paper['level']}: result label {label} has no head after its anchor")
    # numbered sequences restart per section (or are global in the exposition)
    seen = {}
    for kind, num, _label in order:
        key = kind if paper["level"] == "expository" else "thm"
        if paper["level"] == "expository" and kind in ("Theorem",):
            key = "thm"
        prefix, _, n = num.rpartition(".")
        prev = seen.get((key, prefix), 0)
        if int(n) != prev + 1:
            fail(f"{paper['level']}: {kind} {num} out of sequence")
        seen[(key, prefix)] = int(n)
    # headings against the toc
    want = [(e["number"], convert.norm_title(e["title"])) for e in toc
            if e["number"] is not None and e["kind"] in ("section", "subsection", "subsubsection")]
    got = []
    for line in lines:
        hm = re.match(r"^#{%d,6} (" % (3 if paper["level"] == "long" else 2) + HEADNUM + r") (.*)$", line)
        if hm:
            got.append((hm.group(1).rstrip("."), convert.norm_title(hm.group(2))))
    if got != want:
        for x, y in zip(got, want):
            if x != y:
                fail(f"{paper['level']}: heading {x} != toc {y}")
                break
        if len(got) != len(want):
            fail(f"{paper['level']}: {len(got)} numbered headings, toc has {len(want)}")
    checked += len(got)
    # labelled headings
    for k, line in enumerate(lines):
        am = re.match(r'^<a id="([^"]+)"></a>$', line)
        if am and am.group(1) in aux and k + 2 < len(lines) and lines[k + 2].startswith("#"):
            hm = re.match(r"^#{2,6} (" + HEADNUM + r") ", lines[k + 2])
            if hm and hm.group(1).rstrip(".") != aux[am.group(1)]["printed"]:
                fail(f"{paper['level']}: heading {am.group(1)} {hm.group(1)} != aux")
    ev = 0
    for row in evidence_rows:
        ev += 1
        if heads.get(row["label"]) != row["number"]:
            fail(f"{paper['level']}: paper_evidence {row['label']} number {row['number']} != "
                 f"output {heads.get(row['label'])}")
    return checked, len(got), len(heads), ev


def check_passages(paper, md, out_dir):
    lines = md.split("\n")
    inside = None
    names = []
    first_passage = next(k for k, l in enumerate(lines) if l.startswith("<!-- passage:") or l.startswith('<a id="sec:'))
    for k, line in enumerate(lines):
        om = re.match(r"^<!-- passage:([^\s>]+) -->$", line)
        cm = re.match(r"^<!-- /passage:([^\s>]+) -->$", line)
        if om:
            if inside:
                fail(f"{paper['level']}: nested passage {om.group(1)} in {inside}")
            inside = om.group(1)
            names.append(inside)
        elif cm:
            if cm.group(1) != inside:
                fail(f"{paper['level']}: passage close {cm.group(1)} without open")
            inside = None
        elif inside is None and line.strip() and k >= first_passage:
            if not (re.match(r'^<a id="[^"]+"></a>$', line) or re.match(r"^#{2,6} ", line)):
                fail(f"{paper['level']}: line {k + 1} outside every passage: {line[:60]!r}")
    if len(names) != len(set(names)):
        fail(f"{paper['level']}: duplicate passage names")
    rows = json.loads((out_dir / paper["out"]).parent.joinpath("passages.json").read_text())
    if [r["name"] for r in rows] != names:
        fail(f"{paper['level']}: passages.json names differ")
    for r in rows:
        body = "\n".join(lines[r["first_line"] - 1:r["last_line"]])
        opened = lines[r["first_line"] - 2] == f"<!-- passage:{r['name']} -->"
        closed = lines[r["last_line"]] == f"<!-- /passage:{r['name']} -->"
        if hashlib.sha256(body.encode()).hexdigest() != r["text_sha256"] or not opened or not closed:
            fail(f"{paper['level']}: passages.json row {r['name']} does not match the file")
    return len(names)


# ----------------------------------------------------------------------------- main

def main(argv):
    if len(argv) not in (4, 5):
        sys.exit(__doc__)
    root, aux_dir, out_dir = Path(argv[1]), Path(argv[2]), Path(argv[3]).resolve()
    scratch = Path(argv[4]) if len(argv) == 5 else None
    evidence_json = json.loads((root / "evidence/paper_evidence.json").read_text())
    ev_rows = {p["paper_id"]: p["results"] for p in evidence_json["papers"]}
    marks = json.loads((out_dir / "evidence-marks.json").read_text())
    all_md = {p["level"]: (out_dir / p["out"]).read_text(encoding="utf-8") for p in convert.PAPERS}
    summary = {}

    print("(b) KaTeX rendering with the reader's math.ts")
    if not (SITE / "node_modules/katex").exists():
        fail("site/node_modules/katex is missing: run npm ci in site/")
        node = {}
    else:
        res = subprocess.run(["node", "--input-type=module", "-e", NODE, str(SITE / "src/reader/math.ts")]
                             + [str(out_dir / p["out"]) for p in convert.PAPERS],
                             capture_output=True, text=True, check=True)
        node = json.loads(res.stdout)

    for paper in convert.PAPERS:
        paper = dict(paper, _out_dir=str(out_dir))
        level = paper["level"]
        aux, toc, bib = convert.parse_aux((aux_dir / (paper["stem"] + ".aux")).read_text(encoding="utf-8"))
        bibkeys = {k for k, _ in bib}
        md = all_md[level]
        src = (root / "docs/papers/full-text" / (paper["stem"] + ".md")).read_text(encoding="utf-8")
        print(f"== {level}: {paper['out']}")
        words_src, words_out, ndiff, front = check_words(paper, root, aux, bibkeys, out_dir)
        print(f"(a) words compared: source {words_src}, output {words_out}, unexplained differences {ndiff}; "
              f"front-matter tokens {front} equal to the TeX")
        r = node.get(str(out_dir / paper["out"]), {})
        front_lines = md.split("\n")[:md.split("\n").index(next(l for l in md.split("\n")
                                                                  if l.startswith(("<!-- passage:", '<a id="sec:'))))]
        front_math = len(re.findall(r"(?<!\\)\$((?:[^$\\]|\\.)+)\$", "\n".join(
            l for l in front_lines if not l.startswith("\\* *Authorship"))))
        caption_math = len(re.findall(r'<span class="math inline">', src))
        expect = source_math_count(src) + front_math + caption_math
        print(f"(b) formulas {r.get('spans')} (inline {r.get('inline')}, display {r.get('display')}), "
              f"expected {expect}; render failures {len(r.get('errors', []))}; "
              f"passages with unbalanced $: {len(r.get('unbalanced', []))}")
        for e in r.get("errors", [])[:10]:
            fail(f"{level} KaTeX: {e}")
        if r.get("unbalanced"):
            fail(f"{level} unbalanced $ in passages {r['unbalanced']}")
        if r.get("spans") != expect:
            fail(f"{level}: {r.get('spans')} formulas, source has {expect}")
        frag, cross, ext = check_links(paper, md, all_md)
        print(f"(c) internal links {frag} and cross-paper links {cross} resolved; external links {ext} (not fetched)")
        rows = ev_rows.get(paper["stem"], []) if level != "expository" else []
        checked, nheads, nres, nev = check_numbers(paper, md, aux, toc, rows)
        print(f"(d) numbers checked {checked}: numbered headings {nheads} equal the toc, labelled results "
              f"{nres} equal the aux, paper_evidence results {nev} with equal numbers")
        # evidence marks recorded
        src_marks = [re.findall(r'href="([^"]+)"', l) for l in src.split("\n")
                     if l.startswith('<p class="evidence-marks">')]
        if sorted(map(tuple, src_marks)) != sorted(tuple(v) for v in marks[level].values()):
            fail(f"{level}: evidence-marks.json differs from the removed lines")
        n = check_passages(paper, md, out_dir)
        print(f"(e) passages {n}; evidence-mark lines removed and recorded {len(src_marks)}")
        summary[level] = dict(words=words_src, formulas=r.get("spans"), links=frag + cross, results=nres,
                              evidence=nev, passages=n)

    if scratch:
        print("(f) determinism")
        outs = []
        for run in ("run1", "run2"):
            d = scratch / run
            if d.exists():
                subprocess.run(["rm", "-rf", str(d)], check=True)
            d.mkdir(parents=True)
            fig = out_dir / "expository/figures/cycle-mean.svg"
            (d / "expository/figures").mkdir(parents=True)
            (d / "expository/figures/cycle-mean.svg").write_bytes(fig.read_bytes())
            subprocess.run([sys.executable, str(HERE / "convert.py"), str(root), str(aux_dir), str(d)],
                           check=True, capture_output=True)
            outs.append({str(p.relative_to(d)): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in sorted(d.rglob("*")) if p.is_file()})
        if outs[0] != outs[1]:
            fail("two runs differ")
        for rel, h in outs[0].items():
            if hashlib.sha256((out_dir / rel).read_bytes()).hexdigest() != h:
                fail(f"{rel} differs from a fresh run")
        print(f"    {len(outs[0])} files identical across two runs and equal to {out_dir.name}/")

    print("SUMMARY", json.dumps(summary))
    print("RESULT", "FAIL" if FAILURES else "PASS", f"({len(FAILURES)} failures)")
    sys.exit(1 if FAILURES else 0)


if __name__ == "__main__":
    main(sys.argv)
