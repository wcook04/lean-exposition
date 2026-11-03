"""Tests for the register profiler, the packaged register rules and the register CLI."""

import contextlib
import io
import json
import os
import sys
import tempfile
import unittest

from lean_exposition import register as pr
from lean_exposition.cli import main as cli_main

# An assistant-style paragraph: staccato, contrastive, meta-narrating, hedged.
AI_TEXT = """
The key idea is simple. Here is the mechanism. The bound is not a proof, but a certificate.
Crucially, the record is checked in Lean. The receipt is verified. The ledger is exact.
This section does not establish irrationality. The question remains open. We do not claim more.
The pipeline is precise, explicit, and direct. The point is structural, not numerical.
The mechanism is the carry, not the tail. The hard step is the gap, rather than the size.
Importantly, the evidence class is recorded. The formal record is checked. The receipt is exact.
This matters because the claim is bounded; the boundary is explicit; the record is audited.
"""

# A human-style mathematical paragraph: first person plural, Let/Suppose, long varied sentences.
HUMAN_TEXT = """
Let $q\\ge2$ be an integer and suppose that $(a_n)$ is a sequence of positive integers with
$a_{n+1}\\ge a_n^2$ for all large $n$. We show that the sum of the reciprocals is irrational,
and in fact that its irrationality exponent is at least two, by comparing the partial sums with the
denominators they produce. Note that the hypothesis cannot be weakened to $a_{n+1}\\ge a_n^{2-\\epsilon}$,
as the example of Sylvester's sequence (which we recall in Section 3) shows.

Suppose now that the sum were a rational number $p/q$. Then for every $N$ the number
$q a_1\\cdots a_N$ times the tail would be a positive integer, which we can bound from above. Fix such an $N$.
Since the tail is dominated by its first term, we obtain a contradiction for large $N$. This is
essentially the classical argument of Erdős, although he phrased it differently.
Is the same true when the growth condition holds only along a subsequence? We do not know.
"""

TEX_DOC = r"""
\documentclass{article}
\usepackage{amsmath}
\newcommand{\Ser}{S}
\newcommand{\Count}{714}
\title{A title that must not appear}
\begin{document}
\maketitle
\begin{abstract}
We study the series $\Ser=\sum_n 1/(n!-1)$ and prove a basis theorem.
\end{abstract}
\section{Introduction}\label{sec:intro}
% a comment that must disappear
Erd\H{o}s asked whether $\Ser$ is irrational \cite[p.~102]{erdos1988}; see
Theorem~\ref{thm:main} and \eqref{eq:one}. The ledger has \Count{} rows.
\[
  \sum_{n\ge 2} \frac{1}{n!-1} = 0.7301\ldots
\]
We call this the \emph{factorial series} and write \href{https://example.org/x}{the linked text}.
\begin{equation}\label{eq:one}
 a_n = b_n
\end{equation}
The final sentence of the paragraph is here.

\begin{theorem}[Main]\label{thm:main}
Every integer vector has a unique expansion.
\end{theorem}
\begin{thebibliography}{9}
\bibitem{erdos1988} P. Erdős, A bibliography entry that must not appear.
\end{thebibliography}
\end{document}
"""

MD_DOC = """# Introduction

A series of unit fractions $$\\sum_k 1/a_k$$ was named an *Ahmes series* by Erdős and Straus [@ES64], but the
term has seldom been used [@TY02; @HT04]. We conclude that the condition [\\[eq:x\\]](#eq:x){reference-type="eqref" reference="eq:x"} is sharp.

::: theorem
**Theorem 1**. *For every $d$ there is a sequence with rational sums.*
:::

[^1]: A footnote definition that must not appear.

# References

\\[ES64\\] P. Erdős and E. G. Straus, A reference entry that must not appear.
"""


def _write(path, text):
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)


def doc(text, fmt):
    return pr.document_from_text(text, "x." + ("tex" if fmt == "tex" else "md"), fmt)


def feats(text, fmt="md"):
    return pr.compute_features(doc(text, fmt))


class TestSentenceSplitter(unittest.TestCase):
    def spl(self, t):
        return [t[a:b].strip() for a, b in pr.split_sentences(t)]

    def test_abbreviations_do_not_split(self):
        t = ("This follows, e.g. Theorem 2 of Smith et al. It holds, cf. Prop. 3 and Thm. 4, i.e. Lemma 5. "
             "See Fig. 2 and Sec. 4 for details. The value is 1.2640847 exactly. Then we stop.")
        out = self.spl(t)
        self.assertIn("See Fig. 2 and Sec. 4 for details.", out)
        self.assertIn("The value is 1.2640847 exactly.", out)
        self.assertIn("Then we stop.", out)
        self.assertTrue(any(s.startswith("This follows, e.g. Theorem 2") for s in out))
        self.assertTrue(all(not s.startswith("Prop") and not s.startswith("Theorem 2") for s in out))

    def test_initials_and_page_refs(self):
        out = self.spl("This is due to G. H. Hardy and J. E. Littlewood, see p. 12 there. Next sentence.")
        self.assertEqual(len(out), 2)

    def test_math_placeholder_then_capital_splits(self):
        out = self.spl("The remainder is MATH . We classify the vectors. At fixed MATH , all agree.")
        self.assertEqual(len(out), 3)

    def test_question_and_exclamation(self):
        self.assertEqual(len(self.spl("Is it irrational? Nobody knows! Perhaps.")), 3)


class TestTexStripping(unittest.TestCase):
    def setUp(self):
        self.d = doc(TEX_DOC, "tex")
        self.text = " ".join(s.text for s in self.d.sentences)

    def test_keeps_prose(self):
        self.assertIn("Erdos asked whether MATH is irrational", self.text)
        self.assertIn("factorial series", self.text)
        self.assertIn("the linked text", self.text)
        self.assertIn("Every integer vector has a unique expansion.", self.text)
        self.assertIn("The ledger has 714 rows.", self.text)  # zero-argument macro expanded

    def test_drops_math_refs_comments_preamble_bibliography(self):
        for bad in ("sum_", "frac", "0.7301", "a_n", "comment", "must not appear", "erdos1988",
                    "sec:intro", "example.org", "\\", "{", "}", "Main"):
            self.assertNotIn(bad, self.text, bad)
        self.assertIn("REF", self.text)

    def test_abstract_detected(self):
        self.assertTrue(self.d.abstract_words and 8 <= self.d.abstract_words <= 16)
        self.assertTrue(any(p.abstract for p in self.d.paragraphs))

    def test_heading_detected_and_line_numbers(self):
        heads = [p.text for p in self.d.paragraphs if p.kind == "heading"]
        self.assertEqual(heads, ["Introduction"])
        lines = TEX_DOC.split("\n")
        for s in self.d.sentences:
            if s.text.startswith("We call this"):
                self.assertIn("We call this", lines[s.line - 1])
            if s.text.startswith("The final sentence"):
                self.assertIn("The final sentence", lines[s.line - 1])


class TestMarkdownStripping(unittest.TestCase):
    def test_pandoc_markup(self):
        d = doc(MD_DOC, "md")
        t = " ".join(s.text for s in d.sentences)
        self.assertIn("Ahmes series by Erdős and Straus", t)
        self.assertNotIn("@ES64", t)
        self.assertNotIn("reference-type", t)
        self.assertNotIn("must not appear", t)
        self.assertNotIn("Theorem 1", t)   # theorem label stripped, statement kept
        self.assertIn("For every MATH there is a sequence with rational sums.", t)
        self.assertIn("REF", t)

    def test_pandoc_bibliography_block_dropped(self):
        raw = ("# Intro\n\nWe prove the theorem in the next section of this paper.\n\n"
               ":::: thebibliography\n::: {#ref1}\nP. Billingsley, Ergodic theory and information, Wiley, 1965.\n:::\n")
        t = " ".join(s.text for s in doc(raw, "md").sentences)
        self.assertIn("We prove the theorem", t)
        self.assertNotIn("Billingsley", t)

    def test_pdf_two_column_split(self):
        left = ["Left column sentence number %d continues here." % i for i in range(20)]
        right = ["Right column text line %d goes on and on." % i for i in range(20)]
        raw = "\f" + "\n".join(l.ljust(60) + "     " + r for l, r in zip(left, right)) + "\n"
        d = doc(raw, "md")
        t = " ".join(s.text for s in d.sentences)
        self.assertLess(t.index("Left column sentence number 19"), t.index("Right column text line 0"))
        self.assertNotIn("continues here. Right", t.replace("  ", " ")[:t.index("Right column text line 0") - 1] + "x")


class TestFeaturesFire(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ai = feats(AI_TEXT)
        cls.hu = feats(HUMAN_TEXT)

    def test_directional_features(self):
        higher_in_ai = ["contrast_rate", "meta_narration_rate", "hedge_rate", "status_vocab_rate",
                        "intensifier_rate", "short_sent_share", "semicolon_rate", "negation_rate",
                        "same_opener_share", "triad_rate"]
        for f in higher_in_ai:
            self.assertGreater(self.ai[f], self.hu[f], f)
        higher_in_human = ["we_rate", "let_open_share", "note_that_rate", "sent_len_mean", "sent_len_sd",
                           "long_sent_share", "question_share", "paren_rate"]
        for f in higher_in_human:
            self.assertGreater(self.hu[f], self.ai[f], f)

    def test_specific_counters(self):
        s = pr.Sentence("The bound is not a proof, but a certificate, not a guess, rather than a hope.", 1, 0, 0)
        self.assertEqual(pr._count_contrast(s), 3)
        s = pr.Sentence("The sequence is strictly increasing and the bound is strictly sharper.", 1, 0, 0)
        self.assertEqual(len(pr.RX["intensifier"].findall(s.text)), 1)  # "strictly increasing" is math
        s = pr.Sentence("We use formal power series and a formally verified record.", 1, 0, 0)
        self.assertEqual(pr._count_status(s), 3)  # formally, verified, record; not "formal power series"
        s = pr.Sentence("Plectis organises source, evidence and exposition into a world.", 1, 0, 0)
        self.assertEqual(pr._count_triad(s), 1)
        s = pr.Sentence("Moreover, the sum converges, and the tail is small.", 1, 0, 0)
        self.assertEqual(pr._count_triad(s), 0)
        self.assertTrue(pr.RX["i"].search("Here I think the bound is sharp."))
        self.assertFalse(pr.RX["i"].search("In Part I we prove the bound."))

    def test_em_dash_and_tex_dashes(self):
        d = doc("\\begin{document}The tail---small as it is---decides it. Pages 3--5 are fine.\\end{document}", "tex")
        f = pr.compute_features(d)
        self.assertGreater(f["em_dash_rate"], 0)
        self.assertEqual(f["en_dash_rate"], 0)  # an unspaced range is not a dash

    def test_catalogue_sentences_excluded(self):
        cat = "Results: basis; independence; span equality; rank; dimension; count; index; residue."
        d = doc("\\begin{document}" + cat + " This is a real sentence of prose here.\\end{document}", "tex")
        self.assertEqual(d.catalogue, 1)
        self.assertEqual(len(d.sentences), 1)


class TestProfileAndCompare(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        base = self.tmp.name
        variants = [
            HUMAN_TEXT,
            HUMAN_TEXT.replace("We show", "We prove").replace("Fix such an $N$.", "Fix $N$ large."),
            HUMAN_TEXT + "\nWe note that the argument extends to Cantor series, with the obvious changes.\n",
            HUMAN_TEXT.replace("Is the same true", "One may ask whether the same is true").replace("? We", ". We"),
            HUMAN_TEXT + "\nLet $M$ be the moment. Then we have the bound (2.1), and so the claim follows.\n",
        ]
        self.corpus = []
        for i, t in enumerate(variants):
            p = os.path.join(base, "h%d.md" % i)
            _write(p, t * 3)
            self.corpus.append(p)
        self.ai = os.path.join(base, "ai.md")
        _write(self.ai, AI_TEXT * 3)
        self.mixed = os.path.join(base, "mixed.md")
        _write(self.mixed, AI_TEXT + HUMAN_TEXT * 2)
        self.held = os.path.join(base, "held.md")
        _write(self.held, (HUMAN_TEXT.replace("We show", "We establish")) * 3)
        self.prof = pr.build_profile(self.corpus, min_words=50, loo=True, name="test")

    def tearDown(self):
        self.tmp.cleanup()

    def test_profile_shape(self):
        self.assertEqual(len(self.prof["documents"]), 5)
        st = self.prof["features"]["we_rate"]
        self.assertTrue(st["q1"] <= st["median"] <= st["q3"])
        self.assertIn("loo_outside_rate", st)
        json.dumps(self.prof)

    def test_compare_ranks_ai_further_than_human(self):
        ai = pr.compare_one(self.ai, self.prof, None, 1.5, 3, 5)
        hu = pr.compare_one(self.held, self.prof, None, 1.5, 3, 5)
        self.assertGreater(ai["summary"]["mean_abs_d"], hu["summary"]["mean_abs_d"])
        self.assertGreater(ai["summary"]["outside"], hu["summary"]["outside"])
        self.assertLess(ai["features"]["we_rate"]["d"], 0)
        self.assertGreater(ai["features"]["contrast_rate"]["d"], 1.5)
        self.assertTrue(ai["specimens"])  # specimens are produced for the worst features

    def test_baseline_moves_toward(self):
        res = pr.compare_one(self.mixed, self.prof, self.ai, 1.5, 3, 5)
        self.assertTrue(res["features"]["contrast_rate"]["moved_toward"])
        self.assertTrue(res["features"]["we_rate"]["moved_toward"])
        moved = sum(1 for r in res["features"].values() if r.get("moved_toward"))
        self.assertGreater(moved, len(res["features"]) / 2)

    def test_cli_runs(self):
        out = os.path.join(self.tmp.name, "p.json")
        with contextlib.redirect_stdout(io.StringIO()):
            self._cli(out)

    def _cli(self, out):
        self.assertEqual(cli_main(["register", "profile"] + self.corpus + ["--out", out, "--min-words", "50"]), 0)
        self.assertEqual(cli_main(["register", "compare", "--profile", out, self.ai, "--baseline", self.mixed,
                                   "--format", "text"]), 0)
        self.assertEqual(cli_main(["register", "compare", "--profile", out, "--format", "matrix", self.ai, self.held]), 0)
        self.assertEqual(cli_main(["register", "specimens"] + self.corpus + ["--feature", "let_open_share",
                                                                             "--limit", "3"]), 0)
        self.assertEqual(cli_main(["register", "specimens"] + self.corpus + ["--feature", "section_opening"]), 0)

    def test_human_specimens_are_short_and_located(self):
        d = pr.load_document(self.corpus[0])
        sp = pr.human_specimens(d, "let_open_share")
        self.assertTrue(sp)
        with open(self.corpus[0], encoding="utf-8") as fh:
            raw = fh.read().split("\n")
        for s in sp:
            self.assertTrue(s.text.split()[0] in ("Let", "Suppose", "Fix", "Assume", "Consider"))
            self.assertTrue(1 <= s.line <= len(raw))



class TestMarkdownLayoutStripping(unittest.TestCase):
    """Reference links, HTML layout tags, reference definitions and raw TeX figures are not prose."""

    def test_layout_is_removed_and_link_text_kept(self):
        raw = (
            "# A title\n\n"
            "<a id=\"intro\"></a>\n\n"
            "We use the [Sherrington Kirkpatrick model][SK] and a [relative link](../long/record.md#x) here.\n"
            "The <span class=\"pdf\">companion section</span> gives the proof of every lemma in order.\n\n"
            "\\begin{figure}\n\\begin{tikzpicture}\\draw (0,0) -- (1,1);\\end{tikzpicture}\n\\end{figure}\n\n"
            "[SK]: https://example.org/sk\n"
        )
        doc = pr.document_from_text(raw, "x.md")
        text = " ".join(s.text for s in doc.sentences)
        self.assertIn("We use the Sherrington Kirkpatrick model and a relative link here.", text)
        self.assertIn("The companion section gives the proof", text)
        for bad in ("<a", "span", "tikzpicture", "draw", "https://", "[SK]", "a id"):
            self.assertNotIn(bad, text)

    def test_apparatus_feature_counts_hashes_code_and_commands(self):
        s = pr.Sentence("The build at commit 3f2a9c1b7d4e passed after `lake build` from https://example.org/x.", 1, 0, 0)
        self.assertGreaterEqual(len(pr.RX["apparatus"].findall(s.text)), 2)
        clean = pr.Sentence("We prove that the series is irrational for every integer base at least two.", 1, 0, 0)
        self.assertEqual(len(pr.RX["apparatus"].findall(clean.text)), 0)


class TestPackagedRules(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = pr.load_rules()

    def test_rules_validate(self):
        counts = pr.validate_rules(self.data)
        self.assertGreaterEqual(counts["rules"], 20)
        self.assertGreaterEqual(counts["by_status"]["adopted"], 5)

    def test_every_rule_is_a_method_entry(self):
        for rule in self.data["rules"]:
            for key in ("id", "title", "failure", "rule", "limit", "scopes", "status", "provenance",
                        "domain_test", "instances"):
                self.assertIn(key, rule, rule["id"])
            self.assertEqual(set(rule["domain_test"]), {"number_theory", "probability", "computer_science"})
            for spec in rule["specimens"]:
                self.assertLessEqual(len(spec["quote"].split()), pr.MAX_SPECIMEN_WORDS)

    def test_operator_directives_are_adopted(self):
        rules = {r["id"]: r for r in self.data["rules"]}
        adopted = {rid for rid, r in rules.items() if r["status"] == "adopted"}
        verification = [r for r in rules.values() if r["title"].startswith("Formal verification is one ordinary paragraph")]
        self.assertEqual(len(verification), 1)
        self.assertIn(verification[0]["id"], adopted)
        self.assertEqual(verification[0]["scopes"], ["short", "expository"])
        dashes = [r for r in rules.values() if "em dash" in r["title"].lower()]
        self.assertTrue(dashes and dashes[0]["id"] in adopted)
        self.assertTrue(any("line edit" in r["title"] for r in rules.values() if r["id"] in adopted))

    def test_history_records_every_local_rule(self):
        absorbed = [rid for row in self.data["history"] for rid in row.get("absorbs", [])]
        instances = {i["from"] for r in self.data["rules"] for i in r["instances"]}
        self.assertEqual(set(absorbed), {i for i in instances if i.startswith("REG-")})
        self.assertGreaterEqual(len(set(absorbed)), 200)

    def test_rules_select_and_render_by_scope(self):
        short = pr.select_rules(self.data, "short")
        long = pr.select_rules(self.data, "long")
        self.assertNotEqual({r["id"] for r in short}, {r["id"] for r in long})
        text = pr.render_rules(short)
        self.assertNotIn("\u2014", text.split("\n", 4)[-1].split("## ")[0])
        self.assertIn("*Limit.*", text)

    def test_validation_rejects_bad_rules(self):
        base = {"id": "X-1", "title": "t", "status": "candidate", "scopes": ["short"], "rule": "r",
                "limit": "l", "provenance": "p", "specimens": []}
        cases = [
            dict(base, specimens=[{"quote": " ".join(["word"] * 30), "source": "s"}]),
            dict(base, rule="A rule \u2014 with a dash"),
            dict(base, provenance="see /Users/someone/notes"),
            dict(base, scopes=["systems"]),
            dict(base, detector={"features": ["no_such_feature"]}),
        ]
        for rule in cases:
            with self.assertRaises(ValueError):
                pr.validate_rules({"rules": [rule], "history": []})

    def test_compare_names_rules_for_features(self):
        index = pr.rules_by_feature(self.data)
        self.assertIn("em_dash_rate", index)
        self.assertIn("status_vocab_rate", index)


class TestRegisterCli(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = self.tmp.name
        self.lit = []
        for k in range(5):
            d = os.path.join(root, "lit", "paper%d" % k)
            os.makedirs(d)
            with open(os.path.join(d, "extracted.md"), "w", encoding="utf-8") as fh:
                fh.write("# Introduction\n\n" + HUMAN_TEXT * (2 + k))
            self.lit.append(d)
        self.draft = os.path.join(root, "draft.md")
        with open(self.draft, "w", encoding="utf-8") as fh:
            fh.write("# Draft\n\n" + AI_TEXT * 3)

    def tearDown(self):
        self.tmp.cleanup()

    def run_cli(self, argv):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(io.StringIO()):
            code = cli_main(argv)
        return code, buf.getvalue()

    def test_rules_command(self):
        code, out = self.run_cli(["register", "rules", "--scope", "short"])
        self.assertEqual(code, 0)
        self.assertGreater(len(json.loads(out)["selected"]), 10)
        code, out = self.run_cli(["register", "rules", "--scope", "long", "--format", "markdown"])
        self.assertEqual(code, 0)
        self.assertTrue(out.startswith("# Register rules"))

    def test_compare_text_names_rules(self):
        profile = os.path.join(self.tmp.name, "profile.json")
        self.assertEqual(self.run_cli(["register", "profile"] + self.lit + ["--out", profile, "--min-words", "50"])[0], 0)
        code, out = self.run_cli(["register", "compare", "--profile", profile, "--format", "text", self.draft])
        self.assertEqual(code, 0)
        self.assertIn("outside the literature range", out)
        self.assertRegex(out, r"\[RG-\d\d")
        self.assertEqual(self.run_cli(["register", "profile"] + self.lit + ["--out", profile])[0], 1)

    def test_packet_inputs(self):
        out = os.path.join(self.tmp.name, "packet")
        code, report = self.run_cli(["register", "packet", "--draft", "short", self.draft, "--literature"] + self.lit +
                                    ["--out", out, "--title", "Round 1", "--min-words", "50"])
        self.assertEqual(code, 0, report)
        for name in ("request.md", "register/register_rules.json", "register/REGISTER_RULES.md",
                     "register/profile.json", "register/measurement.json", "register/measurement.txt"):
            self.assertTrue(os.path.isfile(os.path.join(out, name)), name)
        with open(os.path.join(out, "request.md"), encoding="utf-8") as fh:
            request = fh.read()
        self.assertIn("# Round 1", request)
        self.assertNotIn("{job}", request)
        first = request.index("Sentence- and paragraph-level writing")
        self.assertLess(first, request.index("Evidence presentation"))
        for name in ("register/measurement.json", "register/profile.json", "register/measurement.txt"):
            with open(os.path.join(out, name), encoding="utf-8") as fh:
                self.assertNotIn(self.tmp.name, fh.read(), name)
        code, _ = self.run_cli(["register", "packet", "--draft", "short", self.draft, "--literature"] + self.lit +
                               ["--out", out, "--title", "Round 1", "--min-words", "50"])
        self.assertEqual(code, 1)


class TestNormalPaperTemplates(unittest.TestCase):
    def read(self, stage):
        from importlib.resources import files
        return files("lean_exposition").joinpath("resources/templates/%s.md" % stage).read_text(encoding="utf-8")

    def headings(self, stage):
        return [line[3:] for line in self.read(stage).splitlines() if line.startswith("## ")]

    def test_short_paper_has_the_normal_shape(self):
        h = self.headings("short")
        self.assertEqual(h[0], "Abstract")
        self.assertIn("Formal verification", h)
        self.assertEqual(h[-2:], ["Acknowledgements", "References"])
        self.assertNotIn("Verification record", h)

    def test_long_record_keeps_apparatus_in_an_appendix(self):
        h = self.headings("long")
        refs = h.index("References")
        self.assertTrue(all(x.startswith("Appendix") for x in h[refs + 1:]))
        self.assertTrue(any("formal sources" in x for x in h[refs + 1:]))

    def test_templates_stay_empty_scaffolds_without_dashes(self):
        for stage in ("short", "expository", "long"):
            text = self.read(stage)
            self.assertIn("EMPTY SCAFFOLD", text)
            self.assertNotIn("\u2014", text)


class TestLiteratureProbes(unittest.TestCase):
    def test_clean_specimen_rejects_extraction_damage(self):
        good = "We do not know how to solve the original question implied by the problem."
        self.assertTrue(pr.clean_specimen(good))
        for bad in ("Huang showed that MATH has eigenvalues equal to one.",
                    "The question was formulated by Erdos and Graham in and posed again later .",
                    "The following lemma allows us to redu e an n-variate polynomial to one.",
                    "We show that there exists a lacunary",
                    "We use induction on m and the base case m = 1 is trivial here."):
            self.assertFalse(pr.clean_specimen(bad), bad)

    def test_packaged_specimens_are_clean(self):
        for rule in pr.load_rules()["rules"]:
            for spec in rule["specimens"]:
                self.assertNotRegex(spec["quote"], r"\b(?:MATH|REF|CODE)\b|\s[.,;:)]")
                self.assertNotIn("extracted", spec.get("locator", ""))
            if not rule["specimens"]:
                self.assertIn("specimens_note", rule)
            self.assertIn("probe", rule)

    def test_probe_rule_finds_moves_and_locates_them(self):
        with tempfile.TemporaryDirectory() as tmp:
            d = os.path.join(tmp, "paper")
            os.makedirs(d)
            with open(os.path.join(d, "extracted.md"), "w", encoding="utf-8") as fh:
                fh.write("# Introduction\n\nThe present paper is organized as follows in four short sections.\n\n"
                         "# Open questions\n\nWe do not know how to remove the growth hypothesis from the theorem.\n")
            cites = {"paper": "Author (2020), A paper"}
            rule = {"probe": {"kind": "regex", "pattern": r"\bwe do not know\b"}}
            res = pr.probe_rule(rule, [d], cites)
            self.assertTrue(res["holds"])
            self.assertEqual(res["specimens"][0]["source"], "Author (2020), A paper")
            self.assertEqual(res["specimens"][0]["locator"], "section “Open questions”")
            self.assertFalse(pr.probe_rule({"probe": {"kind": "regex", "pattern": "nonexistent move"}}, [d], cites)["holds"])
            self.assertTrue(pr.probe_rule({"probe": {"kind": "process"}}, [d], cites)["holds"])
            self.assertEqual(pr.probe_rule(rule, [d], cites, exclude=["We do not know"])["specimens"], [])

    def test_maintenance_script_validates(self):
        import subprocess
        root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        out = subprocess.run([sys.executable, os.path.join(root, "scripts", "register_rules.py"), "validate"],
                             capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertIn("RG-01", out.stdout)
