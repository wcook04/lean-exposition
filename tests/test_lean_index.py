"""The source-text Lean index against the vendored proof and hostile syntax."""
import json
import tempfile
import time
import unittest
from pathlib import Path

from lean_exposition import lean_index
from lean_exposition.cli import main
from lean_exposition.contracts import ContractError

ROOT = Path(__file__).resolve().parents[1]
TREE = ROOT / "examples/qaoa-sk/upstream/lean"


def parsed(source, module="Test"):
    return {row["name"]: row for row in lean_index.parse_module(source, module)["declarations"]}


def indexed(*sources):
    """Index files written as (relative path, source); returns declarations by name."""
    with tempfile.TemporaryDirectory() as directory:
        tree = Path(directory)
        for relative, source in sources:
            target = tree / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(source, encoding="utf-8")
        index = lean_index.build_index(tree)
    return {row["name"]: row for module in index["modules"] for row in module["declarations"]}


class RealCorpus(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        started = time.monotonic()
        cls.index = lean_index.build_index(TREE)
        cls.seconds = time.monotonic() - started
        cls.rows = {}
        for module in cls.index["modules"]:
            for row in module["declarations"]:
                cls.rows.setdefault(row["name"], (module, row))

    def test_stays_fast_and_covers_every_module(self):
        self.assertLess(self.seconds, 15)
        files = [*TREE.glob("OAI/**/*.lean"), *TREE.glob("ComparatorChallenges/**/*.lean")]
        self.assertEqual(len(self.index["modules"]), len(files))
        self.assertTrue(all(module["declarations"] for module in self.index["modules"]))

    def test_declaration_counts_agree_with_the_source_lines(self):
        counts = lean_index.counts(self.index)
        self.assertEqual((counts["theorem"], counts["lemma"], counts["structure"], counts["inductive"]),
                         (160, 2381, 44, 1))
        self.assertEqual(counts["def"] - counts["members"], 547)

    def test_full_support_location_and_dependency(self):
        module, row = self.rows["OAI.ZeroTemperatureSK.full_support"]
        self.assertEqual(module["path"], "OAI/Probability/SKSupport/Main.lean")
        self.assertEqual((row["line"], row["signature_end_line"], row["end_line"]), (35, 36, 59))
        self.assertIn("OAI.ZeroTemperatureSK.minimizer_full_support_actual", row["uses"])
        self.assertNotIn(row["name"], row["uses"])
        used = self.rows["OAI.ZeroTemperatureSK.minimizer_full_support_actual"][1]
        self.assertIn(row["name"], used["used_by"])
        self.assertEqual(row["dependency_source"], "source_text")

    def test_pins_revision_toolchain_and_line_links(self):
        self.assertEqual(self.index["dependency_source"], "source_text")
        self.assertEqual(self.index["toolchain"], (TREE / "lean-toolchain").read_text().strip())
        lock = json.loads((ROOT / "examples/qaoa-sk/source-lock.json").read_text())
        self.assertEqual(self.index["revision"], lock["revision"])
        self.assertEqual(self.index["base_url"], f"https://github.com/openai/math/blob/{lock['revision']}/lean/")

    def test_structure_fields_are_declarations_of_their_structure(self):
        row = self.rows["OAI.ZeroTemperatureSK.OrderParameter.monotone"][1]
        self.assertEqual((row["kind"], row["parent"]), ("def", "OAI.ZeroTemperatureSK.OrderParameter"))
        self.assertEqual(row["line"], 20)

    def test_a_copied_name_resolves_inside_its_own_import_closure(self):
        for module, row in self.rows.values():
            if module["name"].startswith("OAI"):
                continue
            for name in row["uses"]:
                self.assertEqual(row.get("uses_modules", {}).get(name, module["name"])[:3], "Com")

    def test_every_use_is_an_indexed_name(self):
        for module in self.index["modules"]:
            for row in module["declarations"]:
                for name in row["uses"]:
                    self.assertIn(name, self.rows)

    def test_views_split_source_from_lookup(self):
        modules = lean_index.modules_view(self.index)
        self.assertNotIn("source", json.dumps(modules["folders"][0]))
        self.assertEqual(sum(len(f["modules"]) for f in modules["folders"]), 349)
        names = lean_index.names_view(self.index)
        self.assertEqual(len(names["names"]), modules["counts"]["declarations"])
        name, kind, number, line, end = next(r for r in names["names"] if r[0].endswith(".full_support"))
        one = lean_index.module_view(self.index, names["modules"][number])
        self.assertEqual((kind, line, end), ("theorem", 35, 59))
        self.assertIn("theorem full_support", one["source"])
        self.assertIsNone(lean_index.module_view(self.index, "OAI.Absent"))

    def test_index_is_deterministic(self):
        again = lean_index.build_index(TREE)
        self.assertEqual(lean_index.canonical(again), lean_index.canonical(self.index))


class HostileSyntax(unittest.TestCase):
    def test_nested_comments_strings_and_chars_hide_keywords(self):
        rows = parsed('''/- outer /- theorem hidden₁ : True := trivial -/ still -/
def s := "theorem hidden₂ -- \\" /- "
def c := '"'
-- theorem hidden₃ : True := trivial
def r := r#"theorem hidden₄ "quoted" "#
def i := s!"a {"theorem hidden₅"} b"
theorem shown : True := trivial
''')
        self.assertEqual(sorted(rows), ["c", "i", "r", "s", "shown"])

    def test_docstring_attribute_and_flags(self):
        row = parsed('''/-- Says
hello. -/
@[simp, foo bar]
private noncomputable def a.b : Nat := 1
protected theorem c : True := trivial
''')
        self.assertEqual(row["a.b"]["doc"], "Says\nhello.")
        self.assertEqual(row["a.b"]["line"], 3)
        self.assertTrue(row["a.b"]["private"] and row["a.b"]["noncomputable"])
        self.assertEqual(row["a.b"]["namespace"], "a")
        self.assertTrue(row["c"]["protected"])

    def test_namespace_section_and_partial_end(self):
        rows = parsed('''namespace A.B
section
variable (x : Nat)
def one := x
end
end B
def two := 1
namespace C
def three := 1
end C
end A
def four := 1
theorem _root_.Other.five : True := trivial
''')
        self.assertEqual(sorted(rows), ["A.B.one", "A.C.three", "A.two", "Other.five", "four"])

    def test_prefix_commands_keep_the_declaration_they_introduce(self):
        rows = indexed(("OAI/M.lean", '''namespace Lib
def helper := 1
end Lib
set_option maxHeartbeats 0 in
open Lib in
/-- documented -/
theorem uses_it : helper = helper := rfl
def not_open := helper
'''))
        self.assertEqual(rows["uses_it"]["doc"], "documented")
        self.assertEqual(rows["uses_it"]["uses"], ["Lib.helper"])
        self.assertEqual(rows["not_open"]["uses"], [])

    def test_open_only_hiding_and_renaming(self):
        rows = indexed(("OAI/M.lean", '''namespace L
def a := 1
def b := 2
def c := 3
end L
open L (a)
def d := a + b
open L hiding c
def e := b + c
open L renaming c → z
def f := z
'''))
        self.assertEqual(rows["d"]["uses"], ["L.a"])
        self.assertEqual(rows["e"]["uses"], ["L.b"])
        self.assertEqual(rows["f"]["uses"], ["L.c"])

    def test_open_inside_a_proof_does_not_end_the_declaration(self):
        rows = parsed('''theorem a : True := by
  open Nat in
  set_option pp.all true in
  trivial
def b := 1
''')
        self.assertEqual(rows["a"]["end_line"], 4)

    def test_a_scope_after_a_modifier_is_still_a_command(self):
        rows = parsed("namespace A\ndef a := 1\nnoncomputable section\ndef b := 1\nend\nend A\ndef c := 1\n")
        self.assertEqual(sorted(rows), ["A.a", "A.b", "c"])

    def test_a_name_that_spells_a_command_inside_a_proof_keeps_the_proof_whole(self):
        rows = parsed("theorem a : True := by\n  have prefix := 1\n  exact prefix\ndef b := 1\n")
        self.assertEqual(rows["a"]["end_line"], 3)

    def test_signature_stops_at_the_body_and_absolute_values_do_not(self):
        rows = parsed('''theorem abs (x : Nat := 3) :
    |x| ≤ 1 := by
  simp
def alternatives : Nat → Nat
  | 0 => 1
  | n + 1 => n
structure S (a : Nat)
    extends T where
  x : Nat
''')
        self.assertEqual(rows["abs"]["signature_end_line"], 2)
        self.assertEqual(rows["alternatives"]["signature_end_line"], 4)
        self.assertEqual(rows["S"]["signature_end_line"], 8)

    def test_a_let_or_have_in_a_statement_keeps_its_own_assignment(self):
        rows = {row["short"]: row for row in lean_index.parse_module('''theorem let_statement (a : Nat) :
    let b := a + 1
    let c : Nat := b
    b = c := by
  rfl
lemma have_statement : have h : 1 = 1 := rfl
    h = h := by
  rfl
theorem bracketed : (let b := 1; b) = 1 := by
  rfl
def body : Nat := let b := 1; b
theorem in_the_proof : 1 = 1 := by
  let b := 1
  rfl
''', "M")["declarations"]}
        self.assertEqual({name: row["signature_end_line"] for name, row in rows.items()},
                         {"let_statement": 4, "have_statement": 7, "bracketed": 9, "body": 11, "in_the_proof": 12})

    def test_real_statements_with_a_let_end_at_their_own_assignment(self):
        index = lean_index.build_index(TREE)
        rows = {(module["name"].rsplit(".", 1)[1], row["short"]): (module, row) for module in index["modules"]
                for row in module["declarations"]}
        ends = {("FiniteDensity", "finite_density_coercivity"): 116, ("FiniteDensity", "finite_feedback_coercivity"): 180,
                ("ExpectedFeedbackStep", "finite_feedback_verification"): 158,
                ("VariableFeedbackEuler", "variableFeedback_controlledGrid"): 44, ("Coercivity", "rational_identity"): 44,
                ("Regularity", "cross_value_one_step"): 115, ("Verification", "value_bounded_drift_one_step"): 34,
                ("ForcedGenerator", "euler_one_step"): 42, ("TestGenerator", "euler_one_step"): 47,
                ("ThirdOrderRemainderBound", "gradient_euler_one_step"): 187,
                ("ProfileSplit", "diffusion_prefix_coercivity"): 72, ("SplitShape", "split_profile_coercivity"): 70,
                ("CrossExpectation", "cross_value_expectation_step"): 37,
                ("PredictableNormalizer", "euler_normalized_increment_properties"): 279,
                ("ForcedExpectation", "expectation_step"): 19, ("TestExpectation", "expectation_step"): 19,
                ("ValueEulerOneStep", "value_euler_one_step"): 48}
        self.assertEqual(len(ends), 17)
        for key, end in ends.items():
            with self.subTest(key=key):
                module, row = rows[key]
                self.assertEqual(row["signature_end_line"], end)
                self.assertTrue(module["source"].split("\n")[end - 1].rstrip().endswith(":= by"))

    def test_every_real_theorem_stops_at_its_own_assignment_or_where(self):
        for module in lean_index.build_index(TREE)["modules"]:
            source = module["source"].split("\n")
            for row in module["declarations"]:
                if row["kind"] in {"theorem", "lemma"}:
                    line = source[row["signature_end_line"] - 1]
                    self.assertTrue(":=" in line or line.rstrip().endswith("where"), row["name"])

    def test_structure_fields_in_each_form(self):
        rows = parsed('''structure S where
  mk ::
  /-- first -/
  a b : Nat
  (c : Nat)
  d : Nat := 1
  e (n : Nat) :
    Nat
  deriving Repr
class C (α : Type) := (f : α)
''')
        self.assertEqual({n for n in rows if n.startswith("S.")}, {"S.a", "S.b", "S.c", "S.d", "S.e"})
        self.assertEqual(rows["S.a"]["doc"], "first")
        self.assertIn("C.f", rows)

    def test_inductive_constructors(self):
        rows = parsed('''inductive T where
  | /-- one -/ a : T
  | b (x : Nat) : T
  deriving Repr
inductive U | c | d
''')
        self.assertTrue({"T.a", "T.b", "U.c", "U.d"} <= rows.keys())

    def test_where_auxiliary_and_instance_where(self):
        rows = indexed(("OAI/M.lean", '''def f := g 1
where
  g (x : Nat) := x
structure P where
  x : Nat
def p : P where
  x := 1
'''))
        self.assertIn("f.g", rows)
        self.assertIn("f.g", rows["f"]["uses"])
        self.assertNotIn("p.x", rows)

    def test_anonymous_instances_have_stable_distinct_names(self):
        first = parsed("namespace N\ninstance : A B := x\ninstance : A C := x\ninstance : A B := y\nend N\n")
        shifted = parsed("\n\n\nnamespace N\ninstance : A B := x\ninstance : A C := x\ninstance : A B := y\nend N\n")
        self.assertEqual(len(first), 3)
        self.assertEqual(sorted(first), sorted(shifted))
        self.assertTrue(all(row["synthetic"] for row in first.values()))
        named = parsed("instance (priority := 100) foo : A := x\n")
        self.assertEqual(list(named), ["foo"])

    def test_mutual_scope_and_forward_references(self):
        rows = indexed(("OAI/M.lean", '''mutual
  def even : Nat → Bool
    | 0 => true
    | n + 1 => odd n
  def odd : Nat → Bool
    | 0 => false
    | n + 1 => even n
end
def later := 1
def outside := later
'''))
        self.assertEqual(rows["even"]["uses"], ["odd"])
        self.assertEqual(rows["odd"]["uses"], ["even"])
        self.assertEqual(rows["outside"]["uses"], ["later"])

    def test_macros_notation_and_syntax_do_not_crash_or_invent_declarations(self):
        rows = parsed('''notation "theorem" x => x
local notation3 "(" a ")" => a
macro "foo" : tactic => `(tactic| simp)
macro_rules
  | `(bar) => `(command|
def fake := 1
)
syntax "baz" : term
infixl:65 " +++ " => HAdd.hAdd
#eval 1 + 1
def real := 1
''')
        self.assertEqual(list(rows), ["real"])

    def test_unterminated_text_does_not_crash(self):
        for source in ("def a := 1\n/- never closed", 'def a := "never closed', "def a := (1\n", "theorem"):
            lean_index.parse_module(source, "Test")

    def test_quoted_names_and_unicode_identifiers(self):
        rows = indexed(("OAI/M.lean", "def «two words» := 1\ndef β₁' := 2\ndef u := «two words» + β₁'\n"))
        self.assertEqual(rows["u"]["uses"], ["two words", "β₁'"])

    def test_locals_named_arguments_and_shadowing_are_not_uses(self):
        rows = indexed(("OAI/M.lean", '''def x := 1
def y := 2
def z := 3
def w := 4
def t (x : Nat) : Nat := x
def u : Nat := f (y := 2)
theorem v : True := by
  intro z
  have w := 1
  trivial
'''))
        self.assertEqual(rows["t"]["uses"], [])
        self.assertEqual(rows["u"]["uses"], [])
        self.assertEqual(rows["v"]["uses"], [])

    def test_field_notation_requires_a_unique_last_component(self):
        rows = indexed(("OAI/M.lean", '''structure A where
  unique_field : Nat
  shared : Nat
structure B where
  shared : Nat
def go (a : A) := a.unique_field
def no (a : A) := a.shared
def dot (a : A) : Nat := .unique_field a
'''))
        self.assertEqual(rows["go"]["uses"], ["A", "A.unique_field"])
        self.assertEqual(rows["no"]["uses"], ["A"])
        self.assertIn("A.unique_field", rows["dot"]["uses"])

    def test_private_names_stay_in_their_module_and_imports_bound_visibility(self):
        rows = indexed(("OAI/A.lean", "private def hidden := 1\ndef open_one := 1\n"),
                       ("OAI/B.lean", "import OAI.A\ndef b := hidden + open_one\n"),
                       ("OAI/C.lean", "def c := open_one\n"))
        self.assertEqual(rows["b"]["uses"], ["open_one"])
        self.assertEqual(rows["c"]["uses"], [])

    def test_protected_names_need_a_qualifier(self):
        rows = indexed(("OAI/M.lean", '''namespace N
protected def p := 1
def q := p
def r := N.p
end N
'''))
        self.assertEqual(rows["N.q"]["uses"], [])
        self.assertEqual(rows["N.r"]["uses"], ["N.p"])


class Extraction(unittest.TestCase):
    report = {"evidence_kind": "elaborated_expression_dependencies", "declarations": [
        {"name": "b", "type_dependencies": ["a"], "value_dependencies": ["c", "a._proof_1", "Nat.add", "b"],
         "structural_dependencies": [], "source": {"module": "OAI.M", "line": 2}},
        {"name": "_private.OAI.M.0.hidden", "value_dependencies": ["a"], "source": {"module": "OAI.M", "line": 4}},
        {"name": "b.match_1", "value_dependencies": ["a"], "source": {"module": "OAI.M", "line": 2}},
        {"name": "Mathlib.Thing", "value_dependencies": [], "source": {"module": "Mathlib"}}]}

    def build(self):
        with tempfile.TemporaryDirectory() as directory:
            tree = Path(directory)
            (tree / "OAI").mkdir()
            (tree / "OAI/M.lean").write_text("def a := 1\ndef b := a\ndef c := 1\nprivate def hidden := 1\ndef d := a\n")
            return lean_index.build_index(tree, extraction=[self.report])

    def test_elaborated_rows_replace_text_rows_only_where_covered(self):
        index = self.build()
        rows = {row["name"]: row for row in index["modules"][0]["declarations"]}
        self.assertEqual((rows["b"]["uses"], rows["b"]["dependency_source"]), (["a", "c"], "elaborated"))
        self.assertEqual(rows["hidden"]["dependency_source"], "elaborated")
        self.assertEqual((rows["d"]["uses"], rows["d"]["dependency_source"]), (["a"], "source_text"))
        self.assertIn("b", rows["c"]["used_by"])
        self.assertEqual(rows["a"]["used_by"], ["b", "d", "hidden"])
        self.assertEqual(index["dependency_source"], "source_text")
        self.assertEqual(index["extraction"]["elaborated_declarations"], 2)
        self.assertEqual(index["extraction"]["unmatched"], 1)

    def test_rejects_a_report_that_is_not_elaborated(self):
        with self.assertRaises(ContractError):
            lean_index.apply_extraction({"modules": []}, {"declarations": []})


class Command(unittest.TestCase):
    def test_cli_writes_one_file_or_split_views_and_refuses_to_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            tree = Path(directory) / "tree"
            (tree / "OAI").mkdir(parents=True)
            (tree / "OAI/M.lean").write_text("def a := 1\n")
            one, split = Path(directory) / "index.json", Path(directory) / "split"
            self.assertEqual(main(["lean-index", str(tree), "--out", str(one)]), 0)
            self.assertEqual(json.loads(one.read_text())["dependency_source"], "source_text")
            self.assertEqual(main(["lean-index", str(tree), "--out", str(split)]), 0)
            self.assertTrue((split / "module/OAI.M.json").is_file())
            self.assertEqual(lean_index.load_index(one)["modules"][0]["name"], "OAI.M")
            self.assertEqual(main(["lean-index", str(tree), "--out", str(one)]), 1)


if __name__ == "__main__":
    unittest.main()
