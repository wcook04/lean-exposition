"""Optional comparison fields on alignment rows: fidelity, its source, and statement origin."""
import unittest

from lean_exposition import alignment


class ComparisonFields(unittest.TestCase):
    def check(self, item, keys):
        errors = []
        found = alignment._comparison(item, keys, "row", errors)
        return found, errors

    def test_absent_fields_add_nothing(self):
        self.assertEqual(self.check({"name": "x"}, alignment.FIDELITY_KEYS), ({}, []))

    def test_known_values_pass_through(self):
        row = {"fidelity": "stronger", "fidelity_source": "ai", "fidelity_note": "Every integer base."}
        self.assertEqual(self.check(row, alignment.FIDELITY_KEYS), (row, []))
        self.assertEqual(self.check({"origin": "evidence_record"}, {"origin"}), ({"origin": "evidence_record"}, []))

    def test_unknown_values_and_empty_notes_are_errors(self):
        for row in ({"fidelity": "equal"}, {"fidelity_source": "human"}, {"fidelity_note": "  "}):
            with self.subTest(row=row):
                self.assertTrue(self.check(row, alignment.FIDELITY_KEYS)[1])
        self.assertTrue(self.check({"origin": "guess"}, {"origin"})[1])


class TiesCarryComparison(unittest.TestCase):
    ROW = {"role": "statement", "lean_source": "statement", "anchor": "a", "at": "b0-1",
           "lean": [{"name": "X.y", "module": "X", "lines": [1, 2], "relation": "states",
                     "fidelity": "stronger", "fidelity_note": "Every base.", "fidelity_source": "ai"}]}

    def test_tie_copies_origin_and_first_lean_fidelity(self):
        tie = alignment._tie("r", {**self.ROW, "origin": "ai"})
        self.assertEqual((tie["origin"], tie["fidelity"], tie["fidelity_note"], tie["fidelity_source"]),
                         ("ai", "stronger", "Every base.", "ai"))

    def test_tie_without_fields_is_unchanged(self):
        row = {**self.ROW, "lean": [{k: v for k, v in self.ROW["lean"][0].items() if not k.startswith("fidelity")}]}
        tie = alignment._tie("r", row)
        self.assertFalse({"origin", "fidelity", "fidelity_note", "fidelity_source"} & tie.keys())


if __name__ == "__main__":
    unittest.main()
