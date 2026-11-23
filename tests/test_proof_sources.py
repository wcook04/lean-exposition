"""The paper's inline Lean source uses pinned Git blobs and checked sidecars."""

from hashlib import sha256
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from lean_exposition.proof_sources import ProofSources


SOURCE = "import Tests.Dependency\nnamespace Foo\ntheorem first : True := by\n  trivial\ntheorem second : True := first\nend Foo\n"


class CompiledProof:
    def __init__(self, revision):
        self.manifest = {"revision": revision, "upstream": "https://example.test/lean",
                         "dataset": "https://example.test/compiled"}

    def references_among(self, names):
        return {"Foo.first": [], "Foo.second": ["Foo.first"]}

    def dependency_kinds(self, consumer, prerequisite):
        return ["value"] if (consumer, prerequisite) == ("Foo.second", "Foo.first") else []

    def direct_neighbourhood(self, name):
        if name == "Foo.second":
            return {
                "scope": "riemann_hypothesis_closure",
                "dependencies": [
                    {"name": "Tests.alias", "origin": "project", "kind": "def", "kinds": ["type"],
                     "file": "src/Tests.lean", "line": 1},
                ],
                "users": [],
            }
        return None


class ProofSourceFiles(unittest.TestCase):
    def setUp(self):
        folder = tempfile.TemporaryDirectory()
        self.addCleanup(folder.cleanup)
        self.repository = Path(folder.name) / "git"
        self.repository.mkdir()
        self.paper = Path(folder.name) / "paper"
        self.paper.mkdir()
        (self.repository / "src").mkdir()
        self.file = self.repository / "src/Foo.lean"
        self.file.write_text(SOURCE, encoding="utf-8")
        (self.repository / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n", encoding="utf-8")
        self.git("init", "-q")
        self.git("add", ".")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.test",
                 "commit", "--no-gpg-sign", "-qm", "Pinned source")
        self.revision = self.git("rev-parse", "HEAD")
        self.proof = CompiledProof(self.revision)
        fields = {"module": "Foo", "file": "src/Foo.lean", "kind": "theorem", "revision": self.revision, "in_proof": True}
        names = {
            "Foo.first": {"name": "Foo.first", "lines": [3, 4], "statement_lines": [3, 3], **fields},
            "Foo.second": {"name": "Foo.second", "lines": [5, 5], **fields},
        }
        pins = {"lean_revision": self.revision, "paper_revision": "paper-fixture"}
        files = {
            "lean-notes.json": {"bindings": {name: {"source": source} for name, source in names.items()}, **pins},
            "lean-lines.json": {"modules": {"Foo": [
                {"name": name, "lines": source["lines"], "canonical": f"st:{name}"} for name, source in names.items()
            ]}, **pins},
        }
        self.manifest = {"lean": {"revision": self.revision}, "paper": {"revision": "paper-fixture"},
                         "files": {name: self.write_json(name, item) for name, item in files.items()}}
        self.write_json("manifest.json", self.manifest)

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.repository), *args], text=True).strip()

    def write_json(self, name, value):
        raw = json.dumps(value).encode()
        (self.paper / name).write_bytes(raw)
        return sha256(raw).hexdigest()

    def test_pinned_module_payload_ignores_working_tree_edits(self):
        self.file.write_text("Edited worktree source\n", encoding="utf-8")
        sources = ProofSources(self.repository, self.paper, self.proof)
        module = sources.module("Foo")
        self.assertEqual(module["source"], SOURCE)
        self.assertEqual(module["imports"], ["Tests.Dependency"])
        self.assertEqual(module["sha256"], sha256(SOURCE.encode()).hexdigest())
        self.assertEqual(module["declarations"][0]["signature_end_line"], 3)
        self.assertEqual(module["declarations"][0]["used_by"], ["Foo.second"])
        self.assertEqual(module["declarations"][0]["proof_used_by"], ["Foo.second"])
        self.assertEqual(module["declarations"][1]["statement_uses"], [])
        self.assertEqual(module["declarations"][1]["proof_uses"], ["Foo.first"])
        self.assertNotIn("neighbourhood", module["declarations"][0])
        graph = module["declarations"][1]["neighbourhood"]
        self.assertEqual(graph["counts"], {"dependencies": 1, "users": 0})
        self.assertEqual(graph["dependencies"][0]["name"], "Tests.alias")
        self.assertEqual(graph["dependencies"][0]["kinds"], ["type"])
        self.assertEqual(graph["dependencies"][0]["href"],
                         f"https://example.test/lean/blob/{self.revision}/src/Tests.lean#L1-L1")
        self.assertEqual(module["paper_links"][0]["canonical"], "st:Foo.first")
        self.assertEqual(sources.names()["names"][0], ["Foo.first", "theorem", 0, 3, 4])
        metadata = sources.names()["declarations"][1]
        self.assertEqual(metadata["path"], "src/Foo.lean")
        self.assertEqual(metadata["signature_end_line"], 5)
        self.assertEqual(metadata["reference_kinds"], {"Foo.first": ["value"]})
        self.assertNotIn("source", metadata)
        self.assertNotIn("neighbourhood", metadata)
        self.assertEqual(sources.modules()["counts"]["modules"], 1)
        with self.assertRaises(KeyError):
            sources.module("Tests.Dependency")

    def test_rejects_a_changed_line_index(self):
        self.write_json("lean-lines.json", {})
        with self.assertRaisesRegex(ValueError, "does not match the RH paper manifest"):
            ProofSources(self.repository, self.paper, self.proof)

    def test_reader_titles_cover_the_catalogue_and_keep_lean_names(self):
        self.write_json("reader.json", {
            "revision": self.revision, "labels": {"Foo.first": ["The first theorem", "Tests"]},
        })
        config = self.paper / "reader.json"
        with self.assertRaisesRegex(ValueError, "Missing display title for Foo.second"):
            ProofSources(self.repository, self.paper, self.proof, reader_config=config)
        self.write_json("reader.json", {
            "revision": self.revision,
            "labels": {"Foo.first": ["The first theorem", "Tests"], "Foo.second": ["A second theorem", "Tests"],
                       "Tests.alias": ["The proposition", "Tests"]},
        })
        sources = ProofSources(self.repository, self.paper, self.proof, reader_config=config)
        self.assertEqual(sources.names()["declarations"][0]["display_title"], "The first theorem")
        declaration = sources.module("Foo")["declarations"][1]
        self.assertEqual(declaration["display_title"], "A second theorem")
        self.assertEqual(declaration["name"], "Foo.second")
        self.assertEqual(declaration["neighbourhood"]["dependencies"][0]["display_title"], "The proposition")

    def test_rejects_a_different_paper_revision_of_lean(self):
        self.manifest["lean"]["revision"] = "0" * 40
        self.write_json("manifest.json", self.manifest)
        with self.assertRaisesRegex(ValueError, "different Lean revisions"):
            ProofSources(self.repository, self.paper, self.proof)

    def test_lean_checks_are_bound_to_the_edition_and_each_declaration(self):
        graph = {
            "Foo.first": {"axioms": [], "href": "https://example.test/release"},
            "Foo.second": {"axioms": ["propext"], "href": "https://example.test/release"},
        }
        checks = {"schema": "rh-lean-checks/1", "paper_revision": "paper-fixture", "lean_revision": self.revision,
                  "graph": graph, "archive": {}}

        def bind():
            self.manifest["files"]["lean-checks.json"] = self.write_json("lean-checks.json", checks)
            self.write_json("manifest.json", self.manifest)

        bind()
        sources = ProofSources(self.repository, self.paper, self.proof)
        first, second = sources.module("Foo")["declarations"]
        self.assertEqual(first["graph_axioms"], graph["Foo.first"])
        self.assertEqual(second["graph_axioms"], graph["Foo.second"])
        self.assertNotIn("archive_check", first)
        self.assertEqual(sources.names()["declarations"][1]["graph_axioms"], graph["Foo.second"])
        checks["lean_revision"] = "0" * 40
        bind()
        with self.assertRaisesRegex(ValueError, "Lean checks use a different edition"):
            ProofSources(self.repository, self.paper, self.proof)
