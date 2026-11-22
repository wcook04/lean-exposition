"""Exercise the companion builder with reused output and the real static exporter."""
from __future__ import annotations

import json
import os
import shlex
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from lean_exposition.bundle import scaffold
from lean_exposition.contracts import write_json
from lean_exposition.lean_index import build_index
from test_adversarial import synthetic_artifact, synthetic_graph

ROOT = Path(__file__).resolve().parents[1]


class CompanionEditionCache(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        instance = self.root / "instances/example"
        paper = instance / "papers/extra"
        self.alignment = instance / "alignment"
        for directory in (paper, self.alignment, self.root / "site"):
            directory.mkdir(parents=True)
        (self.root / "site/scripts").symlink_to(ROOT / "site/scripts", target_is_directory=True)
        write_json(instance / "instance.json", {"goal": "goal", "documents": [{"slot": "extra", "kind": "companion"}]})
        graph = synthetic_graph()
        write_json(instance / "evidence-graph.json", graph)
        absent = self.root / "scaffold"
        scaffold(graph, absent)
        (instance / "papers/long").mkdir()
        for suffix in ("json", "md"):
            (instance / f"papers/long/absent.{suffix}").write_bytes(
                (absent / f"papers/long.{suffix}").read_bytes())
        mapping, content = synthetic_artifact(graph)
        mapping.update(stage="extra", path="papers/extra.md")
        self.mapping = paper / "correspondence.json"
        write_json(self.mapping, mapping)
        (paper / "paper.md").write_bytes(content)
        self.references = self.alignment / "references-extra.json"
        write_json(self.references, {"paper": "extra", "references": [], "sources": {}})
        write_json(self.alignment / "references-long.json", {"paper": "long", "references": [], "sources": {}})
        write_json(self.alignment / "phrases-extra.json", {
            "schema": "phrase-ties/1", "paper": "extra",
            "parts": [{"name": "Result", "lines": [1, 3],
                       "topics": [{"id": "claim", "name": "Claim"}],
                       "titles": {"claim": "The claim"}, "notes": {"claim": "A synthetic Lean declaration."}}],
            "ties": [{"id": "claim", "from": "A synthetic claim", "to": "A synthetic claim",
                      "role": "statement", "topic": "claim", "status": "new",
                      "lean": [{"name": "claim", "file": "Demo/Proof.lean", "relation": "states", "fidelity": "same"}]}],
        })
        self.colours = self.alignment / "colours-extra.json"
        self.lean = self.root / "lean"
        self.source = self.lean / "Demo/Proof.lean"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("theorem claim : True := True.intro\n")
        launcher = self.root / "lean-exposition"
        launcher.write_text(f'#!/bin/sh\nexec {shlex.quote(sys.executable)} -m lean_exposition.cli "$@"\n')
        launcher.chmod(0o755)
        self.env = {**os.environ, "PYTHONPATH": str(ROOT / "src"),
                    "PYTHON": sys.executable, "LEAN_EXPOSITION": str(launcher), "LX_ADAPTED": "0"}
        self.edition = self.root / "edition"
        self.index = self.edition / "docs/extra/index.json"

    def build(self, lean=None):
        result = subprocess.run(
            [sys.executable, ROOT / "scripts/build_companion_editions.py", "example",
             lean or self.lean, self.edition],
            cwd=self.root, env=self.env, capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout.strip()

    def response(self, route):
        index = json.loads(self.index.read_text())
        return json.loads((self.edition / index["responses"][route]).read_text())

    def test_reuses_unchanged_inputs_and_rebuilds_after_independent_changes(self):
        self.assertEqual(self.build(), "extra: ok")
        original = self.index.stat().st_mtime_ns
        os.utime(self.mapping, ns=(original + 1_000_000_000,) * 2)
        self.assertEqual(self.build(), "extra: current")
        self.assertEqual(self.index.stat().st_mtime_ns, original)

        def change_json(path, value):
            write_json(path, value)
            # Copying or restoring an input can preserve its old timestamp.
            os.utime(path, ns=(original - 1_000_000_000,) * 2)

        mapping = json.loads(self.mapping.read_text())
        mapping["passages"][0]["evidence_class"] = "context"
        change_json(self.mapping, mapping)
        self.assertEqual(self.build(), "extra: ok")
        structure = self.response("/papers/short/structure?representation=reader")
        self.assertEqual(structure["paper"]["passages"][0]["evidence_class"], "context")

        references = json.loads(self.references.read_text())
        change_json(self.references, {**references, "provenance": "Revised source table."})
        self.assertEqual(self.build(), "extra: ok")

        change_json(self.colours, {
            "schema": "topic-colours/1",
            "parts": [{"families": [], "topics": {"claim": {
                "index": 0, "family": "claim", "light": "#123456", "dark": "#abcdef"}}}],
        })
        self.assertEqual(self.build(), "extra: ok")
        self.assertEqual(self.response("/ties/short")["topics"][0]["light"], "#123456")
        self.colours.unlink()
        self.assertEqual(self.build(), "extra: ok")
        self.assertNotIn("light", self.response("/ties/short")["topics"][0])

        raw = self.source.read_text()
        self.source.write_text("\n" + raw)
        os.utime(self.source, ns=(original - 1_000_000_000,) * 2)
        self.assertEqual(self.build(), "extra: ok")
        self.assertEqual(self.response("/ties/short")["ties"][0]["rows"][0]["line"], 2)
        self.assertEqual(self.build(), "extra: current")

        index = self.root / "lean-index.json"
        write_json(index, build_index(self.lean))
        self.assertEqual(self.build(index), "extra: ok")
        self.assertEqual(self.build(index), "extra: current")
        self.source.write_text(raw)
        change_json(index, build_index(self.lean))
        self.assertEqual(self.build(index), "extra: ok")
        self.assertEqual(self.response("/ties/short")["ties"][0]["rows"][0]["line"], 1)
