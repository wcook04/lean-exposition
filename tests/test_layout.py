"""Exercise candidate layout checks against independent disposable Git trees."""
from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("layout_check", ROOT / "scripts/check_layout.py")
LAYOUT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LAYOUT)
POLICY = json.loads((ROOT / "docs/repository_layout.json").read_text())


@unittest.skipUnless(shutil.which("git"), "Git is needed for candidate-tree tests")
class LayoutTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="lean-exposition-layout-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "-q")
        for path in POLICY["required_paths"]:
            self.write(path, "Fixture file\n")
        self.write("docs/repository_layout.json", json.dumps(POLICY))
        self.readme = "# Fixture\n\n" + "\n".join(
            f"- [{target}]({target})" for target in POLICY["readme_map"]
        ) + "\n"
        self.write("README.md", self.readme)
        self.write("AGENTS.md", "\n".join(POLICY["entry_references"]) + "\n")
        self.write("pyproject.toml", '[project.scripts]\nlean-exposition = "lean_exposition.cli:main"\n'
                   '[tool.setuptools.package-data]\nlean_exposition = ["resources/**/*"]\n')
        self.write(".github/workflows/ci.yml", "name: fixture\n")
        self.write(".gitignore", "/build/\n/dist/\n__pycache__/\n")
        self.git("add", ".")

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.root), *args], capture_output=True, check=True)

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def assert_valid(self, *, index=False):
        report = LAYOUT.check(self.root, index=index)
        self.assertTrue(report["ok"], report["errors"])
        return report

    def assert_error(self, phrase, *, index=False):
        report = LAYOUT.check(self.root, index=index)
        self.assertFalse(report["ok"])
        self.assertTrue(any(phrase in item for item in report["errors"]), report["errors"])

    def test_valid_working_and_index_tree(self):
        self.assert_valid()
        self.assert_valid(index=True)

    def test_untracked_candidates_are_checked(self):
        self.write("scratch.py", "print('misplaced')\n")
        self.assert_error("unrecognized root file: scratch.py")
        self.assert_valid(index=True)

    def test_admitted_role_accepts_untracked_document(self):
        before = self.assert_valid()["files"]
        self.write("docs/new-guide.md", "A guide\n")
        self.assertEqual(self.assert_valid()["files"], before + 1)

    def test_new_top_level_family_requires_role(self):
        self.write("notes/example.md", "A new family\n")
        self.assert_error("undeclared top-level directory: notes")
        policy = copy.deepcopy(POLICY)
        policy["directory_roles"]["notes"] = "Worked development notes"
        self.write("docs/repository_layout.json", json.dumps(policy))
        self.assert_valid()

    def test_ignored_build_files_are_not_candidates(self):
        before = self.assert_valid()["files"]
        self.write("build/generated.py", "Generated output\n")
        self.write("dist/artefact.whl", "Not a real wheel\n")
        self.write("src/lean_exposition/__pycache__/cache.pyc", "Cache\n")
        self.assertEqual(self.assert_valid()["files"], before)

    def test_tracked_ignored_output_is_still_checked(self):
        self.write("build/generated.py", "Generated output\n")
        self.git("add", "-f", "build/generated.py")
        self.assert_error("undeclared top-level directory: build", index=True)

    def test_index_reads_staged_readme_even_when_working_is_repaired(self):
        self.write("README.md", "# No repository map\n")
        self.git("add", "README.md")
        self.write("README.md", self.readme)
        self.assert_valid()
        self.assert_error("README map is missing", index=True)

    def test_index_reads_staged_policy_even_when_working_is_repaired(self):
        self.write("docs/repository_layout.json", "{bad JSON")
        self.git("add", "docs/repository_layout.json")
        self.write("docs/repository_layout.json", json.dumps(POLICY))
        self.assert_valid()
        self.assert_error("invalid layout policy", index=True)

    def test_staged_required_deletion_is_detected(self):
        self.git("rm", "-f", "README.md")
        self.assert_error("missing required path: README.md", index=True)

    def test_unstaged_deletion_does_not_change_index_inspection(self):
        (self.root / "src/lean_exposition/resources/templates/short.md").unlink()
        self.assert_error("missing or nonregular working file")
        self.assert_valid(index=True)

    def test_staged_optional_deletion_is_not_a_candidate(self):
        self.write("docs/temporary.md", "Optional\n")
        self.git("add", "docs/temporary.md")
        self.git("rm", "-f", "docs/temporary.md")
        self.assert_valid(index=True)

    def test_stale_readme_link_is_detected(self):
        self.write("README.md", self.readme + "\n[Missing](docs/missing.md)\n")
        self.assert_error("README link has no candidate destination")

    def test_map_accepts_leading_dot_and_optional_trailing_slash(self):
        self.write("README.md", "# Fixture\n" + "\n".join(
            f"- [Directory](./{target.rstrip('/')})" for target in POLICY["readme_map"]
        ))
        self.assert_valid()

    def test_malformed_readme_url_fails_clearly(self):
        self.write("README.md", self.readme + "\n[Invalid](https://[invalid)\n")
        self.assert_error("malformed README link")

    def test_staged_entry_and_package_contents_are_inspected(self):
        self.write("AGENTS.md", "Read from memory\n")
        self.write("pyproject.toml", '[project.scripts]\nlean-exposition = "wrong:main"\n')
        self.git("add", "AGENTS.md", "pyproject.toml")
        self.assert_error("AGENTS.md is missing its entry reference", index=True)
        self.assert_error("pyproject.toml must expose", index=True)
        self.assert_error("packaged resource has no package-data pattern", index=True)

    def test_git_names_with_tabs_and_spaces_are_not_split(self):
        self.write("docs/with space\tand tab.md", "Unusual Git path\n")
        self.git("add", "docs/with space\tand tab.md")
        self.assert_valid(index=True)

    def test_symlink_is_not_accepted_as_a_regular_file(self):
        try:
            (self.root / "docs/link.md").symlink_to("../README.md")
        except OSError:
            self.skipTest("symlink creation is unavailable")
        self.git("add", "docs/link.md")
        self.assert_error("not a regular Git file", index=True)

    def test_working_symlink_ancestor_cannot_supply_policy_bytes(self):
        with tempfile.TemporaryDirectory(prefix="lean-exposition-external-") as raw:
            destination = Path(raw) / "docs"
            shutil.move(str(self.root / "docs"), destination)
            try:
                (self.root / "docs").symlink_to(destination, target_is_directory=True)
            except OSError:
                self.skipTest("symlink creation is unavailable")
            self.assert_error("not a regular candidate file")
            self.assert_valid(index=True)

    def test_missing_policy_fails_clearly(self):
        self.git("rm", "-f", "docs/repository_layout.json")
        self.assert_error("missing candidate file: docs/repository_layout.json", index=True)

    def test_non_git_root_fails_clearly(self):
        with tempfile.TemporaryDirectory(prefix="lean-exposition-non-git-") as raw:
            report = LAYOUT.check(Path(raw))
        self.assertFalse(report["ok"])
        self.assertIn("Git inspection failed", report["errors"][0])


if __name__ == "__main__":
    unittest.main()
