"""The private-source guard fails on a planted match and passes this repository."""
import subprocess
import sys
import unittest
from pathlib import Path

GUARD = Path(__file__).resolve().parents[1] / "scripts/private_guard.py"


class PrivateGuard(unittest.TestCase):
    def test_self_test_catches_planted_matches(self):
        result = subprocess.run([sys.executable, str(GUARD), "--self-test"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_tracked_files_are_clean(self):
        result = subprocess.run([sys.executable, str(GUARD), "--tracked"], capture_output=True, text=True,
                                cwd=GUARD.parents[1])
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
