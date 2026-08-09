import subprocess
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEDGER = (
    "lean/TwistedYetter/Kirby/Final/Semantics/Independent/"
    "semantic-review-ledger-v1.json"
)


class SemanticReviewLedgerTest(unittest.TestCase):
    def test_final_theorem_semantic_review_snapshot_is_current(self) -> None:
        result = subprocess.run(
            [
                sys.executable,
                "scripts/lean_semantic_review_ledger.py",
                "check",
                "--ledger",
                LEDGER,
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
