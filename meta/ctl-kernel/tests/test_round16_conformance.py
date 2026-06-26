from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "reference"))

import ctl_ref  # noqa: E402


def classify(fn):
    try:
        fn()
        return "valid"
    except ctl_ref.InvalidHistory:
        return "invalid"
    except ctl_ref.UnsupportedProfile:
        return "unsupported"
    except Exception as exc:
        return f"host:{type(exc).__name__}"


class Round16ConformanceTests(unittest.TestCase):
    def malformed_run_receipt_recording_is_invalid_not_host_exception(self, bad_status):
        store, manifest = ctl_ref.build_case("genesis")
        state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        role_cid = manifest["objects"]["role"]
        receipt = ctl_ref.revision(
            "run-receipt:bad",
            "run-receipt",
            "agent/run-receipt/1",
            {"status": bad_status},
        )
        receipt_cid = store.add(receipt)
        transition = ctl_ref.batch(
            state["root_cid"],
            [receipt_cid],
            [],
            [role_cid],
        )
        transition_cid = store.add(transition)
        return classify(lambda: ctl_ref.validate_transition(store, state, transition_cid))

    def test_run_receipt_status_array_is_invalid_not_host_exception(self):
        self.assertEqual(
            self.malformed_run_receipt_recording_is_invalid_not_host_exception([]),
            "invalid",
        )

    def test_run_receipt_status_object_is_invalid_not_host_exception(self):
        self.assertEqual(
            self.malformed_run_receipt_recording_is_invalid_not_host_exception({}),
            "invalid",
        )


if __name__ == "__main__":
    unittest.main()
