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


class Round14ConformanceTests(unittest.TestCase):
    def test_irrelevant_unsupported_evidence_basis_is_still_unsupported(self):
        store, manifest = ctl_ref.build_case("genesis")
        state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        role_cid = manifest["objects"]["role"]
        claim = ctl_ref.revision(
            "claim:with-irrelevant-evidence",
            "claim",
            "ctl-data/opaque-json/1",
            {},
        )
        claim_cid = store.add(claim)
        transition = ctl_ref.batch(
            state["root_cid"],
            [claim_cid],
            [ctl_ref.set_op("claim:with-irrelevant-evidence", ctl_ref.absent(), claim_cid)],
            [role_cid],
            evidence=[
                {
                    "target": {"kind": "binding_op", "logical_id": "claim:with-irrelevant-evidence"},
                    "basis": "vendor/unknown/1",
                    "cid": role_cid,
                }
            ],
        )
        transition_cid = store.add(transition)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, transition_cid)),
            "unsupported",
        )


if __name__ == "__main__":
    unittest.main()
