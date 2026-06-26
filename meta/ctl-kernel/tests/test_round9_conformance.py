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


class Round9ConformanceTests(unittest.TestCase):
    def genesis_state(self):
        store, manifest = ctl_ref.build_case("genesis")
        state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        return store, manifest, state

    def test_invalid_binding_target_dominates_unsupported_evidence_basis(self):
        store, manifest, state = self.genesis_state()
        role_cid = manifest["objects"]["role"]
        bad_op = ctl_ref.set_op("claim:not-recorded", ctl_ref.absent(), manifest["genesis_batch"])
        batch = ctl_ref.batch(
            state["root_cid"],
            [],
            [bad_op],
            [role_cid],
            evidence=[
                {
                    "target": {"kind": "binding_op", "logical_id": "claim:not-recorded"},
                    "basis": "vendor/unknown/1",
                    "cid": role_cid,
                }
            ],
        )
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )

    def test_bad_admitted_at_dominates_unsupported_recorded_profile(self):
        store, manifest, state = self.genesis_state()
        role_cid = manifest["objects"]["role"]
        unknown = ctl_ref.revision("claim:unknown", "claim", "vendor/profile/1", {})
        unknown_cid = store.add(unknown)
        batch = ctl_ref.batch(state["root_cid"], [unknown_cid], [], [role_cid])
        batch["admitted_at"] = "2026-99-99T99:99:99Z"
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )

    def test_principal_authentication_assurance_must_be_id(self):
        store, manifest = ctl_ref.build_case("genesis")
        batch = store.resolve(manifest["genesis_batch"])
        batch["principal_claim"]["authentication_assurance"] = "Local Operator"
        batch_cid = store.add(batch)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.derive_genesis(store, batch_cid)

    def test_malformed_policy_selector_returns_invalid_not_host_exception(self):
        store = ctl_ref.Store()
        policy = ctl_ref.revision(
            "sys:policy",
            "policy-set",
            "ctl-governance/policy-set/1",
            {
                "version": 1,
                "default": "deny",
                "rules": [
                    {
                        "effect": "allow",
                        "subject": {"role_id": "role:owner"},
                        "actions": ["revision.record"],
                        "resources": ["not-a-selector-object"],
                        "required_evidence_basis": [],
                    }
                ],
            },
        )
        policy_cid = store.add(policy)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_revision(store, policy_cid, policy)

    def test_supported_run_receipt_profile_has_minimal_structural_validation(self):
        store = ctl_ref.Store()
        receipt = ctl_ref.revision(
            "claim:receipt",
            "run-receipt",
            "agent/run-receipt/1",
            {
                "status": "ok",
                "command": ["uv", "run", "python", "-m", "unittest"],
                "started_at": "2026-06-25T23:00:00Z",
                "finished_at": "2026-06-25T23:00:01Z",
            },
        )
        receipt_cid = store.add(receipt)
        ctl_ref.validate_revision(store, receipt_cid, receipt)


if __name__ == "__main__":
    unittest.main()
