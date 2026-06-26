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


class Round11ConformanceTests(unittest.TestCase):
    def genesis_state(self):
        store, manifest = ctl_ref.build_case("genesis")
        state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        return store, manifest, state

    def inactive_role_binding(self, store: ctl_ref.Store) -> str:
        role = ctl_ref.revision(
            "role-binding:inactive",
            "role-binding",
            "ctl-governance/role-binding/1",
            {
                "actor_id": "actor:jin",
                "role_id": "role:owner",
                "scope": {"project_id": "project:demo"},
            },
        )
        return store.add(role)

    def test_unsupported_recorded_profile_does_not_mask_inactive_principal_role(self):
        store, _manifest, state = self.genesis_state()
        inactive_role_cid = self.inactive_role_binding(store)
        unknown = ctl_ref.revision("claim:unknown", "claim", "vendor/profile/1", {})
        unknown_cid = store.add(unknown)
        batch = ctl_ref.batch(
            state["root_cid"],
            [inactive_role_cid, unknown_cid],
            [],
            [inactive_role_cid],
        )
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )

    def test_unsupported_evidence_basis_does_not_mask_inactive_principal_role(self):
        store, manifest, state = self.genesis_state()
        inactive_role_cid = self.inactive_role_binding(store)
        claim = ctl_ref.revision("claim:with-evidence", "claim", "ctl-data/opaque-json/1", {})
        claim_cid = store.add(claim)
        batch = ctl_ref.batch(
            state["root_cid"],
            [claim_cid, inactive_role_cid],
            [],
            [inactive_role_cid],
            evidence=[
                {
                    "target": {"kind": "recorded_revision", "cid": claim_cid},
                    "basis": "vendor/unknown/1",
                    "cid": manifest["objects"]["role"],
                }
            ],
        )
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )


if __name__ == "__main__":
    unittest.main()
