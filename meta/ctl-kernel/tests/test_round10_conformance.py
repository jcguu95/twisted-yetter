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


class Round10ConformanceTests(unittest.TestCase):
    def genesis_state(self):
        store, manifest = ctl_ref.build_case("genesis")
        state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        return store, manifest, state

    def test_unsupported_recorded_profile_does_not_mask_unrecorded_binding_target(self):
        store, manifest, state = self.genesis_state()
        role_cid = manifest["objects"]["role"]
        unknown = ctl_ref.revision("claim:unknown", "claim", "vendor/profile/1", {})
        unknown_cid = store.add(unknown)
        batch = ctl_ref.batch(
            state["root_cid"],
            [unknown_cid],
            [ctl_ref.set_op("claim:not-recorded", ctl_ref.absent(), manifest["genesis_batch"])],
            [role_cid],
        )
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )

    def test_unsupported_recorded_profile_does_not_mask_malformed_evidence(self):
        store, manifest, state = self.genesis_state()
        role_cid = manifest["objects"]["role"]
        unknown = ctl_ref.revision("claim:unknown", "claim", "vendor/profile/1", {})
        unknown_cid = store.add(unknown)
        batch = ctl_ref.batch(state["root_cid"], [unknown_cid], [], [role_cid])
        batch["evidence"] = "not-an-array"
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )

    def test_missing_transition_parent_root_returns_invalid_not_host_exception(self):
        store, manifest, state = self.genesis_state()
        role_cid = manifest["objects"]["role"]
        claim = ctl_ref.revision("claim:missing-parent-root", "claim", "ctl-data/opaque-json/1", {})
        claim_cid = store.add(claim)
        batch = ctl_ref.batch(
            state["root_cid"],
            [claim_cid],
            [ctl_ref.set_op("claim:missing-parent-root", ctl_ref.absent(), claim_cid)],
            [role_cid],
        )
        del batch["parent_root"]
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )

    def test_genesis_parent_root_invalidity_dominates_unsupported_recorded_profile(self):
        store, manifest = ctl_ref.build_case("genesis")
        unknown = ctl_ref.revision("claim:unknown", "claim", "vendor/profile/1", {})
        unknown_cid = store.add(unknown)
        batch = store.resolve(manifest["genesis_batch"])
        batch["parent_root"] = manifest["objects"]["policy"]
        batch["recorded_revisions"] = ctl_ref.sort_scalars(batch["recorded_revisions"] + [unknown_cid])
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.derive_genesis(store, batch_cid)),
            "invalid",
        )


if __name__ == "__main__":
    unittest.main()
