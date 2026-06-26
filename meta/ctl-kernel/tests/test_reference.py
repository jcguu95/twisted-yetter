from __future__ import annotations

import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "reference"))

import ctl_ref  # noqa: E402


class ReferenceTests(unittest.TestCase):
    def non_genesis_state(self):
        store, manifest = ctl_ref.build_case("non-genesis")
        genesis = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        child = ctl_ref.validate_transition(store, genesis, manifest["transition_batch"])
        trust = {
            "project_id": "project:demo",
            "kernel_profile": "ctl-kernel/1",
            "genesis_root_cid": manifest["objects"]["genesis_root"],
        }
        return store, manifest, child, trust

    def test_validate_chain_replays_to_target(self):
        store, _manifest, child, trust = self.non_genesis_state()
        replayed = ctl_ref.validate_chain(store, child["root_cid"], trust)
        self.assertEqual(replayed["root_cid"], child["root_cid"])
        self.assertEqual(ctl_ref.canonical_bytes(replayed["root"]), ctl_ref.canonical_bytes(child["root"]))

    def test_validate_chain_rejects_unknown_root_field_before_traversal(self):
        store, _manifest, child, trust = self.non_genesis_state()
        bad_root = dict(child["root"])
        bad_root["created_at"] = "2026-06-25T23:02:00Z"
        bad_root_cid = store.add(bad_root)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_chain(store, bad_root_cid, trust)

    def test_validate_chain_rejects_project_mismatch(self):
        store, _manifest, child, trust = self.non_genesis_state()
        trust = dict(trust)
        trust["project_id"] = "project:other"
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_chain(store, child["root_cid"], trust)

    def test_validate_chain_rejects_kernel_mismatch(self):
        store, _manifest, child, trust = self.non_genesis_state()
        trust = dict(trust)
        trust["kernel_profile"] = "ctl-kernel/2"
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_chain(store, child["root_cid"], trust)

    def test_validate_chain_requires_pinned_genesis(self):
        store, manifest, child, trust = self.non_genesis_state()
        trust = dict(trust)
        trust["genesis_root_cid"] = manifest["objects"]["policy"]
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_chain(store, child["root_cid"], trust)

    def test_new_round7_vectors_have_expected_results(self):
        for case in [
            "role-binding-slot-hijack-no-parent",
            "role-binding-non-fast-forward",
            "invalid-plus-unsupported",
            "genesis-evidence-plus-unsupported",
        ]:
            store, manifest = ctl_ref.build_case(case)
            try:
                state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
                if "transition_batch" in manifest:
                    ctl_ref.validate_transition(store, state, manifest["transition_batch"])
                result = "valid"
            except ctl_ref.UnsupportedProfile:
                result = "unsupported"
            except ctl_ref.InvalidHistory:
                result = "invalid"
            self.assertEqual(result, manifest["expect"], case)


if __name__ == "__main__":
    unittest.main()

