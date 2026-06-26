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


class Round15ConformanceTests(unittest.TestCase):
    def genesis_with_policy(self, policy_revision):
        store = ctl_ref.Store()
        role = ctl_ref.revision(
            "role-binding:operator",
            "role-binding",
            "ctl-governance/role-binding/1",
            {"actor_id": "actor:jin", "role_id": "role:owner", "scope": {"project_id": "project:demo"}},
        )
        policy_cid = store.add(policy_revision)
        role_cid = store.add(role)
        genesis = ctl_ref.batch(
            None,
            [policy_cid, role_cid],
            [
                ctl_ref.set_op("role-binding:operator", ctl_ref.absent(), role_cid),
                ctl_ref.set_op("sys:policy", ctl_ref.absent(), policy_cid),
            ],
            [],
        )
        genesis_cid = store.add(genesis)
        return store, genesis_cid

    def test_policy_version_true_is_invalid_not_valid(self):
        base_store, manifest = ctl_ref.build_case("genesis")
        policy = base_store.resolve(manifest["objects"]["policy"])
        policy["payload"]["version"] = True
        store, genesis_cid = self.genesis_with_policy(policy)
        self.assertEqual(classify(lambda: ctl_ref.derive_genesis(store, genesis_cid)), "invalid")

    def test_malformed_policy_action_entry_returns_invalid_not_host_exception(self):
        base_store, manifest = ctl_ref.build_case("genesis")
        policy = base_store.resolve(manifest["objects"]["policy"])
        policy["payload"]["rules"][0]["actions"] = [123]
        store, genesis_cid = self.genesis_with_policy(policy)
        self.assertEqual(classify(lambda: ctl_ref.derive_genesis(store, genesis_cid)), "invalid")

    def test_malformed_binding_op_kind_returns_invalid_not_host_exception(self):
        store, manifest = ctl_ref.build_case("non-genesis")
        genesis = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        transition = store.resolve(manifest["transition_batch"])
        transition["binding_ops"][0]["op"] = []
        transition_cid = store.add(transition)
        self.assertEqual(classify(lambda: ctl_ref.validate_transition(store, genesis, transition_cid)), "invalid")


if __name__ == "__main__":
    unittest.main()
