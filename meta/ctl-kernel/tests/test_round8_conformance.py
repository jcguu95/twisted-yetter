from __future__ import annotations

import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
# When applied under meta/ctl-kernel/tests/, this resolves to ../reference.
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


class Round8ConformanceTests(unittest.TestCase):
    """Executable reproductions for Round 8 protocol/reference mismatches."""

    def test_candidate_policy_with_unsupported_basis_is_unsupported(self):
        store, manifest = ctl_ref.build_case("genesis")
        state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        old_policy_cid = manifest["objects"]["policy"]
        role_cid = manifest["objects"]["role"]

        payload = ctl_ref.policy_payload()
        payload["rules"] = ctl_ref.sort_objects(
            payload["rules"]
            + [
                {
                    "effect": "allow",
                    "subject": {"role_id": "role:owner"},
                    "actions": ["revision.record"],
                    "resources": [{"logical_id_prefix": "claim:"}],
                    "required_evidence_basis": ["agent/unknown-basis/1"],
                }
            ]
        )
        candidate = ctl_ref.revision(
            "sys:policy",
            "policy-set",
            "ctl-governance/policy-set/1",
            payload,
            parents=[old_policy_cid],
        )
        candidate["created_at"] = "2026-06-25T23:00:01Z"
        candidate_cid = store.add(candidate)
        batch = ctl_ref.batch(
            state["root_cid"],
            [candidate_cid],
            [
                ctl_ref.set_op(
                    "sys:policy",
                    ctl_ref.bound(old_policy_cid),
                    candidate_cid,
                )
            ],
            [role_cid],
        )
        batch_cid = store.add(batch)

        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "unsupported",
        )

    def test_invalid_parent_root_dominates_unsupported_profile(self):
        store, manifest = ctl_ref.build_case("genesis")
        state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        role_cid = manifest["objects"]["role"]

        unknown = ctl_ref.revision(
            "claim:unknown",
            "claim",
            "vendor/example/1",
            {},
        )
        unknown_cid = store.add(unknown)
        # A valid object CID, but not the validated parent root CID.
        batch = ctl_ref.batch(
            manifest["genesis_batch"],
            [unknown_cid],
            [],
            [role_cid],
        )
        batch_cid = store.add(batch)

        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )

    def test_invalid_gregorian_timestamp_is_rejected(self):
        store = ctl_ref.Store()
        revision = ctl_ref.revision(
            "claim:timestamp",
            "claim",
            "ctl-data/opaque-json/1",
            {},
        )
        revision["created_at"] = "0000-99-99T99:99:99Z"
        cid = store.add(revision)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_revision(store, cid, revision)

    def test_nesting_depth_65_is_rejected(self):
        store = ctl_ref.Store()
        nested = 0
        for _ in range(65):
            nested = {"x": nested}
        revision = ctl_ref.revision(
            "claim:deep",
            "claim",
            "ctl-data/opaque-json/1",
            {"x": nested},
        )
        cid = store.add(revision)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_revision(store, cid, revision)

    def test_canonical_object_over_one_mib_is_rejected(self):
        store = ctl_ref.Store()
        payload = {f"k{i}": "x" * 262_144 for i in range(5)}
        revision = ctl_ref.revision(
            "claim:large",
            "claim",
            "ctl-data/opaque-json/1",
            payload,
        )
        self.assertGreater(len(ctl_ref.canonical_bytes(revision)), 1_048_576)
        with self.assertRaises(ctl_ref.InvalidHistory):
            store.add(revision)

    def test_logical_id_over_256_bytes_is_rejected(self):
        store = ctl_ref.Store()
        revision = ctl_ref.revision(
            "claim:" + "a" * 300,
            "claim",
            "ctl-data/opaque-json/1",
            {},
        )
        cid = store.add(revision)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_revision(store, cid, revision)

    def test_principal_role_bindings_over_64_is_rejected(self):
        store = ctl_ref.Store()
        policy = ctl_ref.revision(
            "sys:policy",
            "policy-set",
            "ctl-governance/policy-set/1",
            ctl_ref.policy_payload(),
        )
        policy_cid = store.add(policy)

        role_cids = []
        recorded = [policy_cid]
        operations = [ctl_ref.set_op("sys:policy", ctl_ref.absent(), policy_cid)]
        for index in range(65):
            logical_id = f"role-binding:r{index:02d}"
            role = ctl_ref.revision(
                logical_id,
                "role-binding",
                "ctl-governance/role-binding/1",
                {
                    "actor_id": "actor:jin",
                    "role_id": "role:owner",
                    "scope": {"project_id": "project:demo"},
                },
            )
            role_cid = store.add(role)
            role_cids.append(role_cid)
            recorded.append(role_cid)
            operations.append(ctl_ref.set_op(logical_id, ctl_ref.absent(), role_cid))

        genesis_batch = ctl_ref.batch(None, recorded, operations, [])
        genesis_batch_cid = store.add(genesis_batch)
        state = ctl_ref.derive_genesis(store, genesis_batch_cid)

        claim = ctl_ref.revision(
            "claim:many-roles",
            "claim",
            "ctl-data/opaque-json/1",
            {"value": 1},
        )
        claim_cid = store.add(claim)
        transition = ctl_ref.batch(
            state["root_cid"],
            [claim_cid],
            [ctl_ref.set_op("claim:many-roles", ctl_ref.absent(), claim_cid)],
            role_cids,
        )
        transition_cid = store.add(transition)

        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, transition_cid)),
            "invalid",
        )

    def test_role_binding_cannot_satisfy_run_receipt_basis(self):
        store = ctl_ref.Store()
        rules = [
            {
                "effect": "allow",
                "subject": {"role_id": "role:owner"},
                "actions": ctl_ref.sort_scalars(["binding.set", "revision.record"]),
                "resources": [{"logical_id_prefix": "claim:"}],
                "required_evidence_basis": ["agent/run-receipt/1"],
            },
            {
                "effect": "allow",
                "subject": {"role_id": "role:owner"},
                "actions": ctl_ref.sort_scalars(
                    ["binding.set", "policy.replace", "revision.record"]
                ),
                "resources": [{"logical_id": "sys:policy"}],
                "required_evidence_basis": [],
            },
        ]
        policy = ctl_ref.revision(
            "sys:policy",
            "policy-set",
            "ctl-governance/policy-set/1",
            {"version": 1, "default": "deny", "rules": ctl_ref.sort_objects(rules)},
        )
        policy_cid = store.add(policy)
        role = ctl_ref.revision(
            "role-binding:operator",
            "role-binding",
            "ctl-governance/role-binding/1",
            {
                "actor_id": "actor:jin",
                "role_id": "role:owner",
                "scope": {"project_id": "project:demo"},
            },
        )
        role_cid = store.add(role)
        genesis_batch = ctl_ref.batch(
            None,
            [policy_cid, role_cid],
            [
                ctl_ref.set_op("role-binding:operator", ctl_ref.absent(), role_cid),
                ctl_ref.set_op("sys:policy", ctl_ref.absent(), policy_cid),
            ],
            [],
        )
        genesis_batch_cid = store.add(genesis_batch)
        state = ctl_ref.derive_genesis(store, genesis_batch_cid)

        claim = ctl_ref.revision(
            "claim:fake-receipt",
            "claim",
            "ctl-data/opaque-json/1",
            {"value": 1},
        )
        claim_cid = store.add(claim)
        evidence = [
            {
                "target": {"kind": "recorded_revision", "cid": claim_cid},
                "basis": "agent/run-receipt/1",
                "cid": role_cid,
            },
            {
                "target": {"kind": "binding_op", "logical_id": "claim:fake-receipt"},
                "basis": "agent/run-receipt/1",
                "cid": role_cid,
            },
        ]
        transition = ctl_ref.batch(
            state["root_cid"],
            [claim_cid],
            [
                ctl_ref.set_op(
                    "claim:fake-receipt",
                    ctl_ref.absent(),
                    claim_cid,
                )
            ],
            [role_cid],
            evidence=evidence,
        )
        transition_cid = store.add(transition)

        self.assertIn(
            classify(lambda: ctl_ref.validate_transition(store, state, transition_cid)),
            {"invalid", "unsupported"},
        )

    def test_malformed_binding_op_returns_invalid_not_python_exception(self):
        store, manifest = ctl_ref.build_case("genesis")
        batch = store.resolve(manifest["genesis_batch"])
        batch["binding_ops"] = [{"op": "set"}]
        batch_cid = store.add(batch)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.derive_genesis(store, batch_cid)


if __name__ == "__main__":
    unittest.main()
