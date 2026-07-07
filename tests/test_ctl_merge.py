from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DOGFOOD_ROOT = REPO_ROOT / "ctl-dogfood"
CTL_META_ROOT = Path(os.environ.get("CTL_META_ROOT", REPO_ROOT.parent / "ctl-meta")).resolve()
KERNEL_ROOT = CTL_META_ROOT / "meta" / "ctl-kernel"
sys.path.insert(0, str(KERNEL_ROOT / "reference"))
sys.path.insert(0, str(DOGFOOD_ROOT / "scripts"))

import ctl_ref  # noqa: E402
import ctl_merge  # noqa: E402
import ctl_store  # noqa: E402


def trust_anchor(genesis_root_cid: str) -> dict[str, str]:
    return {
        "project_id": "project:demo",
        "kernel_profile": "ctl-kernel/1",
        "genesis_root_cid": genesis_root_cid,
    }


def admit_claim(
    store: ctl_ref.Store,
    state: dict[str, object],
    role_cid: str,
    logical_id: str,
    payload: dict[str, object],
) -> dict[str, object]:
    old_cid = state["bindings"].get(logical_id)  # type: ignore[index,union-attr]
    parents = [] if old_cid is None else [old_cid]
    claim = ctl_ref.revision(logical_id, "claim", "ctl-data/opaque-json/1", payload, parents)
    claim_cid = store.add(claim)
    expected = ctl_ref.absent() if old_cid is None else ctl_ref.bound(old_cid)
    batch = ctl_ref.batch(
        state["root_cid"],  # type: ignore[index]
        [claim_cid],
        [ctl_ref.set_op(logical_id, expected, claim_cid)],
        [role_cid],
    )
    batch_cid = store.add(batch)
    return ctl_ref.validate_transition(store, state, batch_cid)  # type: ignore[arg-type]


class CtlMergeTests(unittest.TestCase):
    def genesis(self):
        store, manifest = ctl_ref.build_case("genesis")
        state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        return store, manifest, state

    def preview(self, store, base, main, incoming):
        return ctl_merge.build_merge_preview(
            store,
            main["root_cid"],
            incoming["root_cid"],
            trust_anchor(base["root_cid"]),
            base["root_cid"],
        )

    def admit(self, store, base, main, incoming):
        return ctl_merge.admit_merge_in_memory(
            store,
            main["root_cid"],
            incoming["root_cid"],
            trust_anchor(base["root_cid"]),
            actor_id="actor:jin",
            submitted_by="operator:local",
            admitted_at="2026-06-25T23:02:00Z",
            base_root=base["root_cid"],
        )

    def admit_auto_only(self, store, base, main, incoming):
        return ctl_merge.admit_merge_in_memory(
            store,
            main["root_cid"],
            incoming["root_cid"],
            trust_anchor(base["root_cid"]),
            actor_id="actor:jin",
            submitted_by="operator:local",
            admitted_at="2026-06-25T23:02:00Z",
            base_root=base["root_cid"],
            auto_only=True,
        )

    def write_test_store(self, root: Path, store, base, head):
        ctl_merge.write_all_objects(root, store)
        ref_common = {
            "schema": "ctl-dogfood/ref/1",
            "name": "refs/main",
            "project_id": "project:demo",
            "kernel_profile": "ctl-kernel/1",
            "genesis_root_cid": base["root_cid"],
            "updated_at": "2026-06-25T23:01:00Z",
            "updated_by": "operator:local",
        }
        ctl_merge.write_json(
            root / "refs" / "main.json",
            {**ref_common, "root_cid": head["root_cid"], "transition_cid": head["root"]["transition"]},
        )

    def test_distinct_branch_binding_can_auto_admit(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:branch", {"text": "branch"})

        report = self.preview(store, base, main, incoming)

        self.assertEqual(report["status"], "ok")
        self.assertEqual([item["status"] for item in report["items"]], ["auto-admit"])
        self.assertEqual(report["items"][0]["logical_id"], "claim:branch")

    def test_auto_admit_builds_valid_merge_root(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:branch", {"text": "branch"})

        report = self.admit(store, base, main, incoming)
        merged = ctl_ref.validate_chain(store, report["current_root_cid"], trust_anchor(base["root_cid"]))

        self.assertEqual(report["status"], "ok")
        self.assertEqual(len(report["merge_batches"]), 1)
        self.assertIn("claim:main", merged["bindings"])
        self.assertIn("claim:branch", merged["bindings"])

    def test_same_binding_cid_is_already_present(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:same", {"text": "same"})
        incoming = admit_claim(store, base, role_cid, "claim:same", {"text": "same"})

        report = self.preview(store, base, main, incoming)

        self.assertEqual(report["status"], "ok")
        self.assertEqual([item["status"] for item in report["items"]], ["already-present"])

    def test_main_at_intermediate_branch_state_fast_forwards(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        first = admit_claim(store, base, role_cid, "claim:topic", {"text": "one"})
        incoming = admit_claim(store, first, role_cid, "claim:topic", {"text": "two"})
        main = first

        preview = self.preview(store, base, main, incoming)
        report = self.admit(store, base, main, incoming)
        merged = ctl_ref.validate_chain(store, report["current_root_cid"], trust_anchor(base["root_cid"]))

        self.assertEqual([item["status"] for item in preview["items"]], ["already-present", "auto-admit"])
        self.assertEqual(report["status"], "ok")
        self.assertEqual(len(report["merge_batches"]), 1)
        self.assertEqual(merged["bindings"]["claim:topic"], incoming["bindings"]["claim:topic"])

    def test_fully_merged_multistep_branch_is_noop(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        first = admit_claim(store, base, role_cid, "claim:topic", {"text": "one"})
        incoming = admit_claim(store, first, role_cid, "claim:topic", {"text": "two"})
        main = incoming

        preview = self.preview(store, base, main, incoming)
        report = self.admit(store, base, main, incoming)

        self.assertEqual([item["status"] for item in preview["items"]], ["already-present", "already-present"])
        self.assertEqual(report["status"], "ok")
        self.assertEqual(report["merge_batches"], [])
        self.assertEqual(report["current_root_cid"], main["root_cid"])

    def test_same_logical_id_different_cid_conflicts(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:shared", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:shared", {"text": "branch"})

        report = self.preview(store, base, main, incoming)

        self.assertEqual(report["status"], "conflict")
        self.assertEqual([item["status"] for item in report["items"]], ["conflict"])
        self.assertEqual(report["items"][0]["main_current"]["state"], "bound")
        self.assertEqual(report["logical_ids"][0]["payload_diff"]["changed"]["text"]["main"], "main")
        self.assertEqual(report["logical_ids"][0]["payload_diff"]["changed"]["text"]["incoming"], "branch")

    def test_text_report_names_conflict_logical_id_and_payload_diff(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:shared", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:shared", {"text": "branch"})

        text = ctl_merge.format_merge_root_text(self.preview(store, base, main, incoming))

        self.assertIn("status: conflict", text)
        self.assertIn("claim:shared", text)
        self.assertIn("payload: changed", text)
        self.assertIn("main='main'", text)
        self.assertIn("incoming='branch'", text)

    def test_text_report_shows_operator_next_step_for_ok_merge(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:branch", {"text": "branch"})

        text = ctl_merge.format_merge_root_text(self.preview(store, base, main, incoming))

        self.assertIn("status: ok", text)
        self.assertIn("auto-admit=1", text)
        self.assertIn("transplant-revisions", text)

    def test_conflict_is_not_admitted(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:shared", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:shared", {"text": "branch"})
        object_count = len(store.objects)

        report = self.admit(store, base, main, incoming)

        self.assertEqual(report["status"], "conflict")
        self.assertNotIn("current_root_cid", report)
        self.assertEqual(len(store.objects), object_count)

    def test_auto_only_partial_transplant_skips_conflict_and_admits_safe_bindings(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        main = admit_claim(store, main, role_cid, "claim:shared", {"text": "main shared"})
        incoming = admit_claim(store, base, role_cid, "claim:branch-a", {"text": "branch a"})
        incoming = admit_claim(store, incoming, role_cid, "claim:shared", {"text": "branch shared"})
        incoming = admit_claim(store, incoming, role_cid, "claim:branch-b", {"text": "branch b"})

        normal = self.admit(store, base, main, incoming)
        partial = self.admit_auto_only(store, base, main, incoming)
        merged = ctl_ref.validate_chain(store, partial["current_root_cid"], trust_anchor(base["root_cid"]))

        self.assertEqual(normal["status"], "conflict")
        self.assertEqual(partial["status"], "ok")
        self.assertEqual(partial["mode"], "auto-only")
        self.assertEqual([item["logical_id"] for item in partial["skipped_conflicts"]], ["claim:shared"])
        self.assertIn("claim:branch-a", merged["bindings"])
        self.assertIn("claim:branch-b", merged["bindings"])
        self.assertEqual(merged["bindings"]["claim:shared"], main["bindings"]["claim:shared"])
        self.assertNotEqual(merged["bindings"]["claim:shared"], incoming["bindings"]["claim:shared"])

    def test_auto_only_store_manifest_records_skipped_conflicts(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        main = admit_claim(store, main, role_cid, "claim:shared", {"text": "main shared"})
        incoming = admit_claim(store, base, role_cid, "claim:branch", {"text": "branch"})
        incoming = admit_claim(store, incoming, role_cid, "claim:shared", {"text": "branch shared"})

        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            main_root = tmp_root / "main"
            incoming_root = tmp_root / "incoming"
            self.write_test_store(main_root, store, base, main)
            self.write_test_store(incoming_root, store, base, incoming)

            report = ctl_merge.admit_merge_to_store(
                main_root,
                incoming_root,
                incoming_root=incoming["root_cid"],
                expected_root=main["root_cid"],
                admitted_at="2026-06-25T23:02:00Z",
                actor_id="actor:jin",
                submitted_by="operator:local",
                base_root=base["root_cid"],
                auto_only=True,
            )
            manifest_doc = ctl_merge.load_json(Path(report["manifest_path"]))
            ref = ctl_merge.load_ref(main_root)
            tmp_path_text = str(tmp_root)

        self.assertEqual(report["status"], "ok")
        self.assertEqual(report["mode"], "auto-only")
        self.assertEqual(ref["root_cid"], report["current_root_cid"])
        self.assertEqual(manifest_doc["mode"], "auto-only")
        self.assertEqual([item["logical_id"] for item in manifest_doc["skipped_conflicts"]], ["claim:shared"])
        self.assertNotIn(tmp_path_text, json.dumps(manifest_doc, sort_keys=True))

    def test_store_preview_warns_about_incoming_branch_local_manifest(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:branch", {"text": "branch"})

        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            main_root = tmp_root / "main"
            incoming_root = tmp_root / "incoming"
            self.write_test_store(main_root, store, base, main)
            self.write_test_store(incoming_root, store, base, incoming)
            ctl_merge.write_json(
                incoming_root / "manifests" / "branch-local.json",
                {
                    "schema": "ctl-dogfood/admission-manifest/1",
                    "current_root_cid": incoming["root_cid"],
                },
            )
            ctl_merge.write_json(
                incoming_root / "manifests" / "base.json",
                {
                    "schema": "ctl-dogfood/admission-manifest/1",
                    "current_root_cid": base["root_cid"],
                },
            )

            report = ctl_merge.build_store_merge_preview(
                main_root,
                incoming_root,
                main_root=main["root_cid"],
                incoming_root=incoming["root_cid"],
                base_root=base["root_cid"],
            )

        self.assertEqual(report["status"], "ok")
        self.assertEqual(len(report["warnings"]), 1)
        self.assertEqual(report["warnings"][0]["code"], "incoming_manifest_branch_local")
        self.assertEqual(report["warnings"][0]["path"], "manifests/branch-local.json")
        self.assertEqual(report["warnings"][0]["current_root_cid"], incoming["root_cid"])

    def test_text_report_shows_auto_only_command_for_mixed_reports(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        main = admit_claim(store, main, role_cid, "claim:shared", {"text": "main shared"})
        incoming = admit_claim(store, base, role_cid, "claim:branch", {"text": "branch"})
        incoming = admit_claim(store, incoming, role_cid, "claim:shared", {"text": "branch shared"})

        text = ctl_merge.format_merge_root_text(self.preview(store, base, main, incoming))

        self.assertIn("status: conflict", text)
        self.assertIn("python3 scripts/ctl_merge.py transplant-revisions", text)
        self.assertIn("--auto-only", text)
        self.assertIn("--expected-root", text)

    def test_runbook_same_root_is_noop_without_transplant_command(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "store"
            self.write_test_store(root, store, base, main)

            report = ctl_merge.build_runbook(root, root, main_root=main["root_cid"], incoming_root=main["root_cid"])

        self.assertEqual(report["status"], "ok")
        self.assertEqual(report["plan"]["kind"], "noop")
        self.assertFalse(report["plan"]["writes_state"])
        self.assertEqual(report["plan"]["commands"], [])

    def test_runbook_clean_branch_recommends_full_transplant(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:branch", {"text": "branch"})

        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            main_root = tmp_root / "main"
            incoming_root = tmp_root / "incoming"
            self.write_test_store(main_root, store, base, main)
            self.write_test_store(incoming_root, store, base, incoming)

            report = ctl_merge.build_runbook(
                main_root,
                incoming_root,
                main_root=main["root_cid"],
                incoming_root=incoming["root_cid"],
                base_root=base["root_cid"],
            )

        self.assertEqual(report["plan"]["kind"], "full-transplant")
        self.assertFalse(report["plan"]["writes_state"])
        command_text = "\n".join(report["plan"]["commands"])
        self.assertIn("transplant-revisions", command_text)
        self.assertIn("--expected-root " + main["root_cid"], command_text)
        self.assertNotIn("--auto-only", command_text)

    def test_runbook_mixed_branch_recommends_partial_auto_only(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        main = admit_claim(store, main, role_cid, "claim:shared", {"text": "main shared"})
        incoming = admit_claim(store, base, role_cid, "claim:branch", {"text": "branch"})
        incoming = admit_claim(store, incoming, role_cid, "claim:shared", {"text": "branch shared"})

        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            main_root = tmp_root / "main"
            incoming_root = tmp_root / "incoming"
            self.write_test_store(main_root, store, base, main)
            self.write_test_store(incoming_root, store, base, incoming)

            report = ctl_merge.build_runbook(
                main_root,
                incoming_root,
                main_root=main["root_cid"],
                incoming_root=incoming["root_cid"],
                base_root=base["root_cid"],
            )

        self.assertEqual(report["plan"]["kind"], "partial-auto-only")
        self.assertEqual(report["plan"]["blocked_logical_ids"], ["claim:shared"])
        command_text = "\n".join(report["plan"]["commands"])
        self.assertIn("--auto-only", command_text)

    def test_runbook_pure_conflict_blocks_transplant_command(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:shared", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:shared", {"text": "branch"})

        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            main_root = tmp_root / "main"
            incoming_root = tmp_root / "incoming"
            self.write_test_store(main_root, store, base, main)
            self.write_test_store(incoming_root, store, base, incoming)

            report = ctl_merge.build_runbook(
                main_root,
                incoming_root,
                main_root=main["root_cid"],
                incoming_root=incoming["root_cid"],
                base_root=base["root_cid"],
            )

        self.assertEqual(report["plan"]["kind"], "blocked-conflict")
        self.assertEqual(report["plan"]["commands"], [])
        self.assertEqual(report["plan"]["blocked_logical_ids"], ["claim:shared"])

    def test_manifest_plan_classifies_reachable_branch_local_and_unreadable(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:branch", {"text": "branch"})

        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            main_root = tmp_root / "main"
            incoming_root = tmp_root / "incoming"
            self.write_test_store(main_root, store, base, main)
            self.write_test_store(incoming_root, store, base, incoming)
            ctl_merge.write_json(
                incoming_root / "manifests" / "reachable.json",
                {"schema": "ctl-dogfood/admission-manifest/1", "current_root_cid": base["root_cid"]},
            )
            ctl_merge.write_json(
                incoming_root / "manifests" / "branch-local.json",
                {"schema": "ctl-dogfood/admission-manifest/1", "current_root_cid": incoming["root_cid"]},
            )
            unreadable = incoming_root / "manifests" / "bad.json"
            unreadable.parent.mkdir(parents=True, exist_ok=True)
            unreadable.write_text("{bad json\n")

            report = ctl_merge.build_manifest_plan(
                main_root,
                incoming_root,
                main_root=main["root_cid"],
            )

        by_path = {item["path"]: item for item in report["manifest_plan"]["items"]}
        self.assertEqual(report["status"], "warning")
        self.assertEqual(by_path["manifests/reachable.json"]["classification"], "reachable-from-target")
        self.assertEqual(by_path["manifests/branch-local.json"]["classification"], "branch-local")
        self.assertEqual(by_path["manifests/bad.json"]["classification"], "unreadable")

    def test_report_contract_stable_fields_are_present(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:branch", {"text": "branch"})

        preview = self.preview(store, base, main, incoming)

        for key in [
            "status",
            "summary",
            "logical_ids",
            "items",
            "recorded_items",
            "base_root_cid",
            "main_root_cid",
            "incoming_root_cid",
        ]:
            self.assertIn(key, preview)
        self.assertIsInstance(preview["items"], list)
        self.assertIsInstance(preview["recorded_items"], list)

    def test_admit_merge_to_store_writes_ref_and_manifest(self):
        store, manifest, base = self.genesis()
        role_cid = manifest["objects"]["role"]
        main = admit_claim(store, base, role_cid, "claim:main", {"text": "main"})
        incoming = admit_claim(store, base, role_cid, "claim:branch", {"text": "branch"})

        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            main_root = tmp_root / "main"
            incoming_root = tmp_root / "incoming"
            self.write_test_store(main_root, store, base, main)
            self.write_test_store(incoming_root, store, base, incoming)

            report = ctl_merge.admit_merge_to_store(
                main_root,
                incoming_root,
                incoming_root=incoming["root_cid"],
                expected_root=main["root_cid"],
                admitted_at="2026-06-25T23:02:00Z",
                actor_id="actor:jin",
                submitted_by="operator:local",
                base_root=base["root_cid"],
            )
            ref = ctl_merge.load_ref(main_root)

        self.assertEqual(report["status"], "ok")
        self.assertEqual(report["mode"], "full")
        self.assertEqual(report["skipped_conflicts"], [])
        self.assertEqual(ref["root_cid"], report["current_root_cid"])
        self.assertIn("manifest_path", report)

    def test_path_hygiene_reports_absolute_paths_and_allows_placeholders(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "decisions").mkdir()
            (root / "protocols").mkdir()
            (root / "decisions" / "bad.json").write_text('{"path": "/Users/example/worktree/file.json"}\n')
            (root / "protocols" / "ok.org").write_text("Use ${REPO_ROOT}/ctl-dogfood here.\n")

            report = ctl_store.path_hygiene_report(root)

        self.assertEqual(report["status"], "warning")
        self.assertEqual(len(report["warnings"]), 1)
        self.assertEqual(report["warnings"][0]["path"], "decisions/bad.json")
        self.assertIn("/Users/example/worktree/file.json", report["warnings"][0]["matches"])

    def test_agent_guide_and_report_contract_are_profile_neutral(self):
        agent_guide = (DOGFOOD_ROOT / "protocols" / "branch-store-merge-agents.org").read_text()
        contract = (DOGFOOD_ROOT / "protocols" / "branch-store-merge-report-contract.org").read_text()
        readme = (DOGFOOD_ROOT / "README.org").read_text()

        self.assertIn("branch-store-merge-agents.org", readme)
        self.assertIn("runbook", agent_guide)
        self.assertIn("manifest-plan", agent_guide)
        self.assertIn("JSON", contract)
        self.assertNotIn("subject-index", agent_guide)
        self.assertNotIn("Dic12", agent_guide)


if __name__ == "__main__":
    unittest.main()
