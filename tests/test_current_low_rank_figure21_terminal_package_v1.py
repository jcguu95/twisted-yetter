import json

from experiments.scripts.build_current_low_rank_figure21_terminal_package_v1 import (
    NONTRIVIAL_RULE_PATH,
    TARGET_READINESS_PATH,
    build_package,
)
from experiments.scripts.build_figure21_pointed_batch_result_v1 import (
    PREFIX_SWEEP_PATH,
    PREHETZNER_SMOKE_PATH,
    WORKER_SMOKE_PATH,
    build_result,
)
from experiments.scripts.build_figure21_pointed_worker_plan_v1 import build_plan
from experiments.scripts.run_figure21_pointed_prehetzner_smoke_v1 import (
    run_smoke as run_prehetzner_smoke,
)
from experiments.scripts.run_figure21_pointed_worker_smoke_v1 import (
    run_smoke as run_worker_smoke,
)


def _write_matching_smokes(plan_path, tmp_path):
    worker_smoke = run_worker_smoke(
        plan_path=plan_path,
        smoke_root=tmp_path / "smoke",
        max_rows=1,
        sectors_per_row=1,
    )
    worker_smoke_path = tmp_path / "worker-smoke.json"
    worker_smoke_path.write_text(
        json.dumps(worker_smoke, indent=2, sort_keys=True) + "\n"
    )
    prehetzner_smoke = run_prehetzner_smoke(plan_path=plan_path)
    prehetzner_smoke_path = tmp_path / "prehetzner-smoke.json"
    prehetzner_smoke_path.write_text(
        json.dumps(prehetzner_smoke, indent=2, sort_keys=True) + "\n"
    )
    return worker_smoke_path, prehetzner_smoke_path


def test_pointed_batch_result_terminal_blocks_without_remote_capacity(tmp_path):
    plan = build_plan(
        target_chunk_seconds=300,
        min_chunks=32,
        worker_count_hint=16,
        work_root=tmp_path / "chunks",
    )
    plan_path = tmp_path / "plan.json"
    plan_path.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n")
    worker_smoke_path, prehetzner_smoke_path = _write_matching_smokes(
        plan_path, tmp_path
    )

    batch = build_result(
        plan_path=plan_path,
        worker_smoke_path=worker_smoke_path,
        prehetzner_smoke_path=prehetzner_smoke_path,
        prefix_sweep_path=PREFIX_SWEEP_PATH,
        work_root=tmp_path / "chunks",
        remote_capacity_provided=False,
    )

    assert batch["status"] == "TERMINAL_BLOCKED_REMOTE_CAPACITY_NOT_PROVIDED"
    rank2_rows = [row for row in batch["rows"] if row["rank"] == 2]
    ready_rows = [
        row for row in batch["rows"] if row["worker_plan_status"] == "READY_FOR_WORKERS"
    ]
    assert {row["row_status"] for row in rank2_rows} == {
        "COMPLETE_FROM_PREFIX_SWEEP"
    }
    assert ready_rows
    assert {row["row_status"] for row in ready_rows} == {
        "TERMINAL_BLOCKED_REMOTE_CAPACITY_NOT_PROVIDED"
    }


def test_terminal_package_records_all_three_terminal_lines(tmp_path):
    plan = build_plan(
        target_chunk_seconds=300,
        min_chunks=32,
        worker_count_hint=16,
        work_root=tmp_path / "chunks",
    )
    plan_path = tmp_path / "plan.json"
    plan_path.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n")
    worker_smoke_path, prehetzner_smoke_path = _write_matching_smokes(
        plan_path, tmp_path
    )
    batch = build_result(
        plan_path=plan_path,
        worker_smoke_path=worker_smoke_path,
        prehetzner_smoke_path=prehetzner_smoke_path,
        prefix_sweep_path=PREFIX_SWEEP_PATH,
        work_root=tmp_path / "chunks",
        remote_capacity_provided=False,
    )
    batch_path = tmp_path / "batch.json"
    batch_path.write_text(json.dumps(batch, indent=2, sort_keys=True) + "\n")

    package = build_package(
        pointed_batch_path=batch_path,
        nontrivial_rule_path=NONTRIVIAL_RULE_PATH,
        target_readiness_path=TARGET_READINESS_PATH,
    )

    assert package["status"] == "TERMINAL_WITH_EXPLICIT_BLOCKERS"
    lines = package["lines"]
    assert lines["figure21_pointed_batch"]["status"] == (
        "TERMINAL_BLOCKED_REMOTE_CAPACITY_NOT_PROVIDED"
    )
    nonpointed = lines["nonpointed_unresolved_rows"]
    blocked_families = {
        row["family_id"] for row in nonpointed["blocked_or_unknown_rows"]
    }
    assert {"rank3-ising", "rank5-su2-4", "rank5-psu3-4"} <= blocked_families
    discarded = {
        row["family_id"]
        for row in nonpointed["discarded_trivial_universal_group_rows"]
    }
    assert "rank5-psu2-9" in discarded
    deferred = {
        row["family_id"] for row in nonpointed["resolved_deferred_nonpointed_rows"]
    }
    assert "rank4-semion-times-fibonacci" in deferred
    assert lines["exotic_vs_standard_comparison_readiness"]["status"] == (
        "TERMINAL_BLOCKED_TARGET_CERTIFICATION_MISSING"
    )
    assert "This does not make a CTL final theorem claim." in package["exact_non_claims"]
