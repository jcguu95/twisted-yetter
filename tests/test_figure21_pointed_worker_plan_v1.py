import json

from experiments.scripts.build_figure21_pointed_worker_plan_v1 import build_plan
from experiments.scripts.run_figure21_pointed_prehetzner_smoke_v1 import run_smoke as run_prehetzner_smoke
from experiments.scripts.run_figure21_pointed_worker_smoke_v1 import run_smoke


def test_figure21_pointed_worker_plan_has_no_blocked_rows(tmp_path):
    plan = build_plan(
        target_chunk_seconds=300,
        min_chunks=32,
        worker_count_hint=16,
        work_root=tmp_path / "chunks",
    )
    assert plan["status"] == "PASS_WORKER_PLAN_READY"
    assert plan["paid_batch_preflight_status"] == "PASS_PAID_BATCH_PREFLIGHT"
    assert plan["parameters"]["logical_worker_shards"] == 16
    assert plan["runbook"]["logical_worker_shards"] == 16
    assert plan["blocked_count"] == 0
    ready = [
        row
        for row in plan["rows"]
        if row["worker_plan_status"] == "READY_FOR_WORKERS"
    ]
    assert ready
    assert any(
        row["realization_id"] == "rank4-pointed-z2xz2-q002" for row in ready
    )
    for row in ready:
        assert row["prefix_modular_cross_check_status"] == "PASS"
        assert row["chunk_count"] >= 32
        assert "--worker-index {worker_index}" in row["worker_command_template"]
        assert "--no-aggregate" in row["worker_command_template"]
        assert "--work-root $PWD/" in row["worker_command_template"]
        assert "--work-root $PWD/" in row["aggregate_command"]
        assert row["smoke_sector_ids"]
        if row["rank"] == 5:
            assert row["runtime_cost_model"] == "VACUUM_AWARE_RANK5_WEIGHTED_ESTIMATE"
            assert row["vacuum_aware_estimate"]["status"] == (
                "PASS_RANK5_VACUUM_AWARE_TIMING"
            )
            assert row["runtime_estimate_warnings"] == []


def test_figure21_pointed_worker_smoke_runs_one_case(tmp_path):
    plan = build_plan(
        target_chunk_seconds=300,
        min_chunks=32,
        worker_count_hint=16,
        work_root=tmp_path / "chunks",
    )
    plan_path = tmp_path / "plan.json"
    plan_path.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n")
    smoke = run_smoke(
        plan_path=plan_path,
        smoke_root=tmp_path / "smoke",
        max_rows=1,
        sectors_per_row=1,
    )
    assert smoke["status"] == "PASS_WORKER_SMOKE"
    assert smoke["smoke_case_count"] == 1
    assert smoke["failed_case_count"] == 0
    result = smoke["results"][0]
    assert result["status"] == "PASS"
    assert result["parsed_last_stdout_json"]["status"] == "PASS_CHUNK_COMPLETE"


def test_figure21_pointed_prehetzner_smoke_checks_planned_chunk_shape(tmp_path):
    plan = build_plan(
        target_chunk_seconds=300,
        min_chunks=32,
        worker_count_hint=16,
        work_root=tmp_path / "chunks",
    )
    plan_path = tmp_path / "plan.json"
    plan_path.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n")
    smoke = run_prehetzner_smoke(plan_path=plan_path)
    assert smoke["status"] == "PASS_PREHETZNER_SMOKE"
    assert smoke["ready_row_count_smoked"] == plan["ready_count"]
    assert smoke["failed_row_count"] == 0
    for row in smoke["rows"]:
        assert row["status"] == "PASS"
        assert row["chunk_count"] % row["worker_count"] == 0
        assert row["partition_sector_count"] == row["full_sector_count"]
        if row["rank"] == 5:
            ranks = {
                result["projector_rank"] for result in row["sector_results"]
            }
            assert {0, 1} <= ranks
