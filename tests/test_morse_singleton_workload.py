import json

from experiments.scripts.morse_singleton_workload import (
    FsyncJSONLWriter,
    atomic_write_json,
    balanced_lpt_shards,
    iter_singleton_payloads,
    payload_sha256,
    read_jsonl,
    recover_jsonl_checkpoint,
)


def test_balanced_lpt_shards_preserve_rows_and_balance_heavy_items():
    rows = [
        {"sector_index": index, "estimated_work": weight}
        for index, weight in enumerate((9, 8, 7, 6, 5, 4, 3, 2, 1))
    ]
    shards = balanced_lpt_shards(rows, 3, "estimated_work")
    observed = sorted(
        row["sector_index"] for shard in shards for row in shard["rows"]
    )
    assert observed == list(range(9))
    loads = [shard["estimated_work"] for shard in shards]
    assert sum(loads) == sum(row["estimated_work"] for row in rows)
    assert max(loads) - min(loads) <= 2
    for shard in shards:
        weights = [row["estimated_work"] for row in shard["rows"]]
        assert weights == sorted(weights)


def test_atomic_json_and_jsonl_helpers(tmp_path):
    destination = tmp_path / "nested" / "payload.json"
    atomic_write_json(destination, {"value": 3, "status": "pass"})
    assert json.loads(destination.read_text()) == {"status": "pass", "value": 3}

    jsonl = tmp_path / "rows.jsonl"
    jsonl.write_text('{"sector_index":2,"estimated_work":4}\n')
    assert read_jsonl(jsonl) == [{"sector_index": 2, "estimated_work": 4}]
    assert payload_sha256({"b": 2, "a": 1}) == payload_sha256({"a": 1, "b": 2})


def test_durable_jsonl_checkpoint_recovers_only_torn_final_row(tmp_path):
    identity = "fixed-identity"
    ledger = tmp_path / "singleton-ledger-worker.jsonl"
    row = {
        "status": "pass",
        "evaluation_identity_sha256": identity,
        "sector_index": 7,
    }
    with FsyncJSONLWriter(ledger) as writer:
        writer.append(row)
    with ledger.open("ab") as handle:
        handle.write(b'{"status":"pass"')

    assert recover_jsonl_checkpoint(ledger, identity) == {7: row}
    assert ledger.read_text().endswith("\n")
    assert list(iter_singleton_payloads([tmp_path])) == [
        (f"{ledger}#1", row)
    ]


def test_jsonl_checkpoint_rejects_identity_mismatch(tmp_path):
    ledger = tmp_path / "singleton-ledger-worker.jsonl"
    with FsyncJSONLWriter(ledger) as writer:
        writer.append(
            {
                "status": "pass",
                "evaluation_identity_sha256": "old",
                "sector_index": 0,
            }
        )

    try:
        recover_jsonl_checkpoint(ledger, "new")
    except ValueError as error:
        assert "identity mismatch" in str(error)
    else:
        raise AssertionError("identity mismatch was silently accepted")
