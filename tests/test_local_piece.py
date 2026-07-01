import json

import pytest

from twisted_yetter.local_piece import (
    LOCAL_PIECE_PROGRAM_SCHEMA,
    BraidClosure,
    BraidCrossingPiece,
    LocalPieceProgram,
    braid_closure_data,
    braid_closure_linking_matrix,
    braid_program,
)


def test_braid_program_composes_local_crossing_pieces() -> None:
    program = braid_program(
        program_id="right-trefoil",
        category_id="SU(2)_2",
        strand_count=2,
        braid_word=(1, 1, 1),
        framings=(0,),
        omega_labels=(1,),
        fixed_labels=(1,),
    )

    assert program.braid_word() == (1, 1, 1)
    assert program.closure_data().components == ((0, 1),)
    assert program.linking_matrix() == ((0,),)
    assert program.to_oracle_payload() == {
        "n_strands": 2,
        "braid_word": [1, 1, 1],
        "framings": [0],
        "omega_labels": [1],
        "fixed_labels": [1],
    }


def test_positive_hopf_closure_components_and_linking_are_explicit() -> None:
    data = braid_closure_data(2, (1, 1))

    assert data.components == ((0,), (1,))
    assert data.strand_to_component == (0, 1)
    assert braid_closure_linking_matrix(2, (1, 1)) == ((0, 1), (1, 0))


def test_local_piece_program_round_trips_json() -> None:
    program = braid_program(
        program_id="positive-hopf",
        category_id="SU(2)_2",
        strand_count=2,
        braid_word=(1, 1),
        framings=(0, 0),
        omega_labels=(0, 1),
        fixed_labels=(1, 2),
        description="Positive Hopf as two local R pieces.",
    )

    payload = program.to_json()

    assert payload["schema"] == LOCAL_PIECE_PROGRAM_SCHEMA
    assert json.loads(json.dumps(payload)) == payload
    assert LocalPieceProgram.from_json(payload).diagnostics() == program.diagnostics()


def test_rejects_unsupported_or_malformed_local_pieces() -> None:
    with pytest.raises(ValueError, match="unsupported local piece kind"):
        LocalPieceProgram.from_json(
            {
                "schema": LOCAL_PIECE_PROGRAM_SCHEMA,
                "program_id": "cup-not-yet",
                "category_id": "SU(2)_2",
                "strand_count": 2,
                "pieces": [{"kind": "cup", "id": "cup1", "left_index": 1, "sign": 1}],
                "closure": {"kind": "braid_closure", "framings": [0, 0], "omega_labels": [0, 0]},
            }
        )

    with pytest.raises(ValueError, match="strand_count - 1"):
        LocalPieceProgram(
            "bad-crossing-index",
            "SU(2)_2",
            2,
            pieces=(BraidCrossingPiece("x1", 2, 1),),
            closure=BraidClosure((0, 0), (0, 0)),
        )


def test_closure_label_counts_must_match_component_count() -> None:
    with pytest.raises(ValueError, match="closure.framings count"):
        braid_program(
            program_id="bad-framing-count",
            category_id="SU(2)_2",
            strand_count=2,
            braid_word=(1, 1, 1),
            framings=(0, 0),
            omega_labels=(0, 0),
        )

    with pytest.raises(ValueError, match="closure.fixed_labels count"):
        braid_program(
            program_id="bad-fixed-label-count",
            category_id="SU(2)_2",
            strand_count=2,
            braid_word=(1, 1),
            framings=(0, 0),
            omega_labels=(0, 1),
            fixed_labels=(1,),
        )
