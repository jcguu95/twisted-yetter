import os
import subprocess
from pathlib import Path


def test_su2k_fusion_braid_evaluator_self_test_passes() -> None:
    env = dict(os.environ)
    env["DOT_SAGE"] = str(Path.cwd() / ".sage")
    result = subprocess.run(
        ["sage", "experiments/sage/su2k_fusion_braid_evaluator.sage.py", "--self-test"],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )

    assert '"status": "pass"' in result.stdout
    assert "right_trefoil_sigma_matches_existing_oracle_value" in result.stdout


def test_su2k_fusion_braid_evaluator_yasui_su2_2_r1_raw_rt_profile() -> None:
    env = dict(os.environ)
    env["DOT_SAGE"] = str(Path.cwd() / ".sage")
    script = r'''
import importlib.util, itertools, json, sys
from pathlib import Path
from sage.all import ComplexField

eval_path = Path("experiments/sage/su2k_fusion_braid_evaluator.sage.py").resolve()
eval_spec = importlib.util.spec_from_file_location("su2k", eval_path)
su2k = importlib.util.module_from_spec(eval_spec)
sys.modules["su2k"] = su2k
eval_spec.loader.exec_module(su2k)

payload = json.loads(Path("experiments/results/yasui/figure3-a1-r1-normalized-braid-payload-v1.json").read_text())
evaluator = su2k.SU2KBraidEvaluator(2, exact=False, precision=120)
CF = ComplexField(120)

def omega(cache, labels):
    total = evaluator.zero()
    for fixed_labels, amplitude in cache.items():
        coefficient = evaluator.one()
        for omega_label, simple_label in zip(labels, fixed_labels, strict=True):
            coefficient *= evaluator.dimension(simple_label) * evaluator.character(omega_label, simple_label)
        total += coefficient * amplitude
    return total

def yasui_labels(alpha):
    alpha_h, alpha_e1, alpha_e2 = alpha
    by_source = {"A": alpha_e2, "B": alpha_h, "C": alpha_e1}
    return tuple(by_source[name] for name in payload["omega_label_order"])

yasui_cache = evaluator.sector_amplitudes(
    payload["n_strands"],
    tuple(payload["braid_word"]),
    tuple(payload["framings_in_braid_order"]),
)
standard_cache = evaluator.sector_amplitudes(3, (), (1, -1, -1))
max_diff = CF(0)
for alpha in itertools.product((0, 1), repeat=3):
    max_diff = max(max_diff, abs(CF(omega(yasui_cache, yasui_labels(alpha)) - omega(standard_cache, alpha))))
print(max_diff)
raise SystemExit(0 if max_diff < 1e-12 else 1)
'''
    result = subprocess.run(
        ["sage", "-python", "-c", script],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )

    assert float(result.stdout.strip()) < 1e-12


def test_su2k_fusion_braid_evaluator_satisfies_braid_relation_beyond_level_2() -> None:
    env = dict(os.environ)
    env["DOT_SAGE"] = str(Path.cwd() / ".sage")
    script = r'''
import importlib.util, itertools, sys
from pathlib import Path
from sage.all import ComplexField

eval_path = Path("experiments/sage/su2k_fusion_braid_evaluator.sage.py").resolve()
eval_spec = importlib.util.spec_from_file_location("su2k", eval_path)
su2k = importlib.util.module_from_spec(eval_spec)
sys.modules["su2k"] = su2k
eval_spec.loader.exec_module(su2k)

CF = ComplexField(100)

def compose(ev, sequence, total_charge, word):
    basis = ev.paths(sequence, total_charge)
    state = {(path, path): ev.one() for path in basis}
    current_sequence = tuple(sequence)
    for generator in word:
        crossing, _next_basis = ev.crossing_entries(
            current_sequence,
            total_charge,
            abs(generator) - 1,
            generator > 0,
        )
        state = ev._compose_sparse(crossing, state)
        current_sequence = ev.swapped_sequence(current_sequence, abs(generator) - 1)
    return current_sequence, state

max_diff = CF(0)
for level in (3, 4, 6):
    ev = su2k.SU2KBraidEvaluator(level, exact=False, precision=120)
    for sequence in itertools.product(ev.labels, repeat=3):
        for total_charge in ev.labels:
            if not ev.paths(sequence, total_charge):
                continue
            target_left, left = compose(ev, sequence, total_charge, (1, 2, 1))
            target_right, right = compose(ev, sequence, total_charge, (2, 1, 2))
            if target_left != target_right:
                raise AssertionError((level, sequence, total_charge, target_left, target_right))
            for key in set(left) | set(right):
                diff = abs(CF(left.get(key, ev.zero()) - right.get(key, ev.zero())))
                max_diff = max(max_diff, diff)

print(max_diff)
raise SystemExit(0 if max_diff < CF("1e-20") else 1)
'''
    result = subprocess.run(
        ["sage", "-python", "-c", script],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )

    assert float(result.stdout.strip()) < 1e-20
