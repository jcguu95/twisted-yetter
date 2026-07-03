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


def test_su2k_fusion_braid_evaluator_yasui_su2_2_calibration() -> None:
    env = dict(os.environ)
    env["DOT_SAGE"] = str(Path.cwd() / ".sage")
    script = r'''
import importlib.util, json, sys
from pathlib import Path

oracle_path = Path("experiments/sage/su2_2_braid_oracle.sage.py").resolve()
oracle_spec = importlib.util.spec_from_file_location("oracle", oracle_path)
oracle = importlib.util.module_from_spec(oracle_spec)
sys.modules["oracle"] = oracle
oracle_spec.loader.exec_module(oracle)

eval_path = Path("experiments/sage/su2k_fusion_braid_evaluator.sage.py").resolve()
eval_spec = importlib.util.spec_from_file_location("su2k", eval_path)
su2k = importlib.util.module_from_spec(eval_spec)
sys.modules["su2k"] = su2k
eval_spec.loader.exec_module(su2k)

payload = json.loads(Path("experiments/results/yasui/figure3-a1-braid-payload-v1.json").read_text())
evaluator = su2k.SU2KBraidEvaluator(2, exact=False, precision=120)
word = tuple(payload["braid_word"])
framings = tuple(payload["framings_in_braid_order"])
max_diff = 0.0
for a in range(3):
    for b in range(3):
        for c in range(3):
            labels = (a, b, c)
            oracle_value = complex(oracle.fixed_label_rt_value(payload["n_strands"], word, labels, framings))
            evaluator_value = complex(evaluator.fixed_label_value(payload["n_strands"], word, labels, framings))
            max_diff = max(max_diff, abs(oracle_value - evaluator_value))
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
