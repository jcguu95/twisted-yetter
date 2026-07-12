# Morse DSL Prototype

This is a small Python prototype for hand-writing Morse/tangle diagrams.
It expands convenient builder calls into local fundamental forms while
checking the active left-to-right strand order.

Status: `DRAFT_NOT_VERIFIED_AGAINST_PRINTED_DIAGRAM`.  This is input and
inspection infrastructure, not a category-theoretic evaluator and not a proof
that the draft transcription agrees with Gompf-Stipsicz Figure 8.15.

Current scope:

- `cup`, `cap`, `cross`, and one-sided `kink` are fundamental forms.
- `nested_cups`, `over_left` / `over_right`, `kink_each`, and `full_twist`
  are convenience functions that expand into fundamental forms.
- `over_left(..., times=n)` and `over_right(..., times=n)` are state-dependent:
  they infer the next adjacent strand from the current active order at each
  crossing.
- This is not an evaluator yet.

Run the K3 Figure 8.15 draft prefix:

```sh
PYTHONPATH=. python experiments/scripts/k3_figure815_morse_draft.py \
  --write /tmp/k3-figure815-morse-prefix-expanded-v1.json
```

Generate the repo-local E(1) and K3/E(2) draft inputs:

```sh
python experiments/scripts/k3_figure815_morse_draft.py \
  --wheel-count 4 --self-twist 1 --name "E(1)" \
  --write experiments/inputs/gompf-stipsicz/figure815-e1-morse-draft-v1.json

python experiments/scripts/k3_figure815_morse_draft.py \
  --wheel-count 10 --self-twist 2 --name "K3/E(2)" \
  --write experiments/inputs/gompf-stipsicz/figure815-k3-e2-morse-draft-v1.json
```

Render the inspection diagrams:

```sh
python experiments/scripts/render_morse_svg.py \
  experiments/inputs/gompf-stipsicz/figure815-e1-morse-draft-v1.json \
  --out /tmp/e1-figure815-rect45-vscale24.svg \
  --layout-mode unoptimized --vertical-mode scheduled \
  --draw-style rectilinear45 --stroke-scale 2 --vertical-scale 2.4 \
  --collision-report /tmp/e1-figure815-rect45-vscale24-collisions.json

python experiments/scripts/render_morse_svg.py \
  experiments/inputs/gompf-stipsicz/figure815-k3-e2-morse-draft-v1.json \
  --out /tmp/k3-figure815-rect45-vscale24.svg \
  --layout-mode unoptimized --vertical-mode scheduled \
  --draw-style rectilinear45 --stroke-scale 2 --vertical-scale 2.4 \
  --collision-report /tmp/k3-figure815-rect45-vscale24-collisions.json
```

Run tests:

```sh
env UV_CACHE_DIR=/tmp/uv-cache PYTHONPATH=. uv run pytest tests/test_morse_dsl.py
```
