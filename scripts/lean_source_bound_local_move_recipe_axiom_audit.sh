#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/SourceBoundLocalMoveRecipe.lean \
  lean/TwistedYetter/Kirby/SourceBoundLocalMoveRecipeAxiomAudit.lean \
  >/dev/null

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/SourceBoundLocalMoveRecipeAxiomAudit.lean
