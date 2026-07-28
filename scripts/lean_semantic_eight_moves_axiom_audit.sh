#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
handle_path="lean/TwistedYetter/Kirby/Final/Semantics/HandleChain.lean"
presentation_path="lean/TwistedYetter/Kirby/Final/Semantics/Presentation.lean"
band_path="lean/TwistedYetter/Kirby/Final/Semantics/BandSlide.lean"
cancellation_path="lean/TwistedYetter/Kirby/Final/Semantics/Cancellation.lean"
isotopy_path="lean/TwistedYetter/Kirby/Final/Semantics/FramedIsotopy.lean"
slide_moves_path="lean/TwistedYetter/Kirby/Final/Semantics/SlideMoves.lean"
cancellation_moves_path="lean/TwistedYetter/Kirby/Final/Semantics/CancellationMoves.lean"
assembly_path="lean/TwistedYetter/Kirby/Final/Semantics/MoveAssembly.lean"
move_facade_path="lean/TwistedYetter/Kirby/Final/SemanticEightMoves.lean"
entry_path="lean/TwistedYetter/Kirby/Final/SemanticSpecification.lean"
audit_path="lean/TwistedYetter/Kirby/Final/SemanticEightMovesAxiomAudit.lean"
audit_file="${root}/${audit_path}"

move_paths=(
  "${handle_path}"
  "${presentation_path}"
  "${band_path}"
  "${cancellation_path}"
  "${isotopy_path}"
  "${slide_moves_path}"
  "${cancellation_moves_path}"
  "${assembly_path}"
)
move_files=()
for path in "${move_paths[@]}"; do
  move_files+=("${root}/${path}")
done

if [[ "$(rg '^import ' "${root}/${move_facade_path}")" != \
    "import TwistedYetter.Kirby.Final.Semantics.Moves" ]]; then
  printf 'Eight-move compatibility facade is no longer import-only.\n' >&2
  rg '^import ' "${root}/${move_facade_path}" >&2
  exit 1
fi

if rg -q \
    'TableTwo|RoleAwareTable|OrdinaryWindow|GraphicalEditProgram|LocalCycle|MoveCompiler|KirbyColor|Encircling' \
    "${move_files[@]}"; then
  printf 'Independent move specification references legacy move machinery.\n' >&2
  exit 1
fi

if rg -q '\b(sorry|admit|opaque)\b' "${move_files[@]}"; then
  printf 'Independent move specification contains a hidden proof oracle.\n' >&2
  exit 1
fi

expected_axioms="$(
  printf '%s\n' \
    'IsCleanOrientedBandSum' \
    'IsHandleChainOfPresentation' \
    'IsInducedHandleChainTransport' \
    | sort
)"
observed_axioms="$(
  rg --no-filename -o '^axiom [A-Za-z0-9_]+' "${move_files[@]}" |
    sed 's/^axiom //' |
    sort
)"
if [[ "${observed_axioms}" != "${expected_axioms}" ]]; then
  printf 'Independent move custom axiom denominator changed.\n' >&2
  printf 'Expected:\n%s\nObserved:\n%s\n' \
    "${expected_axioms}" "${observed_axioms}" >&2
  exit 1
fi

cd "${root}"

./scripts/lean_local_build.sh \
  "${move_paths[@]}" \
  "${move_facade_path}" \
  "${entry_path}" \
  "${audit_path}" \
  >/dev/null

./scripts/lean_local_check.sh "${audit_path}"
