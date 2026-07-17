#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -eq 0 ]]; then
  printf 'usage: %s lean/Module.lean [lean/Next.lean ...]\n' "$0" >&2
  exit 64
fi

for source in "$@"; do
  case "${source}" in
    lean/*.lean) ;;
    *)
      printf 'source must be under lean/ and end in .lean: %s\n' "${source}" >&2
      exit 64
      ;;
  esac

  relative="${source#lean/}"
  output=".lake/build/lib/lean/${relative%.lean}.olean"
  mkdir -p "$(dirname "${output}")"
  ./scripts/lean_local_check.sh -o "${output}" "${source}"
done
