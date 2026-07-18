#!/usr/bin/env bash
set -euo pipefail

LEAN_NUM_THREADS=1 ./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/ConcreteMarkedPairAssemblyAxiomAudit.lean
