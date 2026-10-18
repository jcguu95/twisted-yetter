# Homologically Twisted Crane--Yetter Invariants

This repository contains a draft manuscript, a Lean 4 companion formalization,
and computational research artifacts for homologically twisted Crane--Yetter
invariants of smooth four-manifolds.

> **Research snapshot.** The manuscript and formalization remain under expert
> review. This repository establishes a public, reproducible snapshot of the
> project; it does not claim a fully foundational formalization of every
> categorical or Kirby-topological input.

## Main construction

Let `C` be a premodular fusion category over the complex numbers and let
`eta : Id C => Id C` be a monoidal natural automorphism. For a closed connected
oriented smooth four-manifold `X` and a class `alpha` in integral second
homology, the project constructs a scalar

```text
CY_(C, eta)(X, alpha).
```

The draft proves marked oriented-diffeomorphism invariance using a special
Kirby-diagram evaluator. For simply connected manifolds it gives odd and even
stable formulas; in the modular case these reduce to an explicit closed
formula. The non-simply-connected marked case and the non-semisimple case are
left open.

The manuscript deliberately distinguishes this fixed-character integral
specialization from the full coefficient-group proposal in Yetter's 1993
note.

## Manuscript

The source is in [`paper/`](paper/). A compiled draft is attached to the
[latest GitHub release](https://github.com/jcguu95/twisted-yetter/releases/latest)
as `homologically-twisted-crane-yetter-draft.pdf`.

Build it with:

```bash
make -C paper
```

This requires a LaTeX installation containing `latexmk` and `biber`.

## Lean companion

The clean public manifold-level definitions are:

- [`TwistedYetter`](lean/TwistedYetter/Kirby/Final/TwistedYetter.lean)
- [`TwistedYetter_diffeomorphism_invariant`](lean/TwistedYetter/Kirby/Final/TwistedYetter.lean)
- [`TwistedYetter_premodular_numerical_formula`](lean/TwistedYetter/StableNoGo/FinalTheorem.lean)
- [`TwistedYetter_modular_explicit_formula`](lean/TwistedYetter/StableNoGo/ModularExplicitFormula.lean)

The human-facing audit of the formal inputs, intermediate structures, outputs,
and explicit assumptions is in
[`paper/appendix/formalization-interface.tex`](paper/appendix/formalization-interface.tex).

### Formalization status

At the publication checkpoint recorded in
[`explicit-trust-boundary-v16.json`](lean/TwistedYetter/Kirby/Final/Semantics/Independent/explicit-trust-boundary-v16.json):

- the full Lean build passed with one worker;
- the kernel axiom audit found no `sorryAx` in the final diffeomorphism theorem;
- that theorem depended on 19 explicitly named project axioms, in addition to
  `propext`, `Classical.choice`, and `Quot.sound`;
- a conservative source audit identified 33 proposition-valued structure
  fields requiring human semantic review;
- the source audit therefore remained
  `INCONCLUSIVE_HUMAN_REVIEW_REQUIRED`.

In particular, successful kernel compilation verifies the Lean proposition
relative to its declared inputs. It does **not** by itself verify that every
categorical and Kirby-topological declaration has the intended human meaning.
The manuscript appendix translates those declarations for expert review.

## Building

The project pins Lean and Mathlib in [`lean-toolchain`](lean-toolchain) and
[`lake-manifest.json`](lake-manifest.json).

```bash
lake exe cache get
env LAKE_JOBS=1 lake build
```

The one-worker command is intentional: the development is large and was
validated under a conservative local resource limit.

To print the final theorem's kernel-visible axioms:

```bash
env LAKE_JOBS=1 lake build TwistedYetter.Kirby.Final.FinalAxiomAudit
```

## Repository layout

- `paper/`: manuscript and human audit appendix
- `lean/`: Lean 4 development
- `experiments/`: numerical and diagrammatic research artifacts
- `tests/`: artifact and semantic regression tests
- `scripts/`: Lean audits, mutation checks, and reproducibility helpers
- `ctl-dogfood/`: machine-readable research provenance and historical state
- `legacy-archives/`: preserved historical material, not an active proof route

## Scope and non-claims

This snapshot does not claim:

- a foundation-level construction of smooth four-manifolds or Kirby calculus;
- that all explicit topology-to-graphical assumptions have completed expert
  review;
- equivalence with every historical Crane--Yetter state-sum convention;
- recertification of every legacy numerical experiment;
- a result for the full coefficient group proposed by Yetter;
- a no-go theorem in the non-simply-connected marked case;
- a non-semisimple extension.

## Citation

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). Until the
manuscript receives a permanent publication identifier, please cite both the
manuscript and the specific GitHub release used.
