import TwistedYetter.Kirby.Final.Semantics.Independent.Algebra
import TwistedYetter.Kirby.Final.Semantics.Independent.Diagram
import TwistedYetter.Kirby.Final.Semantics.Independent.Homology
import TwistedYetter.Kirby.Final.Semantics.Independent.Moves
import TwistedYetter.Kirby.Final.Semantics.Independent.Graphical
import TwistedYetter.Kirby.Final.Semantics.Independent.Evaluator
import TwistedYetter.Kirby.Final.Semantics.Independent.Invariant
import TwistedYetter.Kirby.Final.Semantics.Independent.EntranceAxioms

/-!
# Independent semantics: unique entry

This is the only public import for the normative human semantic
specification.  Its topology-side input starts at
`CombinatorialSpecialKirbyDiagram`.

The external names use ordinary Kirby calculus (`dotted = primal 1-handle`,
`framed = primal 2-handle`).  The evaluator follows Tham, Definition 5.11 on
the turned-over decomposition (`1 ↔ 3`, `2 ↔ 2`).  This explicit conversion is
only a convention alignment; it does not assert that either convention is
intrinsically preferred or change the intended invariant.

Dependency order:

`Algebra → Diagram → Homology → Moves → Graphical → Evaluator → Invariant
→ EntranceAxioms`.

`EntranceAxioms` contains the global manifold, dotted-disk, turnover, and
category-literature boundaries.  Four move-local, category-neutral topology
predicates are declared next to the move grammar in `Moves`, so their proof
arguments remain visible in every `ElementaryMove` constructor.  Three
additional clean attach/finite transport/detach interpretation boundaries are
declared individually in `EntranceAxioms`.  The complete list of twenty-one
explicit axioms is recorded in
`explicit-trust-boundary-v1.json`.

Domain-defining category laws remain visible in `Algebra`; combinatorial
certificates in the other semantic modules must use transparent propositions.
Neither kind is allowed to hide evaluator equality, representative
independence, or local-move invariance.

Implementation bridges, legacy evaluators, computation code, axiom audits,
and conformance checks are intentionally outside this entry.  In particular,
this import closure must not contain an existing presentation, evaluator,
move compiler, or comparison bridge.
-/

-- semantic-freeze-padding: 878
