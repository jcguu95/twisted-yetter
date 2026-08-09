import TwistedYetter.CategoryTheory.Premodular.Bundled
import TwistedYetter.Kirby.Final.Semantics.Independent.KirbyDiagram
import TwistedYetter.Kirby.Final.Semantics.Independent.CutOpen
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
`SpecialKirbyDiagram`.

The external names use ordinary Kirby calculus (`dotted = primal 1-handle`,
`framed = primal 2-handle`).  The evaluator follows Tham, Definition 5.11 on
the turned-over decomposition (`1 ↔ 3`, `2 ↔ 2`).  This explicit conversion is
only a convention alignment; it does not assert that either convention is
intrinsically preferred or change the intended invariant.

Dependency order:

`Category → KirbyDiagram → CutOpen → Homology → Moves → Graphical →
Evaluator → Invariant → EntranceAxioms`.

`EntranceAxioms` contains the global manifold, dotted-disk, turnover, and
category-literature boundaries.  Four move-local, category-neutral topology
predicates are declared next to the move grammar in `Moves`, so their proof
arguments remain visible in every `ElementaryMove` constructor.  Three
additional clean attach/finite transport/detach interpretation boundaries are
declared individually in `EntranceAxioms`.  The dotted-handle boundary is an
inbound-to-outbound incidence movie: puncture direction selects only the side
of that morphism, never `X` versus `X*` and never a character exponent.

The dotted-collar topology-to-graphical boundary is the single explicit
normal-form axiom `standardDottedCollarIncidenceNormalForm`; the former
intrinsic cut/regluing witness route is not part of this import closure.  The
signed incidence/handle-boundary identification is proved in `Homology`; it
is not an axiom.
`explicit-trust-boundary-v1.json` predates the corrected dotted-incidence
boundary and is historical only.  The rebuilt downstream compiler, final
route, kernel axiom closure, and source red-team result are recorded in
`explicit-trust-boundary-v15.json`.

Domain-defining category laws remain visible in the reusable category library;
combinatorial certificates in the semantic modules use transparent propositions.
Neither kind is allowed to hide evaluator equality, representative
independence, or local-move invariance.

Implementation bridges, legacy evaluators, computation code, axiom audits,
and conformance checks are intentionally outside this entry.  In particular,
this import closure must not contain an existing presentation, evaluator,
move compiler, or comparison bridge.
-/

-- semantic-freeze-padding: 14953
