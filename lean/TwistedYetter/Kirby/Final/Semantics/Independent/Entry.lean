import TwistedYetter.Kirby.Final.Semantics.Independent.Algebra
import TwistedYetter.Kirby.Final.Semantics.Independent.Diagram
import TwistedYetter.Kirby.Final.Semantics.Independent.Homology
import TwistedYetter.Kirby.Final.Semantics.Independent.Moves
import TwistedYetter.Kirby.Final.Semantics.Independent.Graphical
import TwistedYetter.Kirby.Final.Semantics.Independent.Evaluator
import TwistedYetter.Kirby.Final.Semantics.Independent.Invariant

/-!
# Independent semantics: unique entry

This is the only public import for the frozen human semantic specification.

Dependency order:

`Algebra → Diagram → Homology → Moves → Graphical → Evaluator → Invariant`.

Implementation bridges, legacy evaluators, computation code, axiom audits,
and conformance checks are intentionally outside this entry.
-/

-- sha256-padding: 1237
