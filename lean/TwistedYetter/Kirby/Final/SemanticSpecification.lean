import TwistedYetter.Kirby.Final.Semantics.HandleChain
import TwistedYetter.Kirby.Final.Semantics.Presentation
import TwistedYetter.Kirby.Final.Semantics.BandSlide
import TwistedYetter.Kirby.Final.Semantics.Cancellation
import TwistedYetter.Kirby.Final.Semantics.FramedIsotopy
import TwistedYetter.Kirby.Final.Semantics.SlideMoves
import TwistedYetter.Kirby.Final.Semantics.CancellationMoves
import TwistedYetter.Kirby.Final.Semantics.MoveAssembly
import TwistedYetter.Kirby.Final.Semantics.AlgebraicInput
import TwistedYetter.Kirby.Final.Semantics.TopologicalInput
import TwistedYetter.Kirby.Final.Semantics.Evaluator
import TwistedYetter.Kirby.Final.Semantics.Descent

/-!
# Unified semantic specification entry

This is the only public entry for auditing the intended mathematics. It
defines nothing; it points to twelve reviewable layers in dependency order:

1. `Semantics/HandleChain.lean`: integral handle counts, complexes, and H₂.
2. `Semantics/Presentation.lean`: exact diagram roles and local replacement.
3. `Semantics/BandSlide.lean`: clean attach--transport--detach geometry.
4. `Semantics/Cancellation.lean`: exact 1--2 and 2--3 cancellation windows.
5. `Semantics/FramedIsotopy.lean`: finite primitive isotopy grammar.
6. `Semantics/SlideMoves.lean`: exact 1/1, 2/1, and 2/2 constructors.
7. `Semantics/CancellationMoves.lean`: exact 1--2 and 2--3 birth/death constructors.
8. `Semantics/MoveAssembly.lean`: exhaustive eight cases and induced H₂ transport.
9. `Semantics/AlgebraicInput.lean`: premodular category and character.
10. `Semantics/TopologicalInput.lean`: manifolds, realization, and Kirby--Cerf data.
11. `Semantics/Evaluator.lean`: the exact role-aware finite-sum evaluator.
12. `Semantics/Descent.lean`: finite-movie induction and final invariant theorem.

The compatibility facades `SemanticHandleChain.lean` and
`SemanticEightMoves.lean`, together with `Semantics/Moves.lean` and
`Semantics/PublicInvariant.lean`, remain import-only and contain no definitions.
-/
