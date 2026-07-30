import TwistedYetter.Kirby.Final.Semantics.Independent.Evaluator
import TwistedYetter.Kirby.Final.Semantics.Independent.Moves

/-!
# Independent semantics: invariant vocabulary and obligations

This file contains only the role-aware evaluation and the propositions that
later proofs must establish.  Smooth-manifold vocabulary is introduced by
three explicit foundational axioms in `EntranceAxioms`; it is never hidden in
opaque constants or proof-bearing packages.
-/

namespace TwistedYetter.Semantics.Independent

universe uK

/--
The independent local-move obligation.  It quantifies over all eight move
constructors and therefore cannot disappear into a compiler axiom.
-/
def LocalMoveInvarianceStatement
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K) : Prop :=
  ∀ {source target : HomologicallyMarkedDiagram},
    (move : ElementaryMove source target) →
    ∀ sourceCycle : ThamTwoCycles source.turnedOver,
      evaluateCycle 𝒞η
          source.diagram source.primalBoundary source.turnedOver sourceCycle =
        evaluateCycle 𝒞η
          target.diagram target.primalBoundary target.turnedOver
            (move.homology.tham.mapCycle sourceCycle)

noncomputable def evaluateMarking
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (marked : HomologicallyMarkedDiagram) : K :=
  evaluateCycle 𝒞η
    marked.diagram marked.primalBoundary marked.turnedOver
    (Quotient.out marked.thamAlpha)

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 618
