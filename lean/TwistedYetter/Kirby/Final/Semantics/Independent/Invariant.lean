import TwistedYetter.Kirby.Final.Semantics.Independent.Evaluator
import TwistedYetter.Kirby.Final.Semantics.Independent.Moves

/-!
# Independent semantics: public invariant

This file states the topology boundary and the final theorem target.  It does
not assert the target as an axiom and contains no legacy compatibility claim.
-/

namespace TwistedYetter.Semantics.Independent

universe uK

/--
An opaque human-level type of closed oriented smooth four-manifolds.  The
independent evaluator does not construct values of this type from raw planar
data.
-/
opaque ClosedOrientedSmoothFourManifold : Type

/-- Integral second homology of the manifold, not a fixed auxiliary group. -/
opaque ManifoldH₂ :
  ClosedOrientedSmoothFourManifold → Type

axiom manifoldH₂_addCommGroup
    (X : ClosedOrientedSmoothFourManifold) :
    AddCommGroup (ManifoldH₂ X)

attribute [instance] manifoldH₂_addCommGroup

/--
Category-neutral realization relation.  It only says that a combinatorial
special Kirby diagram presents the manifold.
-/
opaque DiagramRealizes :
  CombinatorialSpecialKirbyDiagram →
  ClosedOrientedSmoothFourManifold →
  Prop

opaque MoveRealizesStandardKirbyMove :
  {source target : HomologicallyMarkedDiagram} →
  ElementaryMove source target →
  Prop

structure MarkedRealization
    (X : ClosedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) where
  markedDiagram : HomologicallyMarkedDiagram
  realizes : DiagramRealizes markedDiagram.diagram X
  homologyComparison :
    PrimalKirbyH₂ markedDiagram.primalBoundary ≃+ ManifoldH₂ X
  markingMatches :
    homologyComparison markedDiagram.alpha = alpha

/--
The classical topology boundary is split into visible pieces.  None may
mention a category, character, graphical evaluation, or scalar equality.
-/
structure ClassicalKirbyTopologyBoundary where
  presentationExistence :
    ∀ (X : ClosedOrientedSmoothFourManifold) (alpha : ManifoldH₂ X),
      Nonempty (MarkedRealization X alpha)
  localMoveRealization :
    ∀ {source target : HomologicallyMarkedDiagram},
      (move : ElementaryMove source target) →
      MoveRealizesStandardKirbyMove move
  diffeomorphismTransport :
    (X Y : ClosedOrientedSmoothFourManifold) →
    Type
  inducedH₂ :
    ∀ {X Y : ClosedOrientedSmoothFourManifold},
      diffeomorphismTransport X Y →
      ManifoldH₂ X ≃+ ManifoldH₂ Y
  /--
  Diffeomorphism-aware marked Kirby--Cerf completeness.

  For a specified oriented diffeomorphism `f : X → Y`, the exact realization
  of `(X, alpha)` and the exact realization of `(Y, f₀ alpha)` are connected by
  a finite movie of the eight marked elementary moves.  This is a
  category-neutral topology boundary: it contains no character, graphical
  evaluator, or scalar equality.
  -/
  markedKirbyCerfCompleteness :
    ∀ {X Y : ClosedOrientedSmoothFourManifold}
      (f : diffeomorphismTransport X Y)
      (alpha : ManifoldH₂ X)
      (left : MarkedRealization X alpha)
      (right : MarkedRealization Y (inducedH₂ f alpha)),
      Nonempty (KirbyMovie left.markedDiagram right.markedDiagram)

/--
The independent local-move obligation.  It quantifies over all eight move
constructors and therefore cannot disappear into a compiler axiom.
-/
def LocalMoveInvarianceStatement
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation 𝒞η.category)
    (compiler : RoleAwareGraphCompiler 𝒞η)
    (normalization : ThamDefinition511Normalization K) : Prop :=
  ∀ {source target : HomologicallyMarkedDiagram},
    (move : ElementaryMove source target) →
    ∀ sourceCycle : ThamTwoCycles source.turnedOver,
      evaluateCycle 𝒞η graphical compiler normalization
          source.diagram source.primalBoundary source.turnedOver sourceCycle =
        evaluateCycle 𝒞η graphical compiler normalization
          target.diagram target.primalBoundary target.turnedOver
            (move.homology.tham.mapCycle sourceCycle)

noncomputable def evaluateMarking
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation 𝒞η.category)
    (compiler : RoleAwareGraphCompiler 𝒞η)
    (normalization : ThamDefinition511Normalization K)
    (marked : HomologicallyMarkedDiagram) : K :=
  evaluateCycle 𝒞η graphical compiler normalization
    marked.diagram marked.primalBoundary marked.turnedOver
    (Quotient.out marked.thamAlpha)

/--
The final public mathematical target.  It is a proposition to prove after
representative independence, all local moves, and classical descent have
been supplied.
-/
def TwistedYetterDiffeomorphismInvarianceTarget
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation 𝒞η.category)
    (compiler : RoleAwareGraphCompiler 𝒞η)
    (normalization : ThamDefinition511Normalization K)
    (topology : ClassicalKirbyTopologyBoundary) : Prop :=
  ∀ (X Y : ClosedOrientedSmoothFourManifold)
    (f : topology.diffeomorphismTransport X Y)
    (alpha : ManifoldH₂ X)
    (left : MarkedRealization X alpha)
    (right :
      MarkedRealization Y (topology.inducedH₂ f alpha)),
    evaluateMarking 𝒞η graphical compiler normalization
        left.markedDiagram =
      evaluateMarking 𝒞η graphical compiler normalization
        right.markedDiagram

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 655
