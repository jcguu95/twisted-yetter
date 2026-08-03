import TwistedYetter.Kirby.Final.Proofs.CancellationMoves

/-!
# Frozen-frontend elementary local moves

This module assembles source-bound proofs for the constructors of
`ElementaryMove`.  It does not add an evaluator, a compiler, or a local
invariance assumption.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open CategoryTheory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

def elementaryMoveKind
    {source target : HomologicallyMarkedDiagram} :
    ElementaryMove source target → ElementaryMoveKind
  | .framedIsotopy .. => .framedIsotopy
  | .oneOverOne .. => .oneOverOne
  | .twoOverOne .. => .twoOverOne
  | .twoOverTwo .. => .twoOverTwo
  | .cancellation script .. => script.kind

/--
The three clean band-slide constructors are all instances of the same
source-bound attach--transport--detach theorem.
-/
theorem cleanBandElementaryMove_preserves_evaluation
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target)
    (isCleanBand :
      elementaryMoveKind move = .oneOverOne ∨
        elementaryMoveKind move = .twoOverOne ∨
        elementaryMoveKind move = .twoOverTwo)
    (sourceCycle : ThamTwoCycles source.primalBoundary) :
    evaluateCycle 𝒞η
        source.diagram source.cut source.primalBoundary sourceCycle =
      evaluateCycle 𝒞η
        target.diagram target.cut target.primalBoundary
          (move.homology.tham.mapCycle sourceCycle) := by
  cases move with
  | framedIsotopy =>
      simp [elementaryMoveKind] at isCleanBand
  | oneOverOne slide slideRealizes transportComplete _ _ homology _ =>
      exact cleanBandSlide_preserves_evaluation
        𝒞η slide slideRealizes transportComplete homology.tham sourceCycle
  | twoOverOne slide slideRealizes transportComplete _ _ homology _ =>
      exact cleanBandSlide_preserves_evaluation
        𝒞η slide slideRealizes transportComplete homology.tham sourceCycle
  | twoOverTwo slide slideRealizes transportComplete _ _ homology _ =>
      exact cleanBandSlide_preserves_evaluation
        𝒞η slide slideRealizes transportComplete homology.tham sourceCycle
  | cancellation script =>
      rcases script.kind_is_cancellation with
        equality | equality | equality | equality <;>
        simp [elementaryMoveKind, equality] at isCleanBand

/--
A certified framed isotopy preserves the exact frozen cycle evaluation.

The entrance boundary supplies only the framed-ribbon isotopy witness.  The
equality of interpreted morphisms is Shum coherence, and scalarization is the
same theorem used by the clean band-slide calculation.
-/
theorem framedIsotopy_preserves_evaluation
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : FramedIsotopyScript source.diagram target.diagram)
    (scriptRealizes :
      FramedIsotopyScriptRealizesFramedIsotopy script)
    (transport : ThamHandleChainTransport source target)
    (sourceCycle : ThamTwoCycles source.primalBoundary) :
    evaluateCycle 𝒞η
        source.diagram source.cut source.primalBoundary sourceCycle =
      evaluateCycle 𝒞η
        target.diagram target.cut target.primalBoundary
          (transport.mapCycle sourceCycle) := by
  have interpretation :=
    shum_framedRibbonCoherence
      (framedIsotopy_hasTypedGraphicalInterpretation
        𝒞η script scriptRealizes transport sourceCycle)
  rw [← normalizedCycleExpression_evaluation 𝒞η source sourceCycle]
  rw [← normalizedCycleExpression_evaluation
    𝒞η target (transport.mapCycle sourceCycle)]
  unfold canonicalRibbonGraphicalEvaluation
  exact congrArg 𝒞η.category.closedScalar interpretation

/--
All eight frozen elementary moves preserve the role-aware premodular
evaluation.  Every constructor is dispatched explicitly.
-/
theorem frozenFrontendLocalMoveInvariance
    (𝒞η : TwistedPremodularCategory K) :
    LocalMoveInvarianceStatement 𝒞η := by
  intro source target move sourceCycle
  cases move with
  | framedIsotopy script scriptRealizes homology _ =>
      exact framedIsotopy_preserves_evaluation
        𝒞η script scriptRealizes homology.tham sourceCycle
  | oneOverOne slide slideRealizes transportComplete _ _ homology _ =>
      exact cleanBandSlide_preserves_evaluation
        𝒞η slide slideRealizes transportComplete homology.tham sourceCycle
  | twoOverOne slide slideRealizes transportComplete _ _ homology _ =>
      exact cleanBandSlide_preserves_evaluation
        𝒞η slide slideRealizes transportComplete homology.tham sourceCycle
  | twoOverTwo slide slideRealizes transportComplete _ _ homology _ =>
      exact cleanBandSlide_preserves_evaluation
        𝒞η slide slideRealizes transportComplete homology.tham sourceCycle
  | cancellation script homology normalForm _ =>
      cases normalForm with
      | oneTwoBirth kind coordinates coordinateBinding normalForm =>
          exact oneTwoBirth_preserves_evaluation
            𝒞η script kind homology coordinates coordinateBinding
              normalForm sourceCycle
      | oneTwoDeath kind coordinates coordinateBinding normalForm =>
          exact oneTwoDeath_preserves_evaluation
            𝒞η script kind homology coordinates coordinateBinding
              normalForm sourceCycle
      | twoThreeBirth kind coordinates coordinateBinding normalForm =>
          exact twoThreeBirth_preserves_evaluation
            𝒞η script kind homology coordinates coordinateBinding
              normalForm sourceCycle
      | twoThreeDeath kind coordinates coordinateBinding normalForm =>
          exact twoThreeDeath_preserves_evaluation
            𝒞η script kind homology coordinates coordinateBinding
              normalForm sourceCycle

end

end TwistedYetter.Kirby.Final.Proofs
