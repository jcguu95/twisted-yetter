import TwistedYetter.Kirby.Final.Semantics.Independent.Entry

/-!
# Frozen-frontend clean band-slide calculation

This file turns the three explicit graphical/topological entrance axioms into
an equality of the canonical frozen-frontend evaluator.  The axioms identify
clean attachment, finite coupon transport, and clean detachment at the typed
ribbon-expression level.  Scalar evaluation equality is derived here.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
Scalarizing the normalized closed expression gives exactly the frozen
cycle-level evaluator.
-/
theorem normalizedCycleExpression_evaluation
    (𝒞η : TwistedPremodularCategory K)
    (marked : HomologicallyMarkedDiagram)
    (cycle : ThamTwoCycles marked.primalBoundary) :
    canonicalRibbonGraphicalEvaluation 𝒞η.category
        (normalizedCycleExpression 𝒞η marked cycle) =
      evaluateCycle 𝒞η
        marked.diagram marked.primalBoundary cycle := by
  classical
  unfold normalizedCycleExpression
  unfold canonicalRibbonGraphicalEvaluation
  unfold evaluateCycle
  unfold rawCycleSum
  unfold PremodularFusionCategory.closedScalar
  simp only [RibbonExpression.interpret]
  simp only [map_smul, map_sum]
  simp only [canonicalRibbonGraphicalEvaluation,
    PremodularFusionCategory.closedScalar]
  simp only [smul_eq_mul]

/--
Any clean band slide whose finite route is certified preserves the exact
frozen-frontend cycle evaluation.

The proof has exactly three mathematical steps: attach, finite naturality
transport, and detach.
-/
theorem cleanBandSlide_preserves_evaluation
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (slide : CleanBandSlide source.diagram target.diagram)
    (slideRealizes :
      CleanBandSlideRealizesStandardKirbySlide slide)
    (transportComplete :
      FiniteCouponTransportRealizesCompletePath
        slide.decomposition.transport)
    (transport : ThamHandleChainTransport source target)
    (sourceCycle : ThamTwoCycles source.primalBoundary) :
    evaluateCycle 𝒞η
        source.diagram source.primalBoundary sourceCycle =
      evaluateCycle 𝒞η
        target.diagram target.primalBoundary
          (transport.mapCycle sourceCycle) := by
  obtain ⟨attachNormalForm, attach⟩ :=
    cleanAttach_hasStandardGraphicalInterpretation
      𝒞η slide slideRealizes sourceCycle
  obtain ⟨detachNormalForm, detach⟩ :=
    cleanDetach_hasStandardGraphicalInterpretation
      𝒞η slide slideRealizes transport sourceCycle
  have attachInterpretation :
      (normalizedCycleExpression 𝒞η source sourceCycle).interpret =
        attachNormalForm.identityStage.interpret :=
    shum_framedRibbonCoherence attach
  have attachResolution :
      attachNormalForm.identityStage.interpret =
        attachNormalForm.resolvedStage.interpret := by
    apply
      RibbonExpressionContext.plug_interpret_eq_of_interpret_eq
        attachNormalForm.context
    exact
      (fusionResolutionExpression_interpret
        𝒞η.category attachNormalForm.movingLabel
          attachNormalForm.stationaryLabel).symm
  have finiteTransport :
      attachNormalForm.resolvedStage.interpret =
        detachNormalForm.resolvedStage.interpret :=
    (finiteCouponTransport_hasTypedGraphicalDerivation
      𝒞η slide slideRealizes transportComplete sourceCycle
        attachNormalForm detachNormalForm).interpret_eq
  have detachResolution :
      detachNormalForm.resolvedStage.interpret =
        detachNormalForm.identityStage.interpret := by
    apply
      RibbonExpressionContext.plug_interpret_eq_of_interpret_eq
        detachNormalForm.context
    exact
      fusionResolutionExpression_interpret
        𝒞η.category detachNormalForm.movingLabel
          detachNormalForm.stationaryLabel
  have detachInterpretation :
      detachNormalForm.identityStage.interpret =
        (normalizedCycleExpression 𝒞η target
          (transport.mapCycle sourceCycle)).interpret :=
    shum_framedRibbonCoherence detach
  rw [← normalizedCycleExpression_evaluation 𝒞η source sourceCycle]
  rw [← normalizedCycleExpression_evaluation
    𝒞η target (transport.mapCycle sourceCycle)]
  unfold canonicalRibbonGraphicalEvaluation
  rw [attachInterpretation, attachResolution, finiteTransport,
    detachResolution, detachInterpretation]

end

end TwistedYetter.Kirby.Final.Proofs
