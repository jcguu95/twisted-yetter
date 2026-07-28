import TwistedYetter.Kirby.TwoOverTwoFusionChannel
import TwistedYetter.Kirby.TwoOverTwoSourceFreeFactorization

/-!
# Exact positive 2/2 endpoints with explicit fusion channels

This module inserts the proved `d_z`-weighted `(z, μ)` resolution into the
actual shared source and target exteriors.  No endpoint evaluator equality is
assumed here.
-/

namespace TwistedYetter.Kirby.TwoOverTwoPositiveEndpointChannel

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.ModularVacuumProjector
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe
open TwistedYetter.Kirby.TwoOverTwoFusionChannel
open TwistedYetter.Kirby.TwoOverTwoSourceFreeFactorization

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance twoOverTwoPositiveEndpointRightRigid : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/-- Source exponent on the moving 2-handle. -/
noncomputable def sourceMovingExponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) : ℤ :=
  source.cycleComponentExponent sourceCycle
    (componentAt source.topology.formal
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).resolvedComponents.slidingSourceIndex)

/-- Target exponent on the transported moving 2-handle. -/
noncomputable def targetMovingExponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) : ℤ :=
  let request :=
    CanonicalSourceBoundSlideMovie.Request.twoOverTwo metadata countsSound
  target.cycleComponentExponent (request.targetCycle sourceCycle)
    (componentAt target.topology.formal
      request.resolvedComponents.slidingTargetIndex)

/-- The handle-chain transport preserves the exponent on the moving ID. -/
theorem targetMovingExponent_eq_sourceMovingExponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    targetMovingExponent metadata countsSound sourceCycle =
      sourceMovingExponent metadata countsSound sourceCycle := by
  let request :=
    CanonicalSourceBoundSlideMovie.Request.twoOverTwo metadata countsSound
  have exponentSound :=
    (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoExponentTransport
      metadata countsSound sourceCycle).exponent_sound
      request.resolvedComponents.slidingTargetIndex
  simpa [
    targetMovingExponent,
    sourceMovingExponent,
    request,
    SourceBoundLocalMoveRecipe.ResolvedSlideComponentPair.slidingTargetIndex
  ] using exponentSound

/-- The handle-chain transport preserves the exponent on the stationary ID. -/
theorem targetStationaryExponent_eq_sourceStationaryExponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
        metadata countsSound sourceCycle =
      CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
        metadata countsSound sourceCycle := by
  let request :=
    CanonicalSourceBoundSlideMovie.Request.twoOverTwo metadata countsSound
  have exponentSound :=
    (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoExponentTransport
      metadata countsSound sourceCycle).exponent_sound
      request.resolvedComponents.stationaryTargetIndex
  simpa [
    CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent,
    CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent,
    request,
    SourceBoundLocalMoveRecipe.ResolvedSlideComponentPair.stationaryTargetIndex
  ] using exponentSound

/--
The exact source endpoint context: a coupon is inserted before the actual
source local piece, then the result is closed by the shared exterior.
-/
noncomputable def sourceEndpointContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :=
  CategoricalTangle.Context.compose
    (CategoricalTangle.Context.compRight
      ((standardSharedFreeWindow metadata countsSound).sourcePiece.interpret
        𝒞
        (source.labelOf 𝒞
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceLabeling
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel))))
    (sourceContext 𝒞 metadata countsSound remaining
      movingLabel stationaryLabel)

/--
The exact target endpoint context: the actual target local piece is followed
by the inserted coupon, then closed by the same shared exterior.
-/
noncomputable def targetEndpointContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :=
  CategoricalTangle.Context.compose
    (CategoricalTangle.Context.compLeft
      ((standardSharedFreeWindow metadata countsSound).targetPiece.interpret
        𝒞
        (target.labelOf 𝒞
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetLabeling
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).sameComponentChange
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel))))
    (targetContext 𝒞 metadata countsSound remaining
      movingLabel stationaryLabel)

/-- Plugging identity into the source endpoint context recovers the exact
source evaluator term, at the level of evaluation. -/
theorem sourceTerm_eval_eq_endpointIdentity
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    Diagram.eval C
        (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceTerm 𝒞
          (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).resolvedComponents
          remaining movingLabel stationaryLabel) =
      LinearContext.evalContextLinearMap (R := K)
        (sourceEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (𝟙 ((localBoundary metadata countsSound).interpret 𝒞
          (source.labelOf 𝒞
            (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceLabeling
              (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
                metadata countsSound).resolvedComponents
              remaining movingLabel stationaryLabel))).denote) := by
  rw [sourceTerm_eq_sharedContext_sourcePiece
    𝒞 metadata countsSound remaining movingLabel stationaryLabel]
  simp [sourceEndpointContext, LinearContext.evalContextLinearMap,
    CategoricalTangle.Context.plug, Diagram.eval]
  exact
    (LinearContext.evalContextLinearMap_diagram (R := K)
      (sourceContext 𝒞 metadata countsSound remaining
        movingLabel stationaryLabel)
      ((standardSharedFreeWindow metadata countsSound).sourcePiece.interpret
        𝒞
        (source.labelOf 𝒞
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceLabeling
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel)))).symm

/-- Plugging identity into the target endpoint context recovers the exact
target evaluator term, at the level of evaluation. -/
theorem targetTerm_eval_eq_endpointIdentity
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    Diagram.eval C
        (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetTerm 𝒞
          (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).sameComponentChange
          (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).resolvedComponents
          remaining movingLabel stationaryLabel) =
      LinearContext.evalContextLinearMap (R := K)
        (targetEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (𝟙 ((localBoundary metadata countsSound).interpret 𝒞
          (target.labelOf 𝒞
            (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetLabeling
              (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
                metadata countsSound).sameComponentChange
              (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
                metadata countsSound).resolvedComponents
              remaining movingLabel stationaryLabel))).denote) := by
  rw [targetTerm_eq_sharedContext_targetPiece
    𝒞 metadata countsSound remaining movingLabel stationaryLabel]
  simp [targetEndpointContext, LinearContext.evalContextLinearMap,
    CategoricalTangle.Context.plug, Diagram.eval]
  exact
    (LinearContext.evalContextLinearMap_diagram (R := K)
      (targetContext 𝒞 metadata countsSound remaining
        movingLabel stationaryLabel)
      ((standardSharedFreeWindow metadata countsSound).targetPiece.interpret
        𝒞
        (target.labelOf 𝒞
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetLabeling
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).sameComponentChange
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel)))).symm

/-- The exact source free boundary denotes `x ⊗ yᘁ`. -/
theorem sourceLocalObject_positive
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .positive)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    ((localBoundary metadata countsSound).interpret 𝒞
        (source.labelOf 𝒞
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceLabeling
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel))).denote =
      OrientedTensorObject 𝒞 movingLabel stationaryLabel := by
  have boundarySound :=
    congrArg (Boundary.denote C)
      (sourceLocalBoundary_interpret_positive
        𝒞 metadata countsSound orientationSound remaining
        movingLabel stationaryLabel)
  exact boundarySound

/-- The exact target free boundary denotes the same `x ⊗ yᘁ`. -/
theorem targetLocalObject_positive
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .positive)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    ((localBoundary metadata countsSound).interpret 𝒞
        (target.labelOf 𝒞
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetLabeling
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).sameComponentChange
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel))).denote =
      OrientedTensorObject 𝒞 movingLabel stationaryLabel := by
  have boundarySound :=
    congrArg (Boundary.denote C)
      (targetLocalBoundary_interpret_positive
        𝒞 metadata countsSound orientationSound remaining
        movingLabel stationaryLabel)
  exact boundarySound

/--
The full internal-channel identity holds inside the exact source exterior.
-/
theorem sourceChannelResolution
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .positive)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S)
    (exponent : ℤ) :
    ∑ channel : OrientedChannel 𝒞 movingLabel stationaryLabel,
        LinearContext.evalContextLinearMap (R := K)
          (sourceContext 𝒞 metadata countsSound remaining
            movingLabel stationaryLabel)
          (transportEndomorphism
            (sourceLocalObject_positive
              𝒞 metadata countsSound orientationSound remaining
              movingLabel stationaryLabel)
            (orientedChannelCouponMorphism
              𝒞 η movingLabel stationaryLabel exponent channel)) =
      LinearContext.evalContextLinearMap (R := K)
        (sourceContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (sourceLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (automorphismObjectPower η
            (OrientedTensorObject 𝒞 movingLabel stationaryLabel)
            exponent)) :=
  sum_orientedChannelCouponMorphism_inBoundaryContext
    𝒞 insertionLaw η movingLabel stationaryLabel exponent
    (sourceLocalObject_positive
      𝒞 metadata countsSound orientationSound remaining
      movingLabel stationaryLabel)
    (sourceContext 𝒞 metadata countsSound remaining
      movingLabel stationaryLabel)

/--
The same full internal-channel identity holds inside the exact target
exterior.
-/
theorem targetChannelResolution
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .positive)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S)
    (exponent : ℤ) :
    ∑ channel : OrientedChannel 𝒞 movingLabel stationaryLabel,
        LinearContext.evalContextLinearMap (R := K)
          (targetContext 𝒞 metadata countsSound remaining
            movingLabel stationaryLabel)
          (transportEndomorphism
            (targetLocalObject_positive
              𝒞 metadata countsSound orientationSound remaining
              movingLabel stationaryLabel)
            (orientedChannelCouponMorphism
              𝒞 η movingLabel stationaryLabel exponent channel)) =
      LinearContext.evalContextLinearMap (R := K)
        (targetContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (targetLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (automorphismObjectPower η
            (OrientedTensorObject 𝒞 movingLabel stationaryLabel)
            exponent)) :=
  sum_orientedChannelCouponMorphism_inBoundaryContext
    𝒞 insertionLaw η movingLabel stationaryLabel exponent
    (targetLocalObject_positive
      𝒞 metadata countsSound orientationSound remaining
      movingLabel stationaryLabel)
    (targetContext 𝒞 metadata countsSound remaining
      movingLabel stationaryLabel)

/--
The exact source exterior with two independent character exponents.
-/
theorem sourceUnequalExponentChannelResolution
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .positive)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S)
    (movingExponent stationaryExponent : ℤ) :
    ∑ channel : OrientedChannel 𝒞 movingLabel stationaryLabel,
        LinearContext.evalContextLinearMap (R := K)
          (sourceContext 𝒞 metadata countsSound remaining
            movingLabel stationaryLabel)
          (transportEndomorphism
            (sourceLocalObject_positive
              𝒞 metadata countsSound orientationSound remaining
              movingLabel stationaryLabel)
            (unequalExponentChannelMorphism
              𝒞 η movingLabel stationaryLabel
              movingExponent stationaryExponent channel)) =
      LinearContext.evalContextLinearMap (R := K)
        (sourceContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (sourceLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (orientedCharacterCoupon
            𝒞 η movingLabel stationaryLabel
            movingExponent stationaryExponent)) :=
  sum_unequalExponentChannelMorphism_inBoundaryContext
    𝒞 insertionLaw η movingLabel stationaryLabel
    movingExponent stationaryExponent
    (sourceLocalObject_positive
      𝒞 metadata countsSound orientationSound remaining
      movingLabel stationaryLabel)
    (sourceContext 𝒞 metadata countsSound remaining
      movingLabel stationaryLabel)

/--
The exact target exterior with two independent character exponents.
-/
theorem targetUnequalExponentChannelResolution
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .positive)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S)
    (movingExponent stationaryExponent : ℤ) :
    ∑ channel : OrientedChannel 𝒞 movingLabel stationaryLabel,
        LinearContext.evalContextLinearMap (R := K)
          (targetContext 𝒞 metadata countsSound remaining
            movingLabel stationaryLabel)
          (transportEndomorphism
            (targetLocalObject_positive
              𝒞 metadata countsSound orientationSound remaining
              movingLabel stationaryLabel)
            (unequalExponentChannelMorphism
              𝒞 η movingLabel stationaryLabel
              movingExponent stationaryExponent channel)) =
      LinearContext.evalContextLinearMap (R := K)
        (targetContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (targetLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (orientedCharacterCoupon
            𝒞 η movingLabel stationaryLabel
            movingExponent stationaryExponent)) :=
  sum_unequalExponentChannelMorphism_inBoundaryContext
    𝒞 insertionLaw η movingLabel stationaryLabel
    movingExponent stationaryExponent
    (targetLocalObject_positive
      𝒞 metadata countsSound orientationSound remaining
      movingLabel stationaryLabel)
    (targetContext 𝒞 metadata countsSound remaining
      movingLabel stationaryLabel)

/--
The positive source endpoint with the actual two exponents read from the
handle-chain cycle.
-/
theorem sourceGlobalPositiveEndpointResolution
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .positive)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    ∑ channel : OrientedChannel 𝒞 movingLabel stationaryLabel,
        LinearContext.evalContextLinearMap (R := K)
          (sourceContext 𝒞 metadata countsSound remaining
            movingLabel stationaryLabel)
          (transportEndomorphism
            (sourceLocalObject_positive
              𝒞 metadata countsSound orientationSound remaining
              movingLabel stationaryLabel)
            (unequalExponentChannelMorphism
              𝒞 η movingLabel stationaryLabel
              (sourceMovingExponent metadata countsSound sourceCycle)
              (-CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
                metadata countsSound sourceCycle)
              channel)) =
      LinearContext.evalContextLinearMap (R := K)
        (sourceContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (sourceLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (globalPositiveEndpointCoupon
            𝒞 η movingLabel stationaryLabel
            (sourceMovingExponent metadata countsSound sourceCycle)
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
              metadata countsSound sourceCycle))) := by
  exact sum_unequalExponentChannelMorphism_inBoundaryContext
    𝒞 insertionLaw η movingLabel stationaryLabel
    (sourceMovingExponent metadata countsSound sourceCycle)
    (-CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
      metadata countsSound sourceCycle)
    (sourceLocalObject_positive
      𝒞 metadata countsSound orientationSound remaining
      movingLabel stationaryLabel)
    (sourceContext 𝒞 metadata countsSound remaining
      movingLabel stationaryLabel)

/--
The positive target endpoint with exponents read from the transported cycle.
-/
theorem targetGlobalPositiveEndpointResolution
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .positive)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    ∑ channel : OrientedChannel 𝒞 movingLabel stationaryLabel,
        LinearContext.evalContextLinearMap (R := K)
          (targetContext 𝒞 metadata countsSound remaining
            movingLabel stationaryLabel)
          (transportEndomorphism
            (targetLocalObject_positive
              𝒞 metadata countsSound orientationSound remaining
              movingLabel stationaryLabel)
            (unequalExponentChannelMorphism
              𝒞 η movingLabel stationaryLabel
              (targetMovingExponent metadata countsSound sourceCycle)
              (-CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
                metadata countsSound sourceCycle)
              channel)) =
      LinearContext.evalContextLinearMap (R := K)
        (targetContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (targetLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (globalPositiveEndpointCoupon
            𝒞 η movingLabel stationaryLabel
            (targetMovingExponent metadata countsSound sourceCycle)
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
              metadata countsSound sourceCycle))) := by
  exact sum_unequalExponentChannelMorphism_inBoundaryContext
    𝒞 insertionLaw η movingLabel stationaryLabel
    (targetMovingExponent metadata countsSound sourceCycle)
    (-CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
      metadata countsSound sourceCycle)
    (targetLocalObject_positive
      𝒞 metadata countsSound orientationSound remaining
      movingLabel stationaryLabel)
    (targetContext 𝒞 metadata countsSound remaining
      movingLabel stationaryLabel)

/--
The full positive source endpoint, including the actual source local piece,
admits the explicit arbitrary-exponent channel resolution.
-/
theorem sourceExactEndpointChannelResolution
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .positive)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    ∑ channel : OrientedChannel 𝒞 movingLabel stationaryLabel,
        LinearContext.evalContextLinearMap (R := K)
          (sourceEndpointContext 𝒞 metadata countsSound remaining
            movingLabel stationaryLabel)
          (transportEndomorphism
            (sourceLocalObject_positive
              𝒞 metadata countsSound orientationSound remaining
              movingLabel stationaryLabel)
            (unequalExponentChannelMorphism
              𝒞 η movingLabel stationaryLabel
              (sourceMovingExponent metadata countsSound sourceCycle)
              (-CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
                metadata countsSound sourceCycle)
              channel)) =
      LinearContext.evalContextLinearMap (R := K)
        (sourceEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (sourceLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (globalPositiveEndpointCoupon
            𝒞 η movingLabel stationaryLabel
            (sourceMovingExponent metadata countsSound sourceCycle)
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
              metadata countsSound sourceCycle))) := by
  exact sum_unequalExponentChannelMorphism_inBoundaryContext
    𝒞 insertionLaw η movingLabel stationaryLabel
    (sourceMovingExponent metadata countsSound sourceCycle)
    (-CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
      metadata countsSound sourceCycle)
    (sourceLocalObject_positive
      𝒞 metadata countsSound orientationSound remaining
      movingLabel stationaryLabel)
    (sourceEndpointContext 𝒞 metadata countsSound remaining
      movingLabel stationaryLabel)

/--
The full positive target endpoint, including the actual target local piece,
admits the corresponding explicit channel resolution.
-/
theorem targetExactEndpointChannelResolution
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .positive)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    ∑ channel : OrientedChannel 𝒞 movingLabel stationaryLabel,
        LinearContext.evalContextLinearMap (R := K)
          (targetEndpointContext 𝒞 metadata countsSound remaining
            movingLabel stationaryLabel)
          (transportEndomorphism
            (targetLocalObject_positive
              𝒞 metadata countsSound orientationSound remaining
              movingLabel stationaryLabel)
            (unequalExponentChannelMorphism
              𝒞 η movingLabel stationaryLabel
              (targetMovingExponent metadata countsSound sourceCycle)
              (-CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
                metadata countsSound sourceCycle)
              channel)) =
      LinearContext.evalContextLinearMap (R := K)
        (targetEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (targetLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (globalPositiveEndpointCoupon
            𝒞 η movingLabel stationaryLabel
            (targetMovingExponent metadata countsSound sourceCycle)
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
              metadata countsSound sourceCycle))) := by
  exact sum_unequalExponentChannelMorphism_inBoundaryContext
    𝒞 insertionLaw η movingLabel stationaryLabel
    (targetMovingExponent metadata countsSound sourceCycle)
    (-CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
      metadata countsSound sourceCycle)
    (targetLocalObject_positive
      𝒞 metadata countsSound orientationSound remaining
      movingLabel stationaryLabel)
    (targetEndpointContext 𝒞 metadata countsSound remaining
      movingLabel stationaryLabel)

end TwistedYetter.Kirby.TwoOverTwoPositiveEndpointChannel
