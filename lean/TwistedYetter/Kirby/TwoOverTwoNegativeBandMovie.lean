import TwistedYetter.Kirby.TwoOverTwoBandMovie

/-!
# Negative source-bound Bärenz--Barrett band movie

The negative local boundary is `x ⊗ y`, rather than the positive
`x ⊗ yᘁ`.  This file keeps that distinction explicit and proves the
character-decorated endpoint equality from a character-free band movie.
-/

namespace TwistedYetter.Kirby.TwoOverTwoNegativeBandMovie

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe
open TwistedYetter.Kirby.TwoOverTwoFusionChannel
open TwistedYetter.Kirby.TwoOverTwoPositiveEndpointChannel
open TwistedYetter.Kirby.TwoOverTwoSourceFreeFactorization

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance twoOverTwoNegativeBandMovieRightRigid : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/-- The exact negative source hole denotes `x ⊗ y`. -/
theorem sourceLocalObject_negative
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .negative)
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
      TensorObject 𝒞.toFusionCategoryData movingLabel stationaryLabel := by
  exact congrArg (Boundary.denote C)
    (sourceLocalBoundary_interpret_negative
      𝒞 metadata countsSound orientationSound remaining
      movingLabel stationaryLabel)

/-- The exact negative target hole denotes the same `x ⊗ y`. -/
theorem targetLocalObject_negative
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .negative)
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
      TensorObject 𝒞.toFusionCategoryData movingLabel stationaryLabel := by
  exact congrArg (Boundary.denote C)
    (targetLocalBoundary_interpret_negative
      𝒞 metadata countsSound orientationSound remaining
      movingLabel stationaryLabel)

/--
Negative Bärenz--Barrett band movie, bound to the exact serialized endpoints.
It is category-neutral with respect to twisting: `f` is arbitrary and the
statement mentions no character, exponent, fusion label, or scalar.
-/
axiom baerenzBarrett_negativeBandMovie
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .negative)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S)
    (f :
      TensorObject 𝒞.toFusionCategoryData movingLabel stationaryLabel ⟶
        TensorObject 𝒞.toFusionCategoryData movingLabel stationaryLabel) :
    LinearContext.evalContextLinearMap (R := K)
        (sourceEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (sourceLocalObject_negative
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          f) =
      LinearContext.evalContextLinearMap (R := K)
        (targetEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (targetLocalObject_negative
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          f)

/--
The exact negative character endpoint is invariant.  Target exponents are
first proved equal to their transported source values; the literature input
is then instantiated with the actual pair of character coupons.
-/
theorem negativeBandMovie_globalCharacterEndpoint
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .negative)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    LinearContext.evalContextLinearMap (R := K)
        (sourceEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (sourceLocalObject_negative
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (tensorCharacterCoupon 𝒞.toFusionCategoryData η
            movingLabel stationaryLabel
            (sourceMovingExponent metadata countsSound sourceCycle)
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
              metadata countsSound sourceCycle))) =
      LinearContext.evalContextLinearMap (R := K)
        (targetEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (targetLocalObject_negative
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (tensorCharacterCoupon 𝒞.toFusionCategoryData η
            movingLabel stationaryLabel
            (targetMovingExponent metadata countsSound sourceCycle)
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
              metadata countsSound sourceCycle))) := by
  rw [
    targetMovingExponent_eq_sourceMovingExponent
      metadata countsSound sourceCycle,
    targetStationaryExponent_eq_sourceStationaryExponent
      metadata countsSound sourceCycle
  ]
  exact baerenzBarrett_negativeBandMovie
    𝒞 metadata countsSound orientationSound remaining
    movingLabel stationaryLabel
    (tensorCharacterCoupon 𝒞.toFusionCategoryData η
      movingLabel stationaryLabel
      (sourceMovingExponent metadata countsSound sourceCycle)
      (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
        metadata countsSound sourceCycle))

/-- The negative source character endpoint is its scalar times the real term. -/
theorem sourceNegativeCharacterEndpoint_eq_scalar_smul_term
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .negative)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    LinearContext.evalContextLinearMap (R := K)
        (sourceEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (sourceLocalObject_negative
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (tensorCharacterCoupon 𝒞.toFusionCategoryData η
            movingLabel stationaryLabel
            (sourceMovingExponent metadata countsSound sourceCycle)
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
              metadata countsSound sourceCycle))) =
      mixedCharacterScalar 𝒞.toFusionCategoryData η
          movingLabel stationaryLabel
          (sourceMovingExponent metadata countsSound sourceCycle)
          (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
            metadata countsSound sourceCycle) •
        Diagram.eval C
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceTerm 𝒞
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel) := by
  rw [tensorCharacterCoupon_eq_smul_identity]
  rw [show
    transportEndomorphism
        (sourceLocalObject_negative
          𝒞 metadata countsSound orientationSound remaining
          movingLabel stationaryLabel)
        (mixedCharacterScalar 𝒞.toFusionCategoryData η
            movingLabel stationaryLabel
            (sourceMovingExponent metadata countsSound sourceCycle)
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
              metadata countsSound sourceCycle) •
          𝟙 (TensorObject 𝒞.toFusionCategoryData movingLabel stationaryLabel)) =
      mixedCharacterScalar 𝒞.toFusionCategoryData η
          movingLabel stationaryLabel
          (sourceMovingExponent metadata countsSound sourceCycle)
          (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
            metadata countsSound sourceCycle) •
        transportEndomorphism
          (sourceLocalObject_negative
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (𝟙 (TensorObject 𝒞.toFusionCategoryData
            movingLabel stationaryLabel)) by
    simp [transportEndomorphism]]
  rw [map_smul]
  rw [show
    transportEndomorphism
        (sourceLocalObject_negative
          𝒞 metadata countsSound orientationSound remaining
          movingLabel stationaryLabel)
        (𝟙 (TensorObject 𝒞.toFusionCategoryData movingLabel stationaryLabel)) =
      𝟙 ((localBoundary metadata countsSound).interpret 𝒞
        (source.labelOf 𝒞
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceLabeling
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel))).denote by
    simp [transportEndomorphism]]
  exact congrArg
    (fun value =>
      mixedCharacterScalar 𝒞.toFusionCategoryData η
        movingLabel stationaryLabel
        (sourceMovingExponent metadata countsSound sourceCycle)
        (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
          metadata countsSound sourceCycle) • value)
    (sourceTerm_eval_eq_endpointIdentity
      𝒞 metadata countsSound remaining movingLabel stationaryLabel).symm

/-- The negative target character endpoint is its scalar times the real term. -/
theorem targetNegativeCharacterEndpoint_eq_scalar_smul_term
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .negative)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    LinearContext.evalContextLinearMap (R := K)
        (targetEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (targetLocalObject_negative
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (tensorCharacterCoupon 𝒞.toFusionCategoryData η
            movingLabel stationaryLabel
            (targetMovingExponent metadata countsSound sourceCycle)
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
              metadata countsSound sourceCycle))) =
      mixedCharacterScalar 𝒞.toFusionCategoryData η
          movingLabel stationaryLabel
          (targetMovingExponent metadata countsSound sourceCycle)
          (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
            metadata countsSound sourceCycle) •
        Diagram.eval C
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetTerm 𝒞
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).sameComponentChange
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel) := by
  rw [tensorCharacterCoupon_eq_smul_identity]
  rw [show
    transportEndomorphism
        (targetLocalObject_negative
          𝒞 metadata countsSound orientationSound remaining
          movingLabel stationaryLabel)
        (mixedCharacterScalar 𝒞.toFusionCategoryData η
            movingLabel stationaryLabel
            (targetMovingExponent metadata countsSound sourceCycle)
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
              metadata countsSound sourceCycle) •
          𝟙 (TensorObject 𝒞.toFusionCategoryData movingLabel stationaryLabel)) =
      mixedCharacterScalar 𝒞.toFusionCategoryData η
          movingLabel stationaryLabel
          (targetMovingExponent metadata countsSound sourceCycle)
          (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
            metadata countsSound sourceCycle) •
        transportEndomorphism
          (targetLocalObject_negative
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (𝟙 (TensorObject 𝒞.toFusionCategoryData
            movingLabel stationaryLabel)) by
    simp [transportEndomorphism]]
  rw [map_smul]
  rw [show
    transportEndomorphism
        (targetLocalObject_negative
          𝒞 metadata countsSound orientationSound remaining
          movingLabel stationaryLabel)
        (𝟙 (TensorObject 𝒞.toFusionCategoryData movingLabel stationaryLabel)) =
      𝟙 ((localBoundary metadata countsSound).interpret 𝒞
        (target.labelOf 𝒞
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetLabeling
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).sameComponentChange
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel))).denote by
    simp [transportEndomorphism]]
  exact congrArg
    (fun value =>
      mixedCharacterScalar 𝒞.toFusionCategoryData η
        movingLabel stationaryLabel
        (targetMovingExponent metadata countsSound sourceCycle)
        (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
          metadata countsSound sourceCycle) • value)
    (targetTerm_eval_eq_endpointIdentity
      𝒞 metadata countsSound remaining movingLabel stationaryLabel).symm

/-- One fully weighted negative `(x,y)` sector is invariant. -/
theorem negativeBandMovie_weightedTerm
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .negative)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceWeight
          𝒞 η
          (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).resolvedComponents
          sourceCycle remaining movingLabel stationaryLabel •
        Diagram.eval C
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceTerm 𝒞
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel) =
      CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetWeight
          𝒞 η
          (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).sameComponentChange
          (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).resolvedComponents
          ((CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).targetCycle sourceCycle)
          remaining movingLabel stationaryLabel •
        Diagram.eval C
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetTerm 𝒞
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).sameComponentChange
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel) := by
  let request :=
    CanonicalSourceBoundSlideMovie.Request.twoOverTwo metadata countsSound
  have endpoint :=
    negativeBandMovie_globalCharacterEndpoint
      𝒞 η metadata countsSound orientationSound sourceCycle remaining
      movingLabel stationaryLabel
  rw [
    sourceNegativeCharacterEndpoint_eq_scalar_smul_term
      𝒞 η metadata countsSound orientationSound sourceCycle remaining
        movingLabel stationaryLabel,
    targetNegativeCharacterEndpoint_eq_scalar_smul_term
      𝒞 η metadata countsSound orientationSound sourceCycle remaining
        movingLabel stationaryLabel
  ] at endpoint
  rw [
    targetMovingExponent_eq_sourceMovingExponent
      metadata countsSound sourceCycle,
    targetStationaryExponent_eq_sourceStationaryExponent
      metadata countsSound sourceCycle
  ] at endpoint
  unfold mixedCharacterScalar at endpoint
  have commonWeight :
      CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceWeight
          𝒞 η request.resolvedComponents sourceCycle remaining
          𝒞.premodular.toFusionCategoryData.unitIndex
          𝒞.premodular.toFusionCategoryData.unitIndex =
        CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetWeight
          𝒞 η request.sameComponentChange request.resolvedComponents
          (request.targetCycle sourceCycle) remaining
          𝒞.premodular.toFusionCategoryData.unitIndex
          𝒞.premodular.toFusionCategoryData.unitIndex := by
    rw [← CanonicalSourceBoundSlideMovie.premodularTwoOverTwoCoefficient_apply
      𝒞 η metadata countsSound sourceCycle remaining
      𝒞.premodular.toFusionCategoryData.unitIndex]
    exact
      CanonicalSourceBoundSlideMovie.premodularTwoOverTwoCoefficient_eq_targetUnitWeight
        𝒞 η metadata countsSound sourceCycle remaining
        𝒞.premodular.toFusionCategoryData.unitIndex
  rw [
    CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceWeight_factor_both,
    CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetWeight_factor_both,
    ← commonWeight
  ]
  unfold CanonicalPresentation.cycleComponentWeight
  change
    ((𝒞.premodular.quantumDimension movingLabel *
          𝒞.toFusionCategoryData.automorphismScalarPower η movingLabel
            (sourceMovingExponent metadata countsSound sourceCycle)) *
        (𝒞.premodular.quantumDimension stationaryLabel *
          𝒞.toFusionCategoryData.automorphismScalarPower η stationaryLabel
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
              metadata countsSound sourceCycle)) *
        _) • _ =
      ((𝒞.premodular.quantumDimension movingLabel *
          𝒞.toFusionCategoryData.automorphismScalarPower η movingLabel
            (targetMovingExponent metadata countsSound sourceCycle)) *
        (𝒞.premodular.quantumDimension stationaryLabel *
          𝒞.toFusionCategoryData.automorphismScalarPower η stationaryLabel
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
              metadata countsSound sourceCycle)) *
        _) • _
  rw [
    targetMovingExponent_eq_sourceMovingExponent
      metadata countsSound sourceCycle,
    targetStationaryExponent_eq_sourceStationaryExponent
      metadata countsSound sourceCycle
  ]
  let dimensionFactor : K :=
    𝒞.premodular.quantumDimension movingLabel *
      𝒞.premodular.quantumDimension stationaryLabel
  let characterFactor : K :=
    𝒞.toFusionCategoryData.automorphismScalarPower η movingLabel
        (sourceMovingExponent metadata countsSound sourceCycle) *
      𝒞.toFusionCategoryData.automorphismScalarPower η stationaryLabel
        (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
          metadata countsSound sourceCycle)
  let commonFactor : K :=
    CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceWeight
      𝒞 η request.resolvedComponents sourceCycle remaining
      𝒞.premodular.toFusionCategoryData.unitIndex
      𝒞.premodular.toFusionCategoryData.unitIndex
  calc
    _ =
        (dimensionFactor * commonFactor * characterFactor) •
          Diagram.eval C
            (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceTerm 𝒞
              request.resolvedComponents remaining movingLabel stationaryLabel) := by
      dsimp only [dimensionFactor, characterFactor, commonFactor]
      congr 1
      ring
    _ =
        (dimensionFactor * commonFactor) •
          (characterFactor •
            Diagram.eval C
              (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceTerm 𝒞
                request.resolvedComponents remaining movingLabel stationaryLabel)) := by
      rw [smul_smul]
    _ =
        (dimensionFactor * commonFactor) •
          (characterFactor •
            Diagram.eval C
              (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetTerm 𝒞
                request.sameComponentChange request.resolvedComponents remaining
                movingLabel stationaryLabel)) := by
      rw [endpoint]
    _ =
        (dimensionFactor * commonFactor * characterFactor) •
          Diagram.eval C
            (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetTerm 𝒞
              request.sameComponentChange request.resolvedComponents remaining
              movingLabel stationaryLabel) := by
      rw [smul_smul]
    _ = _ := by
      dsimp only [dimensionFactor, characterFactor, commonFactor]
      congr 1
      ring

/-- Both selected labels are summed in one fixed-complement negative block. -/
theorem negativeBandMovie_block_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .negative)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).Block (S := S)) :
    LinearDiagram.eval
        (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceBlock
          𝒞 η
          (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).resolvedComponents
          sourceCycle remaining) =
      LinearDiagram.eval
        (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetBlock
          𝒞 η
          (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).sameComponentChange
          (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).resolvedComponents
          ((CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).targetCycle sourceCycle)
          remaining) := by
  classical
  unfold CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceBlock
    CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetBlock
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro movingLabel _
  apply Finset.sum_congr rfl
  intro stationaryLabel _
  simp only [map_smul, LinearDiagram.eval_atom]
  exact negativeBandMovie_weightedTerm
    𝒞 η metadata countsSound orientationSound sourceCycle remaining
    movingLabel stationaryLabel

/-- Complete negative 2/2 role-aware premodular evaluator equality. -/
theorem negativeBandMovie_cycleLinearDiagram_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .negative)
    (sourceCycle : source.DegreeTwoCycle) :
    LinearDiagram.eval
        (source.cycleLinearDiagram 𝒞 η sourceCycle) =
      LinearDiagram.eval
        (target.cycleLinearDiagram 𝒞 η
          ((CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).targetCycle sourceCycle)) := by
  classical
  rw [CanonicalCycleSlideGeometry.CanonicalSlideBlocks.source_decomposition
    𝒞 η
    (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
      metadata countsSound).resolvedComponents
    sourceCycle]
  rw [CanonicalCycleSlideGeometry.CanonicalSlideBlocks.target_decomposition
    𝒞 η
    (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
      metadata countsSound).sameComponentChange
    (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
      metadata countsSound).resolvedComponents
    ((CanonicalSourceBoundSlideMovie.Request.twoOverTwo
      metadata countsSound).targetCycle sourceCycle)]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro remaining _
  exact negativeBandMovie_block_eval_eq
    𝒞 η metadata countsSound orientationSound sourceCycle remaining

end TwistedYetter.Kirby.TwoOverTwoNegativeBandMovie
