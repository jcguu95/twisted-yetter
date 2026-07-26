import TwistedYetter.Kirby.TwoOverTwoPositiveEndpointChannel

/-!
# Source-bound Bärenz--Barrett band movie

This file isolates the sole literature/topology input still needed by the
positive two-over-two calculation.  It does not mention a character,
component exponent, fusion label, or scalar weight: an arbitrary endomorphism
of the exposed local object may pass through the standard band-slide movie.

All character bookkeeping is derived after this input is instantiated with
the explicit `d_z`-weighted fusion-channel morphisms.
-/

namespace TwistedYetter.Kirby.TwoOverTwoBandMovie

open scoped BigOperators
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

local instance twoOverTwoBandMovieRightRigid : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/--
The endpoint-bound form of Bärenz--Barrett Lemmas 3.3--3.4.

The source and target contexts are not arbitrary diagrams: they are obtained
from the exact admitted presentations by `standardSharedFreeWindow`.  The
only content imported from the literature is that the standard positive band
movie transports an arbitrary endomorphism of the exposed object.

In particular, this statement contains no tensor-identity automorphism and
cannot assert the twisted answer directly.
-/
axiom baerenzBarrett_positiveBandMovie
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
    (movingLabel stationaryLabel : S)
    (f :
      OrientedTensorObject 𝒞 movingLabel stationaryLabel ⟶
        OrientedTensorObject 𝒞 movingLabel stationaryLabel) :
    LinearContext.evalContextLinearMap (R := K)
        (sourceEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (sourceLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          f) =
      LinearContext.evalContextLinearMap (R := K)
        (targetEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (targetLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          f)

/--
Every explicit `(z, μ)` channel crosses the exact source-bound band movie.

This is the first twisted theorem in this file: it is obtained by
specializing the character-free literature input to the channel morphism
already constructed and proved correct in `TwoOverTwoFusionChannel`.
-/
theorem positiveBandMovie_channel
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
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
    (movingExponent stationaryExponent : ℤ)
    (channel : OrientedChannel 𝒞 movingLabel stationaryLabel) :
    LinearContext.evalContextLinearMap (R := K)
        (sourceEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (sourceLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (unequalExponentChannelMorphism
            𝒞 η movingLabel stationaryLabel
            movingExponent stationaryExponent channel)) =
      LinearContext.evalContextLinearMap (R := K)
        (targetEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (targetLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (unequalExponentChannelMorphism
            𝒞 η movingLabel stationaryLabel
            movingExponent stationaryExponent channel)) :=
  baerenzBarrett_positiveBandMovie
    𝒞 metadata countsSound orientationSound remaining
    movingLabel stationaryLabel
    (unequalExponentChannelMorphism
      𝒞 η movingLabel stationaryLabel
      movingExponent stationaryExponent channel)

/--
The complete finite channel sum crosses the exact band movie.
-/
theorem positiveBandMovie_channelSum
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
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
    (∑ channel : OrientedChannel 𝒞 movingLabel stationaryLabel,
      LinearContext.evalContextLinearMap (R := K)
        (sourceEndpointContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        (transportEndomorphism
          (sourceLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (unequalExponentChannelMorphism
            𝒞 η movingLabel stationaryLabel
            movingExponent stationaryExponent channel))) =
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
              movingExponent stationaryExponent channel)) := by
  apply Finset.sum_congr rfl
  intro channel _
  exact positiveBandMovie_channel
    𝒞 η metadata countsSound orientationSound remaining
    movingLabel stationaryLabel movingExponent stationaryExponent channel

/--
The character-decorated positive endpoint is invariant under the exact
source-bound two-over-two band movie.

The two source exponents are read from the handle-chain cycle.  The target
exponents are not assumed equal: the two previously proved transport
theorems rewrite them to the source exponents.  The proof then expands both
endpoints into the complete `(z, μ)` sum and applies the character-free
Bärenz--Barrett movie one channel at a time.
-/
theorem positiveBandMovie_globalCharacterEndpoint
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
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
              metadata countsSound sourceCycle))) =
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
  rw [
    targetMovingExponent_eq_sourceMovingExponent
      metadata countsSound sourceCycle,
    targetStationaryExponent_eq_sourceStationaryExponent
      metadata countsSound sourceCycle
  ]
  exact baerenzBarrett_positiveBandMovie
    𝒞 metadata countsSound orientationSound remaining
    movingLabel stationaryLabel
    (globalPositiveEndpointCoupon
      𝒞 η movingLabel stationaryLabel
      (sourceMovingExponent metadata countsSound sourceCycle)
      (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
        metadata countsSound sourceCycle))

/--
The character coupon at the exact source endpoint is precisely the product
of the two component character scalars multiplying the undecorated source
evaluator term.
-/
theorem sourceGlobalCharacterEndpoint_eq_scalar_smul_term
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
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
              metadata countsSound sourceCycle))) =
      (𝒞.toFusionCategoryData.automorphismScalarPower
          η movingLabel
          (sourceMovingExponent metadata countsSound sourceCycle) *
        𝒞.toFusionCategoryData.automorphismScalarPower
          η stationaryLabel
          (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
            metadata countsSound sourceCycle)) •
        Diagram.eval C
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceTerm 𝒞
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel) := by
  rw [globalPositiveEndpointCoupon,
    orientedCharacterCoupon_eq_smul_identity]
  simp only [orientedCharacterScalar, neg_neg]
  rw [show
    transportEndomorphism
        (sourceLocalObject_positive
          𝒞 metadata countsSound orientationSound remaining
          movingLabel stationaryLabel)
        ((𝒞.toFusionCategoryData.automorphismScalarPower
              η movingLabel
              (sourceMovingExponent metadata countsSound sourceCycle) *
            𝒞.toFusionCategoryData.automorphismScalarPower
              η stationaryLabel
              (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
                metadata countsSound sourceCycle)) •
          𝟙 (OrientedTensorObject 𝒞 movingLabel stationaryLabel)) =
      (𝒞.toFusionCategoryData.automorphismScalarPower
            η movingLabel
            (sourceMovingExponent metadata countsSound sourceCycle) *
          𝒞.toFusionCategoryData.automorphismScalarPower
            η stationaryLabel
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
              metadata countsSound sourceCycle)) •
        transportEndomorphism
          (sourceLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (𝟙 (OrientedTensorObject 𝒞 movingLabel stationaryLabel)) by
    simp [transportEndomorphism]]
  rw [map_smul]
  rw [show
    transportEndomorphism
        (sourceLocalObject_positive
          𝒞 metadata countsSound orientationSound remaining
          movingLabel stationaryLabel)
        (𝟙 (OrientedTensorObject 𝒞 movingLabel stationaryLabel)) =
      𝟙 ((localBoundary metadata countsSound).interpret 𝒞
        (source.labelOf 𝒞
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.sourceLabeling
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel))).denote by
    simp [transportEndomorphism]]
  exact congrArg
    (fun value =>
      (𝒞.toFusionCategoryData.automorphismScalarPower
            η movingLabel
            (sourceMovingExponent metadata countsSound sourceCycle) *
          𝒞.toFusionCategoryData.automorphismScalarPower
            η stationaryLabel
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoSourceStationaryExponent
              metadata countsSound sourceCycle)) • value)
    (sourceTerm_eval_eq_endpointIdentity
      𝒞 metadata countsSound remaining movingLabel stationaryLabel).symm

/--
The target endpoint has the same concrete interpretation: its character
coupon is the product of the two transported component scalars multiplying
the undecorated target evaluator term.
-/
theorem targetGlobalCharacterEndpoint_eq_scalar_smul_term
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
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
              metadata countsSound sourceCycle))) =
      (𝒞.toFusionCategoryData.automorphismScalarPower
          η movingLabel
          (targetMovingExponent metadata countsSound sourceCycle) *
        𝒞.toFusionCategoryData.automorphismScalarPower
          η stationaryLabel
          (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
            metadata countsSound sourceCycle)) •
        Diagram.eval C
          (CanonicalCycleSlideGeometry.CanonicalSlideBlocks.targetTerm 𝒞
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).sameComponentChange
            (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
              metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel) := by
  rw [globalPositiveEndpointCoupon,
    orientedCharacterCoupon_eq_smul_identity]
  simp only [orientedCharacterScalar, neg_neg]
  rw [show
    transportEndomorphism
        (targetLocalObject_positive
          𝒞 metadata countsSound orientationSound remaining
          movingLabel stationaryLabel)
        ((𝒞.toFusionCategoryData.automorphismScalarPower
              η movingLabel
              (targetMovingExponent metadata countsSound sourceCycle) *
            𝒞.toFusionCategoryData.automorphismScalarPower
              η stationaryLabel
              (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
                metadata countsSound sourceCycle)) •
          𝟙 (OrientedTensorObject 𝒞 movingLabel stationaryLabel)) =
      (𝒞.toFusionCategoryData.automorphismScalarPower
            η movingLabel
            (targetMovingExponent metadata countsSound sourceCycle) *
          𝒞.toFusionCategoryData.automorphismScalarPower
            η stationaryLabel
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
              metadata countsSound sourceCycle)) •
        transportEndomorphism
          (targetLocalObject_positive
            𝒞 metadata countsSound orientationSound remaining
            movingLabel stationaryLabel)
          (𝟙 (OrientedTensorObject 𝒞 movingLabel stationaryLabel)) by
    simp [transportEndomorphism]]
  rw [map_smul]
  rw [show
    transportEndomorphism
        (targetLocalObject_positive
          𝒞 metadata countsSound orientationSound remaining
          movingLabel stationaryLabel)
        (𝟙 (OrientedTensorObject 𝒞 movingLabel stationaryLabel)) =
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
      (𝒞.toFusionCategoryData.automorphismScalarPower
            η movingLabel
            (targetMovingExponent metadata countsSound sourceCycle) *
          𝒞.toFusionCategoryData.automorphismScalarPower
            η stationaryLabel
            (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoTargetStationaryExponent
              metadata countsSound sourceCycle)) • value)
    (targetTerm_eval_eq_endpointIdentity
      𝒞 metadata countsSound remaining movingLabel stationaryLabel).symm

/--
One fully weighted pair of simple labels has the same value before and after
the positive 2/2 slide.  Unlike the earlier endpoint assumptions, this
statement uses the actual source and target terms and their actual
handle-chain weights.
-/
theorem positiveBandMovie_weightedTerm
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
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
    positiveBandMovie_globalCharacterEndpoint
      𝒞 η metadata countsSound orientationSound sourceCycle
      remaining movingLabel stationaryLabel
  rw [
    sourceGlobalCharacterEndpoint_eq_scalar_smul_term
      𝒞 η metadata countsSound orientationSound sourceCycle remaining
        movingLabel stationaryLabel,
    targetGlobalCharacterEndpoint_eq_scalar_smul_term
      𝒞 η metadata countsSound orientationSound sourceCycle remaining
        movingLabel stationaryLabel
  ] at endpoint
  rw [
    targetMovingExponent_eq_sourceMovingExponent
      metadata countsSound sourceCycle,
    targetStationaryExponent_eq_sourceStationaryExponent
      metadata countsSound sourceCycle
  ] at endpoint
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
    exact CanonicalSourceBoundSlideMovie.premodularTwoOverTwoCoefficient_eq_targetUnitWeight
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

/--
The complete fixed-complement block is invariant.  Both selected simple
labels are explicitly summed, so no `(x,y)` sector can disappear.
-/
theorem positiveBandMovie_block_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
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
  exact positiveBandMovie_weightedTerm
    𝒞 η metadata countsSound orientationSound sourceCycle
    remaining movingLabel stationaryLabel

/--
The complete positive 2/2 slide preserves the unnormalised role-aware
premodular evaluation.  This sums the block theorem over every labeling of
all components outside the moving pair.
-/
theorem positiveBandMovie_cycleLinearDiagram_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation = .positive)
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
  exact positiveBandMovie_block_eval_eq
    𝒞 η metadata countsSound orientationSound sourceCycle remaining

end TwistedYetter.Kirby.TwoOverTwoBandMovie
