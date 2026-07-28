import TwistedYetter.Kirby.CanonicalCycleMoveGeometry
import TwistedYetter.Kirby.SelectedCoordinateFiniteSum
import TwistedYetter.Kirby.TensorAutomorphismCouponCalculus
import TwistedYetter.Kirby.ThamThreeHandleVacuum

/-!
# Whole-sum slide geometry for the canonical modular evaluator

Kirby colours are finite linear combinations.  A local slide proof must
therefore have the complete explicit-cycle linear diagrams as its endpoints;
it is not enough to postulate one equality for every fixed global labeling.

This module provides two closed proof grammars:

* ordinary 1-over-1 and 2-over-1 slides use the exact formal ordinary Kirby
  colour retained by `OrdinaryHandleSlide`; and
* 2-over-2 slides expand the twisted sliding colour label by label and derive
  every term from the ordinary Kirby-colour sliding theorem.  This is the
  identity-functor specialization in Bärenz--Barrett Remark 3.5.

Every atomic proof is bound to the directed move metadata, including band
orientation, presentation hashes, and both participating component IDs.
There is no constructor from a diagram-evaluation equality or a scalar
equality.

The endpoint geometries use the explicit target cycle obtained from the
forward handle-chain map.  Consequently, no arbitrary homology
representative is required to commute with a Kirby move.
-/

namespace TwistedYetter.Kirby.CanonicalCycleSlideGeometry

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.EGNOKirbyColorEncircling
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.EGNOModularKirbyMoves.LiteratureBackedModularGraphicalEnvironment
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.LinearDiagram
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe
open TwistedYetter.Kirby.SelectedCoordinateFiniteSum
open TwistedYetter.Kirby.TensorAutomorphismCouponCalculus

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-
RETIRED LEGACY ROUTE (2026-07-27)

The declarations through `TermwiseCouponAdaptedKirbyColourSlideWindow` used
the old ordinary-Kirby-colour slide environment.  The role-aware premodular
main line uses `CanonicalSlideBlocks` below and the label-indexed band laws
directly.  This block is intentionally excluded from compilation.

/--
Linear closure of complete fixed-label ordinary-slide windows with
source-bound metadata.

The base constructor consumes the whole label-indexed finite sum.  Its
soundness is derived from ordinary Kirby-colour sliding and naturality; no
independent generalized-sliding axiom is used.
-/
inductive BoundKirbyColourLinearSlide
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (kind : SlideKind)
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String)
    (slidingComponentId stationaryComponentId : String) :
    LinearDiagram (R := K) (C := C) .unit .unit →
      LinearDiagram (R := K) (C := C) .unit .unit →
        Type (max uK uC vC)
  | window
      (metadata : SlideMetadata)
      (kind_sound : metadata.kind = kind)
      (orientation_sound : metadata.orientation = orientation)
      (move_id_sound : metadata.moveId = moveId)
      (source_hash_sound :
        metadata.sourcePresentationHash = sourceHash)
      (target_hash_sound :
        metadata.targetPresentationHash = targetHash)
      (sliding_component_id_sound :
        metadata.slidingComponentId = slidingComponentId)
      (stationary_component_id_sound :
        metadata.stationaryComponentId = stationaryComponentId)
      (_lineage : ComponentLineage metadata)
      (closedWindow :
        OrdinaryLabelIndexedSlidingWindow
          𝒞.premodular
          (baerenzBarrett_ordinaryKirbySliding 𝒞.premodular))
      (coefficient : S → K) :
      BoundKirbyColourLinearSlide 𝒞 kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (closedWindow.expandedLinearBefore coefficient)
        (closedWindow.expandedLinearAfter coefficient)
  | add
      {leftBefore leftAfter rightBefore rightAfter :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundKirbyColourLinearSlide 𝒞 kind orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId
          leftBefore leftAfter →
      BoundKirbyColourLinearSlide 𝒞 kind orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId
          rightBefore rightAfter →
      BoundKirbyColourLinearSlide 𝒞 kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (leftBefore + rightBefore) (leftAfter + rightAfter)
  | smul
      (scalar : K)
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundKirbyColourLinearSlide 𝒞 kind orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId before after →
      BoundKirbyColourLinearSlide 𝒞 kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (scalar • before) (scalar • after)
  | trans
      {first middle last :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundKirbyColourLinearSlide 𝒞 kind orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId first middle →
      BoundKirbyColourLinearSlide 𝒞 kind orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId middle last →
      BoundKirbyColourLinearSlide 𝒞 kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId first last

namespace BoundKirbyColourLinearSlide

/--
Soundness follows from the derived fixed-label ordinary window and linearity.
-/
theorem eval_eq
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {kind : SlideKind}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {slidingComponentId stationaryComponentId : String}
    {before after :
      LinearDiagram (R := K) (C := C) .unit .unit}
    (slide :
      BoundKirbyColourLinearSlide 𝒞 kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId before after) :
    LinearDiagram.eval before = LinearDiagram.eval after := by
  induction slide with
  | window _ _ _ _ _ _ _ _ _ closedWindow coefficient =>
      exact closedWindow.expanded_linear_eval_sound coefficient
  | add _ _ leftSound rightSound =>
      simpa only [map_add] using
        congrArg₂ (· + ·) leftSound rightSound
  | smul scalar _ sound =>
      simpa only [map_smul] using
        congrArg (fun value => scalar • value) sound
  | trans _ _ firstSound secondSound =>
      exact firstSound.trans secondSound

end BoundKirbyColourLinearSlide

/--
One coupon-adapted local window between the two canonical linear blocks.

The endpoint conversions use only the closed tensor-automorphism coupon
grammar.  The middle window is the exact expanded ordinary Kirby-colour
slide.  No field accepts an evaluator equality.
-/
structure CouponAdaptedKirbyColourSlideWindow
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (kind : SlideKind)
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String)
    (slidingComponentId stationaryComponentId : String)
    (before after :
      LinearDiagram (R := K) (C := C) .unit .unit) where
  closedWindow :
    OrdinaryLabelIndexedSlidingWindow
      𝒞.premodular
      (baerenzBarrett_ordinaryKirbySliding 𝒞.premodular)
  coefficient : S → K
  beforeConversion :
    FusionLinearGeneratedCalculation
      𝒞.premodular.toFusionCategoryData automorphism
      before
      (closedWindow.expandedLinearBefore coefficient)
  afterConversion :
    FusionLinearGeneratedCalculation
      𝒞.premodular.toFusionCategoryData automorphism
      (closedWindow.expandedLinearAfter coefficient)
      after

namespace CouponAdaptedKirbyColourSlideWindow

/--
Every coupon-adapted local window preserves evaluation.

The first and last equalities come from the restricted coupon grammar; the
middle equality is the derived label-indexed ordinary Kirby-colour slide.
-/
theorem eval_eq
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {kind : SlideKind}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {slidingComponentId stationaryComponentId : String}
    {before after :
      LinearDiagram (R := K) (C := C) .unit .unit}
    (window :
      CouponAdaptedKirbyColourSlideWindow 𝒞 automorphism kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId before after) :
    LinearDiagram.eval before = LinearDiagram.eval after := by
  calc
    _ = LinearDiagram.eval
          (window.closedWindow.expandedLinearBefore window.coefficient) :=
      window.beforeConversion.eval_eq
    _ = LinearDiagram.eval
          (window.closedWindow.expandedLinearAfter window.coefficient) :=
      window.closedWindow.expanded_linear_eval_sound window.coefficient
    _ = _ :=
      window.afterConversion.eval_eq

end CouponAdaptedKirbyColourSlideWindow

/--
Termwise form of a coupon-adapted slide window.

The input must supply one restricted coupon calculation for each ordered
pair consisting of the moving label and the stationary Kirby-colour label.
The complete double-sum conversion is derived by finite addition below.
This prevents a local input from hiding cancellation between different
simple-label sectors.
-/
structure TermwiseCouponAdaptedKirbyColourSlideWindow
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (kind : SlideKind)
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String)
    (slidingComponentId stationaryComponentId : String)
    (beforeWeight afterWeight : S → S → K)
    (beforeTerm afterTerm : S → S → Diagram C .unit .unit) where
  closedWindow :
    OrdinaryLabelIndexedSlidingWindow
      𝒞.premodular
      (baerenzBarrett_ordinaryKirbySliding 𝒞.premodular)
  coefficient : S → K
  beforeTermConversion :
    (movingLabel stationaryLabel : S) →
      FusionLinearGeneratedCalculation
        𝒞.premodular.toFusionCategoryData automorphism
        (beforeWeight movingLabel stationaryLabel •
          LinearDiagram.atom (R := K)
            (beforeTerm movingLabel stationaryLabel))
        (coefficient movingLabel •
          (𝒞.premodular.quantumDimension stationaryLabel •
            LinearDiagram.atom (R := K)
              (closedWindow.expandedBeforeTerm
                movingLabel stationaryLabel)))
  afterTermConversion :
    (movingLabel stationaryLabel : S) →
      FusionLinearGeneratedCalculation
        𝒞.premodular.toFusionCategoryData automorphism
        (coefficient movingLabel •
          (𝒞.premodular.quantumDimension stationaryLabel •
            LinearDiagram.atom (R := K)
              (closedWindow.expandedAfterTerm
                movingLabel stationaryLabel)))
        (afterWeight movingLabel stationaryLabel •
          LinearDiagram.atom (R := K)
            (afterTerm movingLabel stationaryLabel))

namespace TermwiseCouponAdaptedKirbyColourSlideWindow

/--
Lean reassembles all termwise coupon calculations into the exact double-sum
window.  No denominator-completeness or cross-label cancellation premise is
needed.
-/
noncomputable def toWindow
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {kind : SlideKind}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {slidingComponentId stationaryComponentId : String}
    {beforeWeight afterWeight : S → S → K}
    {beforeTerm afterTerm : S → S → Diagram C .unit .unit}
    (window :
      TermwiseCouponAdaptedKirbyColourSlideWindow
        𝒞 automorphism kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        beforeWeight afterWeight beforeTerm afterTerm) :
    CouponAdaptedKirbyColourSlideWindow
      𝒞 automorphism kind orientation
      moveId sourceHash targetHash
      slidingComponentId stationaryComponentId
      (∑ movingLabel, ∑ stationaryLabel,
        beforeWeight movingLabel stationaryLabel •
          LinearDiagram.atom (R := K)
            (beforeTerm movingLabel stationaryLabel))
      (∑ movingLabel, ∑ stationaryLabel,
        afterWeight movingLabel stationaryLabel •
          LinearDiagram.atom (R := K)
            (afterTerm movingLabel stationaryLabel)) where
  closedWindow := window.closedWindow
  coefficient := window.coefficient
  beforeConversion := by
    simpa only [
      OrdinaryLabelIndexedSlidingWindow.expandedLinearBefore,
      Finset.smul_sum
    ] using
      FusionLinearGeneratedCalculation.doubleSum
        window.beforeTermConversion
  afterConversion := by
    simpa only [
      OrdinaryLabelIndexedSlidingWindow.expandedLinearAfter,
      Finset.smul_sum
    ] using
      FusionLinearGeneratedCalculation.doubleSum
        window.afterTermConversion

end TermwiseCouponAdaptedKirbyColourSlideWindow
-/

/-
Canonical finite blocks obtained by leaving both the moving label and the
stationary Kirby colour summed and fixing every other source-component label.

The target block is indexed by the same source labeling and transported by
the exact component correspondence.  This makes denominator completeness a
theorem of finite-sum reindexing rather than an assumption.
-/
namespace CanonicalSlideBlocks

abbrev Block
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId) :=
  RemainingIndex
      (remainingSelected
        components.stationarySourceIndex
        components.slidingSourceIndex
        components.source_indices_distinct) →
    S

/-- Reinsert the two visible labels into one fixed remaining-label block. -/
def sourceLabeling
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    source.GlobalLabeling (S := S) :=
  combineAtTwo
    components.stationarySourceIndex
    components.slidingSourceIndex
    components.source_indices_distinct
    stationaryLabel movingLabel remaining

@[simp] theorem sourceLabeling_stationary
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    sourceLabeling components remaining movingLabel stationaryLabel
        components.stationarySourceIndex =
      stationaryLabel := by
  exact combineAtTwo_first
    components.stationarySourceIndex
    components.slidingSourceIndex
    components.source_indices_distinct
    stationaryLabel movingLabel remaining

@[simp] theorem sourceLabeling_moving
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    sourceLabeling components remaining movingLabel stationaryLabel
        components.slidingSourceIndex =
      movingLabel := by
  exact combineAtTwo_second
    components.stationarySourceIndex
    components.slidingSourceIndex
    components.source_indices_distinct
    stationaryLabel movingLabel remaining

theorem sourceLabeling_eq_away_from_stationary
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel stationaryLabel' : S)
    {index : ComponentIndex source.topology.formal}
    (index_ne_stationary : index ≠ components.stationarySourceIndex) :
    sourceLabeling components remaining movingLabel stationaryLabel index =
      sourceLabeling components remaining movingLabel stationaryLabel' index := by
  exact combineAtTwo_eq_of_ne_first
    components.stationarySourceIndex
    components.slidingSourceIndex
    components.source_indices_distinct
    stationaryLabel stationaryLabel' movingLabel remaining
    index_ne_stationary

theorem sourceLabeling_eq_away_from_moving
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel movingLabel' stationaryLabel : S)
    {index : ComponentIndex source.topology.formal}
    (index_ne_moving : index ≠ components.slidingSourceIndex) :
    sourceLabeling components remaining movingLabel stationaryLabel index =
      sourceLabeling components remaining movingLabel' stationaryLabel index := by
  exact combineAtTwo_eq_of_ne_second
    components.stationarySourceIndex
    components.slidingSourceIndex
    components.source_indices_distinct
    stationaryLabel movingLabel movingLabel' remaining
    index_ne_moving

/-- Transport one reassembled source labeling to the target presentation. -/
def targetLabeling
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    target.GlobalLabeling (S := S) :=
  same.labelingEquiv S
    (sourceLabeling components remaining movingLabel stationaryLabel)

@[simp] theorem targetLabeling_stationary
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    targetLabeling same components remaining movingLabel stationaryLabel
        components.stationaryTargetIndex =
      stationaryLabel := by
  simp [targetLabeling, SameComponentIndexChange.labelingEquiv,
    ResolvedSlideComponentPair.stationaryTargetIndex]

@[simp] theorem targetLabeling_moving
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    targetLabeling same components remaining movingLabel stationaryLabel
        components.slidingTargetIndex =
      movingLabel := by
  simp [targetLabeling, SameComponentIndexChange.labelingEquiv,
    ResolvedSlideComponentPair.slidingTargetIndex]

theorem targetLabeling_eq_away_from_stationary
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel stationaryLabel' : S)
    {index : ComponentIndex target.topology.formal}
    (index_ne_stationary : index ≠ components.stationaryTargetIndex) :
    targetLabeling same components remaining movingLabel stationaryLabel index =
      targetLabeling same components remaining movingLabel stationaryLabel'
        index := by
  apply sourceLabeling_eq_away_from_stationary
  intro source_index_eq
  apply index_ne_stationary
  apply same.targetToSource.injective
  simpa [ResolvedSlideComponentPair.stationaryTargetIndex] using
    source_index_eq

theorem targetLabeling_eq_away_from_moving
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel movingLabel' stationaryLabel : S)
    {index : ComponentIndex target.topology.formal}
    (index_ne_moving : index ≠ components.slidingTargetIndex) :
    targetLabeling same components remaining movingLabel stationaryLabel index =
      targetLabeling same components remaining movingLabel'
        stationaryLabel index := by
  apply sourceLabeling_eq_away_from_moving
  intro source_index_eq
  apply index_ne_moving
  apply same.targetToSource.injective
  simpa [ResolvedSlideComponentPair.slidingTargetIndex] using
    source_index_eq

/-- Exact source coefficient in one visible two-label sector. -/
noncomputable def sourceWeight
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) : K :=
  source.cycleGlobalWeight 𝒞 automorphism sourceCycle
    (sourceLabeling components remaining movingLabel stationaryLabel)

/--
The stationary component weight factors from the complete source coefficient.

The second factor is the same complete coefficient with the stationary label
specialized to the tensor unit.  This is a finite-product theorem valid for
every premodular category; no modular killing relation is used.
-/
theorem sourceWeight_factor_stationary
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    sourceWeight 𝒞 automorphism components sourceCycle remaining
        movingLabel stationaryLabel =
      source.cycleComponentWeight 𝒞 automorphism sourceCycle
          (componentAt source.topology.formal
            components.stationarySourceIndex) stationaryLabel *
        sourceWeight 𝒞 automorphism components sourceCycle remaining
          movingLabel 𝒞.premodular.toFusionCategoryData.unitIndex := by
  classical
  unfold sourceWeight CanonicalPresentation.cycleGlobalWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      source.cycleComponentWeight 𝒞 automorphism sourceCycle
        (source.topology.formal.raw.components.get index)
        (sourceLabeling components remaining movingLabel stationaryLabel index))
    components.stationarySourceIndex]
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      source.cycleComponentWeight 𝒞 automorphism sourceCycle
        (source.topology.formal.raw.components.get index)
        (sourceLabeling components remaining movingLabel
          𝒞.premodular.toFusionCategoryData.unitIndex index))
    components.stationarySourceIndex]
  rw [sourceLabeling_stationary, sourceLabeling_stationary]
  have unitWeight :
      source.cycleComponentWeight 𝒞 automorphism sourceCycle
          (source.topology.formal.raw.components.get
            components.stationarySourceIndex)
          𝒞.premodular.toFusionCategoryData.unitIndex = 1 := by
    unfold CanonicalPresentation.cycleComponentWeight
    rw [𝒞.premodular.quantumDimension_unit]
    rw [
      ThamThreeHandleVacuum.automorphismScalarPower_unitIndex]
    simp
  rw [unitWeight]
  simp only [one_mul, componentAt]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  exact congrArg
    (fun label =>
      source.cycleComponentWeight 𝒞 automorphism sourceCycle
        (source.topology.formal.raw.components.get index.1) label)
    (sourceLabeling_eq_away_from_stationary
      components remaining movingLabel stationaryLabel
        𝒞.premodular.toFusionCategoryData.unitIndex index.property)

/-- The moving component weight also factors from the source coefficient. -/
theorem sourceWeight_factor_moving
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    sourceWeight 𝒞 automorphism components sourceCycle remaining
        movingLabel stationaryLabel =
      source.cycleComponentWeight 𝒞 automorphism sourceCycle
          (componentAt source.topology.formal
            components.slidingSourceIndex) movingLabel *
        sourceWeight 𝒞 automorphism components sourceCycle remaining
          𝒞.premodular.toFusionCategoryData.unitIndex stationaryLabel := by
  classical
  unfold sourceWeight CanonicalPresentation.cycleGlobalWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      source.cycleComponentWeight 𝒞 automorphism sourceCycle
        (source.topology.formal.raw.components.get index)
        (sourceLabeling components remaining movingLabel stationaryLabel index))
    components.slidingSourceIndex]
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      source.cycleComponentWeight 𝒞 automorphism sourceCycle
        (source.topology.formal.raw.components.get index)
        (sourceLabeling components remaining
          𝒞.premodular.toFusionCategoryData.unitIndex
          stationaryLabel index))
    components.slidingSourceIndex]
  rw [sourceLabeling_moving, sourceLabeling_moving]
  have unitWeight :
      source.cycleComponentWeight 𝒞 automorphism sourceCycle
          (source.topology.formal.raw.components.get
            components.slidingSourceIndex)
          𝒞.premodular.toFusionCategoryData.unitIndex = 1 := by
    unfold CanonicalPresentation.cycleComponentWeight
    rw [𝒞.premodular.quantumDimension_unit]
    rw [ThamThreeHandleVacuum.automorphismScalarPower_unitIndex]
    simp
  rw [unitWeight]
  simp only [one_mul, componentAt]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  exact congrArg
    (fun label =>
      source.cycleComponentWeight 𝒞 automorphism sourceCycle
        (source.topology.formal.raw.components.get index.1) label)
    (sourceLabeling_eq_away_from_moving
      components remaining movingLabel
        𝒞.premodular.toFusionCategoryData.unitIndex
        stationaryLabel index.property)

/--
Both selected handle weights factor, leaving the coefficient with both
selected labels specialized to the tensor unit.
-/
theorem sourceWeight_factor_both
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    sourceWeight 𝒞 automorphism components sourceCycle remaining
        movingLabel stationaryLabel =
      source.cycleComponentWeight 𝒞 automorphism sourceCycle
          (componentAt source.topology.formal
            components.slidingSourceIndex) movingLabel *
        source.cycleComponentWeight 𝒞 automorphism sourceCycle
          (componentAt source.topology.formal
            components.stationarySourceIndex) stationaryLabel *
        sourceWeight 𝒞 automorphism components sourceCycle remaining
          𝒞.premodular.toFusionCategoryData.unitIndex
          𝒞.premodular.toFusionCategoryData.unitIndex := by
  rw [sourceWeight_factor_moving]
  rw [sourceWeight_factor_stationary]
  simp only [mul_assoc]

/-- Exact source closed diagram in one visible two-label sector. -/
def sourceTerm
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    Diagram C .unit .unit :=
  source.termDiagram 𝒞
    (sourceLabeling components remaining movingLabel stationaryLabel)

/-- Exact target coefficient in one visible two-label sector. -/
noncomputable def targetWeight
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (targetCycle : target.DegreeTwoCycle)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) : K :=
  target.cycleGlobalWeight 𝒞 automorphism targetCycle
    (targetLabeling same components remaining movingLabel stationaryLabel)

/--
The stationary component weight also factors from the complete target
coefficient.  This is the target-side arithmetic half of premodular 2/2
sliding and uses only finite-product reindexing plus the tensor-unit laws.
-/
theorem targetWeight_factor_stationary
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (targetCycle : target.DegreeTwoCycle)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    targetWeight 𝒞 automorphism same components targetCycle remaining
        movingLabel stationaryLabel =
      target.cycleComponentWeight 𝒞 automorphism targetCycle
          (componentAt target.topology.formal
            components.stationaryTargetIndex) stationaryLabel *
        targetWeight 𝒞 automorphism same components targetCycle remaining
          movingLabel 𝒞.premodular.toFusionCategoryData.unitIndex := by
  classical
  unfold targetWeight CanonicalPresentation.cycleGlobalWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      target.cycleComponentWeight 𝒞 automorphism targetCycle
        (target.topology.formal.raw.components.get index)
        (targetLabeling same components remaining
          movingLabel stationaryLabel index))
    components.stationaryTargetIndex]
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      target.cycleComponentWeight 𝒞 automorphism targetCycle
        (target.topology.formal.raw.components.get index)
        (targetLabeling same components remaining movingLabel
          𝒞.premodular.toFusionCategoryData.unitIndex index))
    components.stationaryTargetIndex]
  rw [targetLabeling_stationary, targetLabeling_stationary]
  have unitWeight :
      target.cycleComponentWeight 𝒞 automorphism targetCycle
          (target.topology.formal.raw.components.get
            components.stationaryTargetIndex)
          𝒞.premodular.toFusionCategoryData.unitIndex = 1 := by
    unfold CanonicalPresentation.cycleComponentWeight
    rw [𝒞.premodular.quantumDimension_unit]
    rw [
      ThamThreeHandleVacuum.automorphismScalarPower_unitIndex]
    simp
  rw [unitWeight]
  simp only [one_mul, componentAt]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  exact congrArg
    (fun label =>
      target.cycleComponentWeight 𝒞 automorphism targetCycle
        (target.topology.formal.raw.components.get index.1) label)
    (targetLabeling_eq_away_from_stationary
      same components remaining movingLabel stationaryLabel
        𝒞.premodular.toFusionCategoryData.unitIndex index.property)

/-- The moving component weight factors from the target coefficient. -/
theorem targetWeight_factor_moving
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (targetCycle : target.DegreeTwoCycle)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    targetWeight 𝒞 automorphism same components targetCycle remaining
        movingLabel stationaryLabel =
      target.cycleComponentWeight 𝒞 automorphism targetCycle
          (componentAt target.topology.formal
            components.slidingTargetIndex) movingLabel *
        targetWeight 𝒞 automorphism same components targetCycle remaining
          𝒞.premodular.toFusionCategoryData.unitIndex stationaryLabel := by
  classical
  unfold targetWeight CanonicalPresentation.cycleGlobalWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      target.cycleComponentWeight 𝒞 automorphism targetCycle
        (target.topology.formal.raw.components.get index)
        (targetLabeling same components remaining
          movingLabel stationaryLabel index))
    components.slidingTargetIndex]
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      target.cycleComponentWeight 𝒞 automorphism targetCycle
        (target.topology.formal.raw.components.get index)
        (targetLabeling same components remaining
          𝒞.premodular.toFusionCategoryData.unitIndex
          stationaryLabel index))
    components.slidingTargetIndex]
  rw [targetLabeling_moving, targetLabeling_moving]
  have unitWeight :
      target.cycleComponentWeight 𝒞 automorphism targetCycle
          (target.topology.formal.raw.components.get
            components.slidingTargetIndex)
          𝒞.premodular.toFusionCategoryData.unitIndex = 1 := by
    unfold CanonicalPresentation.cycleComponentWeight
    rw [𝒞.premodular.quantumDimension_unit]
    rw [ThamThreeHandleVacuum.automorphismScalarPower_unitIndex]
    simp
  rw [unitWeight]
  simp only [one_mul, componentAt]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  exact congrArg
    (fun label =>
      target.cycleComponentWeight 𝒞 automorphism targetCycle
        (target.topology.formal.raw.components.get index.1) label)
    (targetLabeling_eq_away_from_moving
      same components remaining movingLabel
        𝒞.premodular.toFusionCategoryData.unitIndex
        stationaryLabel index.property)

/-- Both selected handle weights factor from the target coefficient. -/
theorem targetWeight_factor_both
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (targetCycle : target.DegreeTwoCycle)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    targetWeight 𝒞 automorphism same components targetCycle remaining
        movingLabel stationaryLabel =
      target.cycleComponentWeight 𝒞 automorphism targetCycle
          (componentAt target.topology.formal
            components.slidingTargetIndex) movingLabel *
        target.cycleComponentWeight 𝒞 automorphism targetCycle
          (componentAt target.topology.formal
            components.stationaryTargetIndex) stationaryLabel *
        targetWeight 𝒞 automorphism same components targetCycle remaining
          𝒞.premodular.toFusionCategoryData.unitIndex
          𝒞.premodular.toFusionCategoryData.unitIndex := by
  rw [targetWeight_factor_moving]
  rw [targetWeight_factor_stationary]
  simp only [mul_assoc]

/-- Exact target closed diagram in one visible two-label sector. -/
def targetTerm
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (remaining : Block (S := S) components)
    (movingLabel stationaryLabel : S) :
    Diagram C .unit .unit :=
  target.termDiagram 𝒞
    (targetLabeling same components remaining movingLabel stationaryLabel)

noncomputable def sourceBlock
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) components) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  ∑ movingLabel : S,
    ∑ stationaryLabel : S,
      sourceWeight 𝒞 automorphism components sourceCycle remaining
          movingLabel stationaryLabel •
        LinearDiagram.atom (R := K)
          (sourceTerm 𝒞 components remaining movingLabel stationaryLabel)

noncomputable def targetBlock
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (targetCycle : target.DegreeTwoCycle)
    (remaining : Block (S := S) components) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  ∑ movingLabel : S,
    ∑ stationaryLabel : S,
      targetWeight 𝒞 automorphism same components targetCycle remaining
          movingLabel stationaryLabel •
        LinearDiagram.atom (R := K)
          (targetTerm 𝒞 same components remaining
            movingLabel stationaryLabel)

theorem source_decomposition
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle) :
    source.cycleLinearDiagram 𝒞 automorphism sourceCycle =
      ∑ remaining : Block (S := S) components,
        sourceBlock 𝒞 automorphism components sourceCycle remaining := by
  classical
  unfold CanonicalPresentation.cycleLinearDiagram LinearDiagram.weightedSum
  rw [sum_splitAtTwo
    components.stationarySourceIndex
    components.slidingSourceIndex
    components.source_indices_distinct]
  rfl

theorem target_decomposition
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (targetCycle : target.DegreeTwoCycle) :
    target.cycleLinearDiagram 𝒞 automorphism targetCycle =
      ∑ remaining : Block (S := S) components,
        targetBlock 𝒞 automorphism same components
          targetCycle remaining := by
  classical
  unfold CanonicalPresentation.cycleLinearDiagram LinearDiagram.weightedSum
  rw [← same.sum_reindex
    (fun targetLabeling =>
      target.cycleGlobalWeight 𝒞 automorphism targetCycle targetLabeling •
        LinearDiagram.atom (R := K)
          (target.termDiagram 𝒞 targetLabeling))]
  rw [sum_splitAtTwo
    components.stationarySourceIndex
    components.slidingSourceIndex
    components.source_indices_distinct]
  rfl

end CanonicalSlideBlocks

/-
RETIRED LEGACY ROUTE (2026-07-27)

The remaining ordinary/label-indexed slide wrappers belonged to the replaced
modular evaluator route.  The role-aware main line closes 1/1 and 2/1 through
unit cutting and 2/2 through the explicit channel-weighted band movie.

/--
A syntactic finite partition of one complete ordinary slide sum into
admitted ordinary Kirby-colour windows.

A fixed global labeling is generally too small: the moving component must
remain expanded label by label, while the stationary component must retain
the complete ordinary Kirby colour.  Each block therefore retains the exact
double sum over those two coordinates, while the two decomposition equalities
prove that the blocks reassemble the exact source and target free linear
diagrams.
-/
structure OrdinarySlideBlockDecomposition
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (kind : SlideKind)
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String)
    (slidingComponentId stationaryComponentId : String)
    (sourceDiagram targetDiagram :
      LinearDiagram (R := K) (C := C) .unit .unit) where
  Block : Type
  blockFintype : Fintype Block
  before :
    Block → LinearDiagram (R := K) (C := C) .unit .unit
  after :
    Block → LinearDiagram (R := K) (C := C) .unit .unit
  slide :
    (block : Block) →
      CouponAdaptedKirbyColourSlideWindow 𝒞 automorphism kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (before block) (after block)
  source_decomposition : sourceDiagram = ∑ block, before block
  target_decomposition : targetDiagram = ∑ block, after block

namespace OrdinarySlideBlockDecomposition

/-- Every exact ordinary block decomposition preserves the full evaluation. -/
theorem eval_eq
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {kind : SlideKind}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {slidingComponentId stationaryComponentId : String}
    {sourceDiagram targetDiagram :
      LinearDiagram (R := K) (C := C) .unit .unit}
    (decomposition :
      OrdinarySlideBlockDecomposition 𝒞 automorphism kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        sourceDiagram targetDiagram) :
    LinearDiagram.eval sourceDiagram =
      LinearDiagram.eval targetDiagram := by
  letI := decomposition.blockFintype
  calc
    _ = LinearDiagram.eval (∑ block, decomposition.before block) :=
      congrArg LinearDiagram.eval decomposition.source_decomposition
    _ = LinearDiagram.eval (∑ block, decomposition.after block) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro block _
      exact (decomposition.slide block).eval_eq
    _ = _ :=
      congrArg LinearDiagram.eval
        decomposition.target_decomposition.symm

end OrdinarySlideBlockDecomposition

/--
The only non-formal-sum input needed for an ordinary slide: one genuine
ordinary-slide derivation for each canonically determined block.

The block type, both block endpoints, and both denominator decomposition
equalities are not fields.  They are derived by `toDecomposition`.
-/
structure CanonicalOrdinarySlideBlockProof
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle)
    (targetCycle : target.DegreeTwoCycle)
    (kind : SlideKind)
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String) where
  slide :
    (remaining : CanonicalSlideBlocks.Block (S := S) components) →
      CouponAdaptedKirbyColourSlideWindow 𝒞 automorphism
        kind orientation moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (CanonicalSlideBlocks.sourceBlock
          𝒞 automorphism components sourceCycle remaining)
        (CanonicalSlideBlocks.targetBlock
          𝒞 automorphism same components targetCycle remaining)

namespace CanonicalOrdinarySlideBlockProof

/--
Reassemble the complete ordinary slide from canonical finite-sum blocks.
-/
noncomputable def toDecomposition
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    {components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId}
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    {kind : SlideKind}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    (proof :
      CanonicalOrdinarySlideBlockProof
        𝒞 automorphism source target same components
        sourceCycle targetCycle kind orientation
        moveId sourceHash targetHash) :
    OrdinarySlideBlockDecomposition
      𝒞 automorphism
      kind orientation moveId sourceHash targetHash
      slidingComponentId stationaryComponentId
      (source.cycleLinearDiagram 𝒞 automorphism sourceCycle)
      (target.cycleLinearDiagram 𝒞 automorphism targetCycle) where
  Block := CanonicalSlideBlocks.Block (S := S) components
  blockFintype := inferInstance
  before :=
    CanonicalSlideBlocks.sourceBlock
      𝒞 automorphism components sourceCycle
  after :=
    CanonicalSlideBlocks.targetBlock
      𝒞 automorphism same components targetCycle
  slide := proof.slide
  source_decomposition :=
    CanonicalSlideBlocks.source_decomposition
      𝒞 automorphism components sourceCycle
  target_decomposition :=
    CanonicalSlideBlocks.target_decomposition
      𝒞 automorphism same components targetCycle

end CanonicalOrdinarySlideBlockProof

/--
Exact whole-sum geometry for a 1-over-1 or 2-over-1 move on one explicit
cycle, exposed as a finite partition into real ordinary-slide windows.
-/
structure OrdinaryCycleSlideGeometry
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (transport : MarkedH2Transport source.topology target.topology)
    (kind : SlideKind)
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String)
    (slidingComponentId stationaryComponentId : String) where
  blockDecomposition :
    (sourceCycle : source.DegreeTwoCycle) →
      OrdinarySlideBlockDecomposition
        𝒞 automorphism
        kind orientation moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (source.cycleLinearDiagram 𝒞 automorphism sourceCycle)
        (target.cycleLinearDiagram 𝒞 automorphism
          ((CycleTransport.ofMarkedH2Transport source target transport)
            |>.targetCycle sourceCycle))

namespace OrdinaryCycleSlideGeometry

/-- The complete explicit-cycle linear evaluations agree. -/
theorem cycleLinearDiagram_eval_transport
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {transport : MarkedH2Transport source.topology target.topology}
    {kind : SlideKind}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {slidingComponentId stationaryComponentId : String}
    (geometry :
      OrdinaryCycleSlideGeometry 𝒞 automorphism source target transport
        kind orientation moveId sourceHash targetHash
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle) :
    LinearDiagram.eval
        (source.cycleLinearDiagram 𝒞 automorphism sourceCycle) =
      LinearDiagram.eval
        (target.cycleLinearDiagram 𝒞 automorphism
          ((CycleTransport.ofMarkedH2Transport source target transport)
            |>.targetCycle sourceCycle)) :=
  (geometry.blockDecomposition sourceCycle).eval_eq

end OrdinaryCycleSlideGeometry

/--
A syntactic finite partition of one complete 2-over-2 sum into admitted
label-indexed sliding windows.

The two decomposition equalities live in the free module of diagrams.  They
cannot be replaced by an equality of evaluations or by a scalar equality.
-/
structure LabelIndexedSlideBlockDecomposition
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String)
    (slidingComponentId stationaryComponentId : String)
    (sourceDiagram targetDiagram :
      LinearDiagram (R := K) (C := C) .unit .unit) where
  Block : Type
  blockFintype : Fintype Block
  before :
    Block → LinearDiagram (R := K) (C := C) .unit .unit
  after :
    Block → LinearDiagram (R := K) (C := C) .unit .unit
  slide :
    (block : Block) →
      CouponAdaptedKirbyColourSlideWindow
        𝒞 automorphism .twoOverTwo orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (before block) (after block)
  source_decomposition : sourceDiagram = ∑ block, before block
  target_decomposition : targetDiagram = ∑ block, after block

namespace LabelIndexedSlideBlockDecomposition

/-- Every exact block decomposition preserves the complete evaluation. -/
theorem eval_eq
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {slidingComponentId stationaryComponentId : String}
    {sourceDiagram targetDiagram :
      LinearDiagram (R := K) (C := C) .unit .unit}
    (decomposition :
      LabelIndexedSlideBlockDecomposition 𝒞 automorphism orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        sourceDiagram targetDiagram) :
    LinearDiagram.eval sourceDiagram =
      LinearDiagram.eval targetDiagram := by
  letI := decomposition.blockFintype
  calc
    _ = LinearDiagram.eval (∑ block, decomposition.before block) :=
      congrArg LinearDiagram.eval decomposition.source_decomposition
    _ = LinearDiagram.eval (∑ block, decomposition.after block) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro block _
      exact (decomposition.slide block).eval_eq
    _ = _ :=
      congrArg LinearDiagram.eval
        decomposition.target_decomposition.symm

end LabelIndexedSlideBlockDecomposition

/--
The remaining local input for a generalized 2-over-2 slide: one restricted
label-indexed sliding derivation for each canonical block.
-/
structure CanonicalLabelIndexedSlideBlockProof
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle)
    (targetCycle : target.DegreeTwoCycle)
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String) where
  slide :
    (remaining : CanonicalSlideBlocks.Block (S := S) components) →
      CouponAdaptedKirbyColourSlideWindow
        𝒞 automorphism .twoOverTwo orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (CanonicalSlideBlocks.sourceBlock
          𝒞 automorphism components sourceCycle remaining)
        (CanonicalSlideBlocks.targetBlock
          𝒞 automorphism same components targetCycle remaining)

namespace CanonicalLabelIndexedSlideBlockProof

/-- Reassemble a complete 2-over-2 slide from canonical finite-sum blocks. -/
noncomputable def toDecomposition
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {same :
      SameComponentIndexChange
        source.topology.formal target.topology.formal}
    {slidingComponentId stationaryComponentId : String}
    {components :
      ResolvedSlideComponentPair
        source.topology.formal target.topology.formal same
        slidingComponentId stationaryComponentId}
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    (proof :
      CanonicalLabelIndexedSlideBlockProof
        𝒞 automorphism source target same components
        sourceCycle targetCycle orientation
        moveId sourceHash targetHash) :
    LabelIndexedSlideBlockDecomposition 𝒞 automorphism orientation
      moveId sourceHash targetHash
      slidingComponentId stationaryComponentId
      (source.cycleLinearDiagram 𝒞 automorphism sourceCycle)
      (target.cycleLinearDiagram 𝒞 automorphism targetCycle) where
  Block := CanonicalSlideBlocks.Block (S := S) components
  blockFintype := inferInstance
  before :=
    CanonicalSlideBlocks.sourceBlock
      𝒞 automorphism components sourceCycle
  after :=
    CanonicalSlideBlocks.targetBlock
      𝒞 automorphism same components targetCycle
  slide := proof.slide
  source_decomposition :=
    CanonicalSlideBlocks.source_decomposition
      𝒞 automorphism components sourceCycle
  target_decomposition :=
    CanonicalSlideBlocks.target_decomposition
      𝒞 automorphism same components targetCycle

end CanonicalLabelIndexedSlideBlockProof

/--
Exact whole-sum geometry for a generalized 2-over-2 slide.

The input must expose a finite syntactic partition into actual generalized
sliding windows; it cannot assume the complete evaluation equality directly.
-/
structure GeneralizedCycleSlideGeometry
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (transport : MarkedH2Transport source.topology target.topology)
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String)
    (slidingComponentId stationaryComponentId : String) where
  blockDecomposition :
    (sourceCycle : source.DegreeTwoCycle) →
      LabelIndexedSlideBlockDecomposition 𝒞 automorphism orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (source.cycleLinearDiagram 𝒞 automorphism sourceCycle)
        (target.cycleLinearDiagram 𝒞 automorphism
          ((CycleTransport.ofMarkedH2Transport source target transport)
            |>.targetCycle sourceCycle))

namespace GeneralizedCycleSlideGeometry

/-- The complete generalized explicit-cycle sums have equal evaluations. -/
theorem cycleLinearDiagram_eval_transport
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {transport : MarkedH2Transport source.topology target.topology}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {slidingComponentId stationaryComponentId : String}
    (geometry :
      GeneralizedCycleSlideGeometry 𝒞 automorphism source target transport
        orientation moveId sourceHash targetHash
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle) :
    LinearDiagram.eval
        (source.cycleLinearDiagram 𝒞 automorphism sourceCycle) =
      LinearDiagram.eval
        (target.cycleLinearDiagram 𝒞 automorphism
          ((CycleTransport.ofMarkedH2Transport source target transport)
            |>.targetCycle sourceCycle)) :=
  (geometry.blockDecomposition sourceCycle).eval_eq

end GeneralizedCycleSlideGeometry
-/

end TwistedYetter.Kirby.CanonicalCycleSlideGeometry
