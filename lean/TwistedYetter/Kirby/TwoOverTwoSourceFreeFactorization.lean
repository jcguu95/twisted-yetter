import TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie

/-!
# Shared category-neutral window for a two-over-two slide

Source and target must use one common exterior.  Merely asking each endpoint
to admit some context would be too weak: the two contexts could be unrelated.

The single external input below therefore exposes one positively oriented
stationary strand and one shared free-diagram context.  Distinct source and
target local pieces fill the same hole.  No field mentions a category,
character, scalar, morphism, or evaluation equality.
-/

namespace TwistedYetter.Kirby.TwoOverTwoSourceFreeFactorization

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleSlideGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SelectedCoordinateFiniteSum
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance twoOverTwoSourceFreeRightRigid : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/-- The stationary occurrence selected by the oriented band convention. -/
def stationaryAtom
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    ComponentAtom :=
  let request := Request.twoOverTwo metadata countsSound
  match request.orientation with
  | .positive =>
      negativeAtom request.stationaryComponentId
  | .negative =>
      positiveAtom request.stationaryComponentId

/--
The actual local boundary at the two trivalent vertices.  Both participating
handles are exposed.  For a positive band this interprets as `x ⊗ yᘁ`; the
negative band retains the oppositely oriented stationary occurrence.
-/
def localBoundary
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    ComponentBoundary :=
  let request := Request.twoOverTwo metadata countsSound
  .tensor
    (.atom (positiveAtom request.slidingComponentId))
    (.atom (stationaryAtom metadata countsSound))

/--
One shared free exterior with the source and target local slide pieces.
-/
structure SharedFreeWindow
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) where
  context :
    ComponentDiagram.Context
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      .unit .unit
  sourcePiece :
    ComponentDiagram
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
  targetPiece :
    ComponentDiagram
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
  source_factorization :
    source.componentTermDiagram = context.plug sourcePiece
  target_factorization :
    target.componentTermDiagram = context.plug targetPiece

/--
The standard local topology fact for a 2/2 handle slide.

It exposes one shared exterior and contains no evaluator-side assertion.
-/
axiom standardSharedFreeWindow
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    SharedFreeWindow source target metadata countsSound

/-- The selected source moving coordinate receives `movingLabel`. -/
theorem sourceLabeling_moving
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    CanonicalSlideBlocks.sourceLabeling
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        remaining movingLabel stationaryLabel
        ((Request.twoOverTwo metadata countsSound).resolvedComponents
          |>.slidingSourceIndex) =
      movingLabel := by
  let components :=
    (Request.twoOverTwo metadata countsSound).resolvedComponents
  exact combineAtTwo_second
    components.stationarySourceIndex
    components.slidingSourceIndex
    components.source_indices_distinct
    stationaryLabel movingLabel remaining

/-- The selected target moving coordinate receives the transported label. -/
theorem targetLabeling_moving
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    CanonicalSlideBlocks.targetLabeling
        (Request.twoOverTwo metadata countsSound).sameComponentChange
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        remaining movingLabel stationaryLabel
        ((Request.twoOverTwo metadata countsSound).resolvedComponents
          |>.slidingTargetIndex) =
      movingLabel := by
  let request := Request.twoOverTwo metadata countsSound
  let components := request.resolvedComponents
  simp [
    CanonicalSlideBlocks.targetLabeling,
    SameComponentIndexChange.labelingEquiv,
    ResolvedSlideComponentPair.slidingTargetIndex,
    sourceLabeling_moving
  ]

/-- The selected source component receives `stationaryLabel`. -/
theorem sourceLabelOf_stationaryComponentId
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    source.labelOf 𝒞
        (CanonicalSlideBlocks.sourceLabeling
          (Request.twoOverTwo metadata countsSound).resolvedComponents
          remaining movingLabel stationaryLabel)
        (Request.twoOverTwo metadata countsSound).stationaryComponentId =
      stationaryLabel := by
  let request := Request.twoOverTwo metadata countsSound
  let components := request.resolvedComponents
  have indexSound :
      source.componentIndexing.indexOf request.stationaryComponentId =
        some components.stationarySourceIndex := by
    calc
      source.componentIndexing.indexOf request.stationaryComponentId =
        source.componentIndexing.indexOf
          (componentAt source.topology.formal
            components.stationarySourceIndex).componentId := by
              rw [components.stationary_source_id_sound]
      _ = some components.stationarySourceIndex :=
        source.componentIndexing.index_roundtrip
          components.stationarySourceIndex
  rw [CanonicalPresentation.labelOf, indexSound]
  exact CanonicalSlideBlocks.sourceLabeling_stationary
    components remaining movingLabel stationaryLabel

/-- The selected source moving component receives `movingLabel`. -/
theorem sourceLabelOf_slidingComponentId
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    source.labelOf 𝒞
        (CanonicalSlideBlocks.sourceLabeling
          (Request.twoOverTwo metadata countsSound).resolvedComponents
          remaining movingLabel stationaryLabel)
        (Request.twoOverTwo metadata countsSound).slidingComponentId =
      movingLabel := by
  let request := Request.twoOverTwo metadata countsSound
  let components := request.resolvedComponents
  have indexSound :
      source.componentIndexing.indexOf request.slidingComponentId =
        some components.slidingSourceIndex := by
    calc
      source.componentIndexing.indexOf request.slidingComponentId =
        source.componentIndexing.indexOf
          (componentAt source.topology.formal
            components.slidingSourceIndex).componentId := by
              rw [components.sliding_source_id_sound]
      _ = some components.slidingSourceIndex :=
        source.componentIndexing.index_roundtrip
          components.slidingSourceIndex
  rw [CanonicalPresentation.labelOf, indexSound]
  exact sourceLabeling_moving
    metadata countsSound remaining movingLabel stationaryLabel

/-- The selected target component receives the same stationary label. -/
theorem targetLabelOf_stationaryComponentId
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    target.labelOf 𝒞
        (CanonicalSlideBlocks.targetLabeling
          (Request.twoOverTwo metadata countsSound).sameComponentChange
          (Request.twoOverTwo metadata countsSound).resolvedComponents
          remaining movingLabel stationaryLabel)
        (Request.twoOverTwo metadata countsSound).stationaryComponentId =
      stationaryLabel := by
  let request := Request.twoOverTwo metadata countsSound
  let components := request.resolvedComponents
  have indexSound :
      target.componentIndexing.indexOf request.stationaryComponentId =
        some components.stationaryTargetIndex := by
    calc
      target.componentIndexing.indexOf request.stationaryComponentId =
        target.componentIndexing.indexOf
          (componentAt target.topology.formal
            components.stationaryTargetIndex).componentId := by
              rw [components.stationary_target_id_sound]
      _ = some components.stationaryTargetIndex :=
        target.componentIndexing.index_roundtrip
          components.stationaryTargetIndex
  rw [CanonicalPresentation.labelOf, indexSound]
  exact CanonicalSlideBlocks.targetLabeling_stationary
    request.sameComponentChange components remaining
      movingLabel stationaryLabel

/-- The selected target moving component receives `movingLabel`. -/
theorem targetLabelOf_slidingComponentId
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    target.labelOf 𝒞
        (CanonicalSlideBlocks.targetLabeling
          (Request.twoOverTwo metadata countsSound).sameComponentChange
          (Request.twoOverTwo metadata countsSound).resolvedComponents
          remaining movingLabel stationaryLabel)
        (Request.twoOverTwo metadata countsSound).slidingComponentId =
      movingLabel := by
  let request := Request.twoOverTwo metadata countsSound
  let components := request.resolvedComponents
  have indexSound :
      target.componentIndexing.indexOf request.slidingComponentId =
        some components.slidingTargetIndex := by
    calc
      target.componentIndexing.indexOf request.slidingComponentId =
        target.componentIndexing.indexOf
          (componentAt target.topology.formal
            components.slidingTargetIndex).componentId := by
              rw [components.sliding_target_id_sound]
      _ = some components.slidingTargetIndex :=
        target.componentIndexing.index_roundtrip
          components.slidingTargetIndex
  rw [CanonicalPresentation.labelOf, indexSound]
  exact targetLabeling_moving
    metadata countsSound remaining movingLabel stationaryLabel

/--
For a positive band, the source local hole is exactly `x ⊗ yᘁ`.
-/
theorem sourceLocalBoundary_interpret_positive
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (Request.twoOverTwo metadata countsSound).orientation = .positive)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    (localBoundary metadata countsSound).interpret 𝒞
        (source.labelOf 𝒞
          (CanonicalSlideBlocks.sourceLabeling
            (Request.twoOverTwo metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel)) =
      .tensor
        (.atom (𝒞.simple movingLabel))
        (.atom ((𝒞.simple stationaryLabel)ᘁ)) := by
  simp only [
    localBoundary,
    stationaryAtom,
    orientationSound,
    ComponentBoundary.interpret,
    ComponentAtom.interpret,
    positiveAtom,
    negativeAtom
  ]
  rw [sourceLabelOf_slidingComponentId]
  exact congrArg
    (fun rightDual =>
      Boundary.tensor
        (.atom (𝒞.simple movingLabel)) (.atom rightDual))
    (congrArg
      (fun simpleLabel => (𝒞.simple simpleLabel)ᘁ)
      (sourceLabelOf_stationaryComponentId
        𝒞 metadata countsSound remaining movingLabel stationaryLabel))

/--
For a negative band, the source local hole is exactly `x ⊗ y`.
-/
theorem sourceLocalBoundary_interpret_negative
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (Request.twoOverTwo metadata countsSound).orientation = .negative)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    (localBoundary metadata countsSound).interpret 𝒞
        (source.labelOf 𝒞
          (CanonicalSlideBlocks.sourceLabeling
            (Request.twoOverTwo metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel)) =
      .tensor
        (.atom (𝒞.simple movingLabel))
        (.atom (𝒞.simple stationaryLabel)) := by
  simp only [
    localBoundary,
    stationaryAtom,
    orientationSound,
    ComponentBoundary.interpret,
    ComponentAtom.interpret,
    positiveAtom
  ]
  rw [sourceLabelOf_slidingComponentId,
    sourceLabelOf_stationaryComponentId]

/--
For a positive band, the target local hole retains `x ⊗ yᘁ`.
-/
theorem targetLocalBoundary_interpret_positive
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (Request.twoOverTwo metadata countsSound).orientation = .positive)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    (localBoundary metadata countsSound).interpret 𝒞
        (target.labelOf 𝒞
          (CanonicalSlideBlocks.targetLabeling
            (Request.twoOverTwo metadata countsSound).sameComponentChange
            (Request.twoOverTwo metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel)) =
      .tensor
        (.atom (𝒞.simple movingLabel))
        (.atom ((𝒞.simple stationaryLabel)ᘁ)) := by
  simp only [
    localBoundary,
    stationaryAtom,
    orientationSound,
    ComponentBoundary.interpret,
    ComponentAtom.interpret,
    positiveAtom,
    negativeAtom
  ]
  rw [targetLabelOf_slidingComponentId]
  exact congrArg
    (fun rightDual =>
      Boundary.tensor
        (.atom (𝒞.simple movingLabel)) (.atom rightDual))
    (congrArg
      (fun simpleLabel => (𝒞.simple simpleLabel)ᘁ)
      (targetLabelOf_stationaryComponentId
        𝒞 metadata countsSound remaining movingLabel stationaryLabel))

/--
For a negative band, the target local hole retains `x ⊗ y`.
-/
theorem targetLocalBoundary_interpret_negative
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (orientationSound :
      (Request.twoOverTwo metadata countsSound).orientation = .negative)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    (localBoundary metadata countsSound).interpret 𝒞
        (target.labelOf 𝒞
          (CanonicalSlideBlocks.targetLabeling
            (Request.twoOverTwo metadata countsSound).sameComponentChange
            (Request.twoOverTwo metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel)) =
      .tensor
        (.atom (𝒞.simple movingLabel))
        (.atom (𝒞.simple stationaryLabel)) := by
  simp only [
    localBoundary,
    stationaryAtom,
    orientationSound,
    ComponentBoundary.interpret,
    ComponentAtom.interpret,
    positiveAtom
  ]
  rw [targetLabelOf_slidingComponentId,
    targetLabelOf_stationaryComponentId]

/-- Interpret the common exterior using the source labeling. -/
noncomputable def sourceContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :=
  (standardSharedFreeWindow metadata countsSound).context.interpret
    𝒞
    (source.labelOf 𝒞
      (CanonicalSlideBlocks.sourceLabeling
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        remaining movingLabel stationaryLabel))

/-- Interpret the same common exterior using the target labeling. -/
noncomputable def targetContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :=
  (standardSharedFreeWindow metadata countsSound).context.interpret
    𝒞
    (target.labelOf 𝒞
      (CanonicalSlideBlocks.targetLabeling
        (Request.twoOverTwo metadata countsSound).sameComponentChange
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        remaining movingLabel stationaryLabel))

/--
After the proved component-label transport, source and target interpret the
shared exterior as exactly the same categorical context.
-/
theorem sourceContext_eq_targetContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    HEq
      (sourceContext 𝒞 metadata countsSound remaining
        movingLabel stationaryLabel)
      (targetContext 𝒞 metadata countsSound remaining
        movingLabel stationaryLabel) := by
  unfold sourceContext targetContext
  have labels :
      target.labelOf 𝒞
          (CanonicalSlideBlocks.targetLabeling
            (Request.twoOverTwo metadata countsSound).sameComponentChange
            (Request.twoOverTwo metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel) =
        source.labelOf 𝒞
          (CanonicalSlideBlocks.sourceLabeling
            (Request.twoOverTwo metadata countsSound).resolvedComponents
            remaining movingLabel stationaryLabel) := by
    funext componentId
    exact
      TwistedYetter.Kirby.CanonicalMoveGeometry.SameComponentIndexChange.labelOf_transport
        𝒞 source target
        (Request.twoOverTwo metadata countsSound).sameComponentChange
        (CanonicalSlideBlocks.sourceLabeling
          (Request.twoOverTwo metadata countsSound).resolvedComponents
          remaining movingLabel stationaryLabel)
        componentId
  generalize
    source.labelOf 𝒞
        (CanonicalSlideBlocks.sourceLabeling
          (Request.twoOverTwo metadata countsSound).resolvedComponents
          remaining movingLabel stationaryLabel) = sourceLabels
    at labels ⊢
  generalize
    target.labelOf 𝒞
        (CanonicalSlideBlocks.targetLabeling
          (Request.twoOverTwo metadata countsSound).sameComponentChange
          (Request.twoOverTwo metadata countsSound).resolvedComponents
          remaining movingLabel stationaryLabel) = targetLabels
    at labels ⊢
  cases labels
  rfl

/-- Source endpoint binding derived from the shared free factorization. -/
theorem sourceTerm_eq_sharedContext_sourcePiece
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    CanonicalSlideBlocks.sourceTerm 𝒞
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        remaining movingLabel stationaryLabel =
      CategoricalTangle.Context.plug C
        (sourceContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        ((standardSharedFreeWindow metadata countsSound).sourcePiece.interpret
          𝒞
          (source.labelOf 𝒞
            (CanonicalSlideBlocks.sourceLabeling
              (Request.twoOverTwo metadata countsSound).resolvedComponents
              remaining movingLabel stationaryLabel))) := by
  unfold CanonicalSlideBlocks.sourceTerm
  unfold CanonicalPresentation.termDiagram
  rw [(standardSharedFreeWindow metadata countsSound).source_factorization]
  exact ComponentDiagram.Context.interpret_plug
    𝒞
    (source.labelOf 𝒞
      (CanonicalSlideBlocks.sourceLabeling
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        remaining movingLabel stationaryLabel))
    (standardSharedFreeWindow metadata countsSound).context
    (standardSharedFreeWindow metadata countsSound).sourcePiece

/-- Target endpoint binding derived from that same shared free exterior. -/
theorem targetTerm_eq_sharedContext_targetPiece
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    CanonicalSlideBlocks.targetTerm 𝒞
        (Request.twoOverTwo metadata countsSound).sameComponentChange
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        remaining movingLabel stationaryLabel =
      CategoricalTangle.Context.plug C
        (targetContext 𝒞 metadata countsSound remaining
          movingLabel stationaryLabel)
        ((standardSharedFreeWindow metadata countsSound).targetPiece.interpret
          𝒞
          (target.labelOf 𝒞
            (CanonicalSlideBlocks.targetLabeling
              (Request.twoOverTwo metadata countsSound).sameComponentChange
              (Request.twoOverTwo metadata countsSound).resolvedComponents
              remaining movingLabel stationaryLabel))) := by
  unfold CanonicalSlideBlocks.targetTerm
  unfold CanonicalPresentation.termDiagram
  rw [(standardSharedFreeWindow metadata countsSound).target_factorization]
  exact ComponentDiagram.Context.interpret_plug
    𝒞
    (target.labelOf 𝒞
      (CanonicalSlideBlocks.targetLabeling
        (Request.twoOverTwo metadata countsSound).sameComponentChange
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        remaining movingLabel stationaryLabel))
    (standardSharedFreeWindow metadata countsSound).context
    (standardSharedFreeWindow metadata countsSound).targetPiece

end TwistedYetter.Kirby.TwoOverTwoSourceFreeFactorization
