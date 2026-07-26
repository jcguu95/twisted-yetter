import Mathlib.Data.Fintype.BigOperators
import TwistedYetter.Kirby.KirbyHandleMoves

/-!
# Source-bound local recipes for special Kirby moves

This module is the category-neutral bridge between a serialized Kirby
presentation and the two downstream compilers.

A recipe records one literal replacement of component and slice-event
windows.  It also records one constructor from a closed handle-edit grammar.
The graphical evaluator and handle-chain compiler receive this same recipe
identity; neither side may substitute an independently named certificate.

The recipe deliberately contains no:

* equality of categorical evaluations;
* normalized scalar equality;
* chain map or homology map;
* arbitrary proposition saying that the move is valid.

Geometric completeness of these recipes remains the separately audited
special-Kirby topology domain axiom.  Evaluator and homology soundness must be
derived by their respective compilers.
-/

namespace TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.Presentation

/-- The exact eight directed local cases used by the special-link calculus. -/
inductive RecipeKind where
  | framedIsotopy
  | oneOverOne
  | twoOverOne
  | twoOverTwo
  | oneTwoBirth
  | oneTwoDeath
  | twoThreeBirth
  | twoThreeDeath
  deriving Repr, BEq, DecidableEq

/-- Machine-visible denominator of all directed local recipe kinds. -/
def requiredRecipeKinds : List RecipeKind :=
  [
    .framedIsotopy,
    .oneOverOne,
    .twoOverOne,
    .twoOverTwo,
    .oneTwoBirth,
    .oneTwoDeath,
    .twoThreeBirth,
    .twoThreeDeath
  ]

theorem recipe_kind_count :
    requiredRecipeKinds.length = 8 := by
  rfl

theorem recipe_kinds_unique :
    requiredRecipeKinds.Nodup := by
  decide

/--
A literal replacement window in two admitted serialized presentations.

The common prefix and suffix are data.  The four equality fields force the
recorded windows to reconstruct the exact source and target payloads; a hash
alone is not accepted as evidence that the replacement occurred.
-/
structure PresentationWindowEdit
    (source target : FormalPresentation) where
  commonComponentPrefix : List ComponentSpec
  sourceComponentWindow : List ComponentSpec
  targetComponentWindow : List ComponentSpec
  commonComponentSuffix : List ComponentSpec
  source_components_sound :
    source.raw.components =
      commonComponentPrefix ++ sourceComponentWindow ++
        commonComponentSuffix
  target_components_sound :
    target.raw.components =
      commonComponentPrefix ++ targetComponentWindow ++
        commonComponentSuffix
  commonEventPrefix : List SliceEvent
  sourceEventWindow : List SliceEvent
  targetEventWindow : List SliceEvent
  commonEventSuffix : List SliceEvent
  source_events_sound :
    source.raw.events =
      commonEventPrefix ++ sourceEventWindow ++ commonEventSuffix
  target_events_sound :
    target.raw.events =
      commonEventPrefix ++ targetEventWindow ++ commonEventSuffix
  source_event_window_nonempty : sourceEventWindow ≠ []
  target_event_window_nonempty : targetEventWindow ≠ []

/--
Closed combinatorial grammar for the handle operation represented by a
recipe.  The result type is indexed by the exact directed recipe kind.
-/
inductive HandleEdit : RecipeKind → Type
  | framedIsotopy
      (touchedEventIds : List String)
      (nonempty : touchedEventIds ≠ []) :
      HandleEdit .framedIsotopy
  | oneOverOne
      (orientation : BandOrientation)
      (slidingDottedId stationaryDottedId : String)
      (distinct : slidingDottedId ≠ stationaryDottedId) :
      HandleEdit .oneOverOne
  | twoOverOne
      (orientation : BandOrientation)
      (slidingTwoHandleId stationaryDottedId : String)
      (distinct : slidingTwoHandleId ≠ stationaryDottedId) :
      HandleEdit .twoOverOne
  | twoOverTwo
      (orientation : BandOrientation)
      (slidingTwoHandleId stationaryTwoHandleId : String)
      (distinct : slidingTwoHandleId ≠ stationaryTwoHandleId) :
      HandleEdit .twoOverTwo
  | oneTwoBirth
      (newDottedId newTwoHandleId : String)
      (distinct : newDottedId ≠ newTwoHandleId) :
      HandleEdit .oneTwoBirth
  | oneTwoDeath
      (removedDottedId removedTwoHandleId : String)
      (distinct : removedDottedId ≠ removedTwoHandleId) :
      HandleEdit .oneTwoDeath
  | twoThreeBirth
      (newTwoHandleId : String) :
      HandleEdit .twoThreeBirth
  | twoThreeDeath
      (removedTwoHandleId : String) :
      HandleEdit .twoThreeDeath

namespace HandleEdit

/-- Orientation recorded inside an exact 1-over-1 recipe. -/
def oneOverOneOrientation : HandleEdit .oneOverOne → BandOrientation
  | .oneOverOne orientation _ _ _ => orientation

/-- Sliding component recorded inside an exact 1-over-1 recipe. -/
def oneOverOneSlidingId : HandleEdit .oneOverOne → String
  | .oneOverOne _ sliding _ _ => sliding

/-- Stationary component recorded inside an exact 1-over-1 recipe. -/
def oneOverOneStationaryId : HandleEdit .oneOverOne → String
  | .oneOverOne _ _ stationary _ => stationary

/-- Orientation recorded inside an exact 2-over-1 recipe. -/
def twoOverOneOrientation : HandleEdit .twoOverOne → BandOrientation
  | .twoOverOne orientation _ _ _ => orientation

/-- Sliding component recorded inside an exact 2-over-1 recipe. -/
def twoOverOneSlidingId : HandleEdit .twoOverOne → String
  | .twoOverOne _ sliding _ _ => sliding

/-- Stationary component recorded inside an exact 2-over-1 recipe. -/
def twoOverOneStationaryId : HandleEdit .twoOverOne → String
  | .twoOverOne _ _ stationary _ => stationary

/-- Orientation recorded inside an exact 2-over-2 recipe. -/
def twoOverTwoOrientation : HandleEdit .twoOverTwo → BandOrientation
  | .twoOverTwo orientation _ _ _ => orientation

/-- Sliding component recorded inside an exact 2-over-2 recipe. -/
def twoOverTwoSlidingId : HandleEdit .twoOverTwo → String
  | .twoOverTwo _ sliding _ _ => sliding

/-- Stationary component recorded inside an exact 2-over-2 recipe. -/
def twoOverTwoStationaryId : HandleEdit .twoOverTwo → String
  | .twoOverTwo _ _ stationary _ => stationary

/-- Newly created dotted component in an exact 1--2 birth recipe. -/
def oneTwoBirthDottedId : HandleEdit .oneTwoBirth → String
  | .oneTwoBirth dotted _ _ => dotted

/-- Newly created ordinary component in an exact 1--2 birth recipe. -/
def oneTwoBirthTwoHandleId : HandleEdit .oneTwoBirth → String
  | .oneTwoBirth _ twoHandle _ => twoHandle

/-- Distinctness certificate retained by an exact 1--2 birth recipe. -/
def oneTwoBirthDistinct
    (edit : HandleEdit .oneTwoBirth) :
    oneTwoBirthDottedId edit ≠ oneTwoBirthTwoHandleId edit :=
  match edit with
  | .oneTwoBirth _ _ distinct => distinct

/-- Removed dotted component in an exact 1--2 death recipe. -/
def oneTwoDeathDottedId : HandleEdit .oneTwoDeath → String
  | .oneTwoDeath dotted _ _ => dotted

/-- Removed ordinary component in an exact 1--2 death recipe. -/
def oneTwoDeathTwoHandleId : HandleEdit .oneTwoDeath → String
  | .oneTwoDeath _ twoHandle _ => twoHandle

/-- Distinctness certificate retained by an exact 1--2 death recipe. -/
def oneTwoDeathDistinct
    (edit : HandleEdit .oneTwoDeath) :
    oneTwoDeathDottedId edit ≠ oneTwoDeathTwoHandleId edit :=
  match edit with
  | .oneTwoDeath _ _ distinct => distinct

/-- Newly created ordinary component in an exact 2--3 birth recipe. -/
def twoThreeBirthTwoHandleId : HandleEdit .twoThreeBirth → String
  | .twoThreeBirth twoHandle => twoHandle

/-- Removed ordinary component in an exact 2--3 death recipe. -/
def twoThreeDeathTwoHandleId : HandleEdit .twoThreeDeath → String
  | .twoThreeDeath twoHandle => twoHandle

end HandleEdit

/-- Finite component index of one exact serialized presentation. -/
abbrev ComponentIndex (presentation : FormalPresentation) :=
  Fin presentation.raw.components.length

/-- Read the exact component at one proved finite index. -/
def componentAt
    (presentation : FormalPresentation)
    (index : ComponentIndex presentation) : ComponentSpec :=
  presentation.raw.components.get index

/--
Component correspondence for a move that neither creates nor removes a link
component.

The equivalence is oriented from target indices to source indices so that a
source global labeling transports by precomposition.  Stable component IDs
are checked at every index; an arbitrary permutation with unrelated IDs is
not accepted.
-/
structure SameComponentIndexChange
    (source target : FormalPresentation) where
  targetToSource :
    ComponentIndex target ≃ ComponentIndex source
  component_id_sound :
    (targetIndex : ComponentIndex target) →
      (componentAt target targetIndex).componentId =
        (componentAt source (targetToSource targetIndex)).componentId
  component_role_sound :
    (targetIndex : ComponentIndex target) →
      (componentAt target targetIndex).role =
        (componentAt source (targetToSource targetIndex)).role

/--
The two actual source-component indices named by a same-component slide.

String IDs alone are not enough to select coordinates in the finite Kirby
colour sum.  This certificate resolves both IDs against the exact source
registry and proves that the two selected indices are distinct.  Their target
indices are then forced by the move's component correspondence.
-/
structure ResolvedSlideComponentPair
    (source target : FormalPresentation)
    (same : SameComponentIndexChange source target)
    (slidingComponentId stationaryComponentId : String) where
  slidingSourceIndex : ComponentIndex source
  stationarySourceIndex : ComponentIndex source
  sliding_source_id_sound :
    (componentAt source slidingSourceIndex).componentId =
      slidingComponentId
  stationary_source_id_sound :
    (componentAt source stationarySourceIndex).componentId =
      stationaryComponentId
  source_indices_distinct :
    slidingSourceIndex ≠ stationarySourceIndex

/--
Exact finite-set decomposition when target contains new local components.

The common summand is indexed by the source presentation.  The finite added
summand is kept separate so later finite-sum proofs cannot silently forget
the labels of a newly born Kirby component.
-/
structure AddedComponentIndexChange
    (source target : FormalPresentation)
    (addedCount : Nat) where
  targetDecomposition :
    ComponentIndex target ≃
      Sum (ComponentIndex source) (Fin addedCount)
  common_component_id_sound :
    (sourceIndex : ComponentIndex source) →
      (componentAt target
        (targetDecomposition.symm (Sum.inl sourceIndex))).componentId =
          (componentAt source sourceIndex).componentId

/-- Exact finite-set decomposition when source contains removed components. -/
structure RemovedComponentIndexChange
    (source target : FormalPresentation)
    (removedCount : Nat) where
  sourceDecomposition :
    ComponentIndex source ≃
      Sum (ComponentIndex target) (Fin removedCount)
  common_component_id_sound :
    (targetIndex : ComponentIndex target) →
      (componentAt source
        (sourceDecomposition.symm (Sum.inl targetIndex))).componentId =
          (componentAt target targetIndex).componentId

/-- First distinguished index in a two-element local summand. -/
def firstOfTwo : Fin 2 := ⟨0, by decide⟩

/-- Second distinguished index in a two-element local summand. -/
def secondOfTwo : Fin 2 := ⟨1, by decide⟩

/-- The sole distinguished index in a one-element local summand. -/
def onlyOne : Fin 1 := ⟨0, by decide⟩

/--
Complete category-neutral component geometry for the exact handle edit.

The constructors enforce the correct number and roles of added or removed
components.  This is finite-set and link-role data only: it contains no
category object, morphism, scalar, evaluator, or equality of evaluations.
-/
inductive ComponentIndexChange
    (source target : FormalPresentation) :
    {kind : RecipeKind} → HandleEdit kind → Type
  | framedIsotopy
      (touchedEventIds : List String)
      (nonempty : touchedEventIds ≠ [])
      (same : SameComponentIndexChange source target) :
      ComponentIndexChange source target
        (.framedIsotopy touchedEventIds nonempty)
  | oneOverOne
      (orientation : BandOrientation)
      (slidingDottedId stationaryDottedId : String)
      (distinct : slidingDottedId ≠ stationaryDottedId)
      (same : SameComponentIndexChange source target)
      (components :
        ResolvedSlideComponentPair source target same
          slidingDottedId stationaryDottedId)
      (sliding_role_sound :
        (componentAt source components.slidingSourceIndex).role =
          .dotted)
      (stationary_role_sound :
        (componentAt source components.stationarySourceIndex).role =
          .dotted) :
      ComponentIndexChange source target
        (.oneOverOne orientation
          slidingDottedId stationaryDottedId distinct)
  | twoOverOne
      (orientation : BandOrientation)
      (slidingTwoHandleId stationaryDottedId : String)
      (distinct : slidingTwoHandleId ≠ stationaryDottedId)
      (same : SameComponentIndexChange source target)
      (components :
        ResolvedSlideComponentPair source target same
          slidingTwoHandleId stationaryDottedId)
      (sliding_role_sound :
        (componentAt source components.slidingSourceIndex).role ≠
          .dotted)
      (stationary_role_sound :
        (componentAt source components.stationarySourceIndex).role =
          .dotted) :
      ComponentIndexChange source target
        (.twoOverOne orientation
          slidingTwoHandleId stationaryDottedId distinct)
  | twoOverTwo
      (orientation : BandOrientation)
      (slidingTwoHandleId stationaryTwoHandleId : String)
      (distinct : slidingTwoHandleId ≠ stationaryTwoHandleId)
      (same : SameComponentIndexChange source target)
      (components :
        ResolvedSlideComponentPair source target same
          slidingTwoHandleId stationaryTwoHandleId)
      (sliding_role_sound :
        (componentAt source components.slidingSourceIndex).role ≠
          .dotted)
      (stationary_role_sound :
        (componentAt source components.stationarySourceIndex).role ≠
          .dotted) :
      ComponentIndexChange source target
        (.twoOverTwo orientation
          slidingTwoHandleId stationaryTwoHandleId distinct)
  | oneTwoBirth
      (newDottedId newTwoHandleId : String)
      (distinct : newDottedId ≠ newTwoHandleId)
      (added : AddedComponentIndexChange source target 2)
      (dotted_id_sound :
        (componentAt target
          (added.targetDecomposition.symm
            (Sum.inr firstOfTwo))).componentId =
          newDottedId)
      (dotted_role_sound :
        (componentAt target
          (added.targetDecomposition.symm
            (Sum.inr firstOfTwo))).role = .dotted)
      (two_handle_id_sound :
        (componentAt target
          (added.targetDecomposition.symm
            (Sum.inr secondOfTwo))).componentId =
          newTwoHandleId)
      (two_handle_role_sound :
        (componentAt target
          (added.targetDecomposition.symm
            (Sum.inr secondOfTwo))).role ≠ .dotted) :
      ComponentIndexChange source target
        (.oneTwoBirth newDottedId newTwoHandleId distinct)
  | oneTwoDeath
      (removedDottedId removedTwoHandleId : String)
      (distinct : removedDottedId ≠ removedTwoHandleId)
      (removed : RemovedComponentIndexChange source target 2)
      (dotted_id_sound :
        (componentAt source
          (removed.sourceDecomposition.symm
            (Sum.inr firstOfTwo))).componentId =
          removedDottedId)
      (dotted_role_sound :
        (componentAt source
          (removed.sourceDecomposition.symm
            (Sum.inr firstOfTwo))).role = .dotted)
      (two_handle_id_sound :
        (componentAt source
          (removed.sourceDecomposition.symm
            (Sum.inr secondOfTwo))).componentId =
          removedTwoHandleId)
      (two_handle_role_sound :
        (componentAt source
          (removed.sourceDecomposition.symm
            (Sum.inr secondOfTwo))).role ≠ .dotted) :
      ComponentIndexChange source target
        (.oneTwoDeath
          removedDottedId removedTwoHandleId distinct)
  | twoThreeBirth
      (newTwoHandleId : String)
      (added : AddedComponentIndexChange source target 1)
      (two_handle_id_sound :
        (componentAt target
          (added.targetDecomposition.symm
            (Sum.inr onlyOne))).componentId =
          newTwoHandleId)
      (two_handle_role_sound :
        (componentAt target
          (added.targetDecomposition.symm
            (Sum.inr onlyOne))).role ≠ .dotted) :
      ComponentIndexChange source target
        (.twoThreeBirth newTwoHandleId)
  | twoThreeDeath
      (removedTwoHandleId : String)
      (removed : RemovedComponentIndexChange source target 1)
      (two_handle_id_sound :
        (componentAt source
          (removed.sourceDecomposition.symm
            (Sum.inr onlyOne))).componentId =
          removedTwoHandleId)
      (two_handle_role_sound :
        (componentAt source
          (removed.sourceDecomposition.symm
            (Sum.inr onlyOne))).role ≠ .dotted) :
      ComponentIndexChange source target
        (.twoThreeDeath removedTwoHandleId)

namespace SameComponentIndexChange

/-- Reindex all global labels along an exact same-component move. -/
def labelingEquiv
    {source target : FormalPresentation}
    (change : SameComponentIndexChange source target)
    (Label : Type*) :
    (ComponentIndex source → Label) ≃
      (ComponentIndex target → Label) where
  toFun sourceLabeling :=
    sourceLabeling ∘ change.targetToSource
  invFun targetLabeling :=
    targetLabeling ∘ change.targetToSource.symm
  left_inv sourceLabeling := by
    funext sourceIndex
    simp
  right_inv targetLabeling := by
    funext targetIndex
    simp

/--
Reindexing the complete finite labeling sum along a same-component move
neither loses nor duplicates a summand.
-/
theorem sum_reindex
    {source target : FormalPresentation}
    (change : SameComponentIndexChange source target)
    {Label Value : Type*}
    [Fintype Label]
    [AddCommMonoid Value]
    (summand : (ComponentIndex target → Label) → Value) :
    (∑ sourceLabeling,
        summand (change.labelingEquiv Label sourceLabeling)) =
      ∑ targetLabeling, summand targetLabeling :=
  Equiv.sum_comp (change.labelingEquiv Label) summand

end SameComponentIndexChange

namespace ResolvedSlideComponentPair

/-- Target index of the moving component, forced by component lineage. -/
def slidingTargetIndex
    {source target : FormalPresentation}
    {same : SameComponentIndexChange source target}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair source target same
        slidingComponentId stationaryComponentId) :
    ComponentIndex target :=
  same.targetToSource.symm components.slidingSourceIndex

/-- Target index of the stationary component, forced by component lineage. -/
def stationaryTargetIndex
    {source target : FormalPresentation}
    {same : SameComponentIndexChange source target}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair source target same
        slidingComponentId stationaryComponentId) :
    ComponentIndex target :=
  same.targetToSource.symm components.stationarySourceIndex

theorem sliding_target_id_sound
    {source target : FormalPresentation}
    {same : SameComponentIndexChange source target}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair source target same
        slidingComponentId stationaryComponentId) :
    (componentAt target components.slidingTargetIndex).componentId =
      slidingComponentId := by
  rw [same.component_id_sound]
  simpa [slidingTargetIndex] using components.sliding_source_id_sound

theorem stationary_target_id_sound
    {source target : FormalPresentation}
    {same : SameComponentIndexChange source target}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair source target same
        slidingComponentId stationaryComponentId) :
    (componentAt target components.stationaryTargetIndex).componentId =
      stationaryComponentId := by
  rw [same.component_id_sound]
  simpa [stationaryTargetIndex] using
    components.stationary_source_id_sound

theorem target_indices_distinct
    {source target : FormalPresentation}
    {same : SameComponentIndexChange source target}
    {slidingComponentId stationaryComponentId : String}
    (components :
      ResolvedSlideComponentPair source target same
        slidingComponentId stationaryComponentId) :
    components.slidingTargetIndex ≠ components.stationaryTargetIndex := by
  intro equal
  apply components.source_indices_distinct
  simpa [slidingTargetIndex, stationaryTargetIndex] using
    congrArg same.targetToSource equal

end ResolvedSlideComponentPair

namespace AddedComponentIndexChange

/--
Split one target labeling into the labels on common source components and
the labels on the newly added local components.
-/
def labelingEquiv
    {source target : FormalPresentation}
    {addedCount : Nat}
    (change : AddedComponentIndexChange source target addedCount)
    (Label : Type*) :
    (ComponentIndex target → Label) ≃
      ((ComponentIndex source → Label) × (Fin addedCount → Label)) where
  toFun targetLabeling :=
    (fun sourceIndex =>
      targetLabeling
        (change.targetDecomposition.symm (Sum.inl sourceIndex)),
    fun addedIndex =>
      targetLabeling
        (change.targetDecomposition.symm (Sum.inr addedIndex)))
  invFun splitLabeling := fun targetIndex =>
    match change.targetDecomposition targetIndex with
    | Sum.inl sourceIndex => splitLabeling.1 sourceIndex
    | Sum.inr addedIndex => splitLabeling.2 addedIndex
  left_inv targetLabeling := by
    funext targetIndex
    cases decomposition : change.targetDecomposition targetIndex with
    | inl sourceIndex =>
        change
          (match change.targetDecomposition targetIndex with
          | Sum.inl sourceIndex =>
              targetLabeling
                (change.targetDecomposition.symm
                  (Sum.inl sourceIndex))
          | Sum.inr addedIndex =>
              targetLabeling
                (change.targetDecomposition.symm
                  (Sum.inr addedIndex))) =
            targetLabeling targetIndex
        have inverse :
            change.targetDecomposition.symm (Sum.inl sourceIndex) =
              targetIndex := by
          exact change.targetDecomposition.injective
            (by simp [decomposition])
        simpa [decomposition] using congrArg targetLabeling inverse
    | inr addedIndex =>
        change
          (match change.targetDecomposition targetIndex with
          | Sum.inl sourceIndex =>
              targetLabeling
                (change.targetDecomposition.symm
                  (Sum.inl sourceIndex))
          | Sum.inr addedIndex =>
              targetLabeling
                (change.targetDecomposition.symm
                  (Sum.inr addedIndex))) =
            targetLabeling targetIndex
        have inverse :
            change.targetDecomposition.symm (Sum.inr addedIndex) =
              targetIndex := by
          exact change.targetDecomposition.injective
            (by simp [decomposition])
        simpa [decomposition] using congrArg targetLabeling inverse
  right_inv splitLabeling := by
    apply Prod.ext
    · funext sourceIndex
      simp
    · funext addedIndex
      simp

/--
The target labeling denominator is exactly the product of the common-source
labelings and the newly added local labelings.
-/
theorem sum_split
    {source target : FormalPresentation}
    {addedCount : Nat}
    (change : AddedComponentIndexChange source target addedCount)
    {Label Value : Type*}
    [Fintype Label]
    [AddCommMonoid Value]
    (summand : (ComponentIndex target → Label) → Value) :
    (∑ targetLabeling, summand targetLabeling) =
      ∑ splitLabeling,
        summand
          ((change.labelingEquiv Label).symm splitLabeling) :=
  (Equiv.sum_comp (change.labelingEquiv Label).symm summand).symm

/--
A product over target components factors into the common and newly added
component products.  This is the component-level algebra used later by the
1--2 and 2--3 finite-sum calculations.
-/
theorem component_product_split
    {source target : FormalPresentation}
    {addedCount : Nat}
    (change : AddedComponentIndexChange source target addedCount)
    {Value : Type*}
    [CommMonoid Value]
    (weight : ComponentIndex target → Value) :
    (∏ targetIndex, weight targetIndex) =
      (∏ sourceIndex,
          weight
            (change.targetDecomposition.symm
              (Sum.inl sourceIndex))) *
        ∏ addedIndex,
          weight
            (change.targetDecomposition.symm
              (Sum.inr addedIndex)) := by
  rw [← Equiv.prod_comp change.targetDecomposition.symm weight]
  exact Fintype.prod_sum_type _

end AddedComponentIndexChange

namespace RemovedComponentIndexChange

/--
Read a removal backwards as the corresponding finite component insertion.

This reuses the same finite equivalence; no reverse correspondence is
selected independently.
-/
def reverseAdded
    {source target : FormalPresentation}
    {removedCount : Nat}
    (change :
      RemovedComponentIndexChange source target removedCount) :
    AddedComponentIndexChange target source removedCount where
  targetDecomposition := change.sourceDecomposition
  common_component_id_sound := change.common_component_id_sound

/--
Split one source labeling into the labels retained by the target and the
labels on the removed local components.
-/
def labelingEquiv
    {source target : FormalPresentation}
    {removedCount : Nat}
    (change : RemovedComponentIndexChange source target removedCount)
    (Label : Type*) :
    (ComponentIndex source → Label) ≃
      ((ComponentIndex target → Label) × (Fin removedCount → Label)) where
  toFun sourceLabeling :=
    (fun targetIndex =>
      sourceLabeling
        (change.sourceDecomposition.symm (Sum.inl targetIndex)),
    fun removedIndex =>
      sourceLabeling
        (change.sourceDecomposition.symm (Sum.inr removedIndex)))
  invFun splitLabeling := fun sourceIndex =>
    match change.sourceDecomposition sourceIndex with
    | Sum.inl targetIndex => splitLabeling.1 targetIndex
    | Sum.inr removedIndex => splitLabeling.2 removedIndex
  left_inv sourceLabeling := by
    funext sourceIndex
    cases decomposition : change.sourceDecomposition sourceIndex with
    | inl targetIndex =>
        change
          (match change.sourceDecomposition sourceIndex with
          | Sum.inl targetIndex =>
              sourceLabeling
                (change.sourceDecomposition.symm
                  (Sum.inl targetIndex))
          | Sum.inr removedIndex =>
              sourceLabeling
                (change.sourceDecomposition.symm
                  (Sum.inr removedIndex))) =
            sourceLabeling sourceIndex
        have inverse :
            change.sourceDecomposition.symm (Sum.inl targetIndex) =
              sourceIndex := by
          exact change.sourceDecomposition.injective
            (by simp [decomposition])
        simpa [decomposition] using congrArg sourceLabeling inverse
    | inr removedIndex =>
        change
          (match change.sourceDecomposition sourceIndex with
          | Sum.inl targetIndex =>
              sourceLabeling
                (change.sourceDecomposition.symm
                  (Sum.inl targetIndex))
          | Sum.inr removedIndex =>
              sourceLabeling
                (change.sourceDecomposition.symm
                  (Sum.inr removedIndex))) =
            sourceLabeling sourceIndex
        have inverse :
            change.sourceDecomposition.symm (Sum.inr removedIndex) =
              sourceIndex := by
          exact change.sourceDecomposition.injective
            (by simp [decomposition])
        simpa [decomposition] using congrArg sourceLabeling inverse
  right_inv splitLabeling := by
    apply Prod.ext
    · funext targetIndex
      simp
    · funext removedIndex
      simp

/--
The source labeling denominator is exactly the product of retained target
labelings and removed local labelings.
-/
theorem sum_split
    {source target : FormalPresentation}
    {removedCount : Nat}
    (change : RemovedComponentIndexChange source target removedCount)
    {Label Value : Type*}
    [Fintype Label]
    [AddCommMonoid Value]
    (summand : (ComponentIndex source → Label) → Value) :
    (∑ sourceLabeling, summand sourceLabeling) =
      ∑ splitLabeling,
        summand
          ((change.labelingEquiv Label).symm splitLabeling) :=
  (Equiv.sum_comp (change.labelingEquiv Label).symm summand).symm

/-- Source-component products split into retained and removed factors. -/
theorem component_product_split
    {source target : FormalPresentation}
    {removedCount : Nat}
    (change : RemovedComponentIndexChange source target removedCount)
    {Value : Type*}
    [CommMonoid Value]
    (weight : ComponentIndex source → Value) :
    (∏ sourceIndex, weight sourceIndex) =
      (∏ targetIndex,
          weight
            (change.sourceDecomposition.symm
              (Sum.inl targetIndex))) *
        ∏ removedIndex,
          weight
            (change.sourceDecomposition.symm
              (Sum.inr removedIndex)) := by
  rw [← Equiv.prod_comp change.sourceDecomposition.symm weight]
  exact Fintype.prod_sum_type _

end RemovedComponentIndexChange

/--
Closed category-neutral tags for the framed-link isotopy generators.

These tags mirror the constructors of `PresentationIsotopy.TaggedMove`
without importing a category object, morphism, diagram, or evaluator
equality into the serialized topology recipe.
-/
inductive FramedIsotopyGenerator where
  | planarIdentityBefore
  | planarIdentityAfter
  | planarCompAssoc
  | criticalInterchange
  | reidemeisterIIPositive
  | reidemeisterIINegative
  | reidemeisterIII
  | rightPrimalSnake
  | rightDualSnake
  | leftPrimalSnake
  | leftDualSnake
  | framedPositive
  | framedNegative
  | couponPositiveCrossing
  | couponNegativeCrossing
  | couponRightCup
  | couponRightCap
  | couponLeftCup
  | couponLeftCap
  | couponPositiveTwist
  | couponNegativeTwist
  | closureCut
  deriving Repr, BEq, DecidableEq

/-- Exact denominator of category-neutral framed-isotopy generators. -/
def requiredFramedIsotopyGenerators : List FramedIsotopyGenerator :=
  [
    .planarIdentityBefore,
    .planarIdentityAfter,
    .planarCompAssoc,
    .criticalInterchange,
    .reidemeisterIIPositive,
    .reidemeisterIINegative,
    .reidemeisterIII,
    .rightPrimalSnake,
    .rightDualSnake,
    .leftPrimalSnake,
    .leftDualSnake,
    .framedPositive,
    .framedNegative,
    .couponPositiveCrossing,
    .couponNegativeCrossing,
    .couponRightCup,
    .couponRightCap,
    .couponLeftCup,
    .couponLeftCap,
    .couponPositiveTwist,
    .couponNegativeTwist,
    .closureCut
  ]

theorem framed_isotopy_generator_count :
    requiredFramedIsotopyGenerators.length = 22 := by
  rfl

theorem framed_isotopy_generators_unique :
    requiredFramedIsotopyGenerators.Nodup := by
  decide

/--
Exact event-level script for one cancelling one--two Hopf pair.

The source-side identity marker is retained separately because every
`PresentationWindowEdit` requires a nonempty window on both sides.
-/
structure OneTwoCancellationScript
    (dottedId twoHandleId : String) where
  identityEventId : String
  identityOrder : List String
  twoBirthId : String
  dottedBirthId : String
  firstCrossingId : String
  secondCrossingId : String
  dottedDeathId : String
  twoDeathId : String
  dottedPositiveId : String
  dottedNegativeId : String
  twoPositiveId : String
  twoNegativeId : String

namespace OneTwoCancellationScript

/-- Nonempty identity-side window of a one--two cancellation. -/
def identityEvents
    {dottedId twoHandleId : String}
    (script : OneTwoCancellationScript dottedId twoHandleId) :
    List SliceEvent :=
  [.planarIsotopy script.identityEventId script.identityOrder]

/-- Exact six-event positive Hopf-pair window. -/
def hopfEvents
    {dottedId twoHandleId : String}
    (script : OneTwoCancellationScript dottedId twoHandleId) :
    List SliceEvent :=
  [
    .birth script.twoBirthId twoHandleId
      script.twoPositiveId script.twoNegativeId 0,
    .birth script.dottedBirthId dottedId
      script.dottedPositiveId script.dottedNegativeId 0,
    .crossing script.firstCrossingId
      script.dottedNegativeId script.twoPositiveId .positive,
    .crossing script.secondCrossingId
      script.twoPositiveId script.dottedNegativeId .positive,
    .death script.dottedDeathId dottedId
      script.dottedPositiveId script.dottedNegativeId,
    .death script.twoDeathId twoHandleId
      script.twoPositiveId script.twoNegativeId
  ]

end OneTwoCancellationScript

/-- Exact event-level script for one cancelling two--three pair. -/
structure TwoThreeCancellationScript (twoHandleId : String) where
  identityEventId : String
  identityOrder : List String
  birthEventId : String
  deathEventId : String
  positiveId : String
  negativeId : String

namespace TwoThreeCancellationScript

/-- Nonempty identity-side window of a two--three cancellation. -/
def identityEvents
    {twoHandleId : String}
    (script : TwoThreeCancellationScript twoHandleId) :
    List SliceEvent :=
  [.planarIsotopy script.identityEventId script.identityOrder]

/-- Exact birth/death window of the isolated zero-framed component. -/
def zeroFramedEvents
    {twoHandleId : String}
    (script : TwoThreeCancellationScript twoHandleId) :
    List SliceEvent :=
  [
    .birth script.birthEventId twoHandleId
      script.positiveId script.negativeId 0,
    .death script.deathEventId twoHandleId
      script.positiveId script.negativeId
  ]

end TwoThreeCancellationScript

/--
Closed graphical program indexed by the exact handle edit.

The framed-isotopy constructor retains an ordered generator script and pins
its event IDs to the edit's touched-event denominator. Every other move has
one constructor whose indices repeat the exact orientation and component IDs
of its handle edit. There is no constructor from an arbitrary proposition,
diagram, or evaluator equality.
-/
inductive GraphicalEditProgram :
    {kind : RecipeKind} → HandleEdit kind → Type
  | framedIsotopy
      (touchedEventIds : List String)
      (nonempty : touchedEventIds ≠ [])
      (steps : List (String × FramedIsotopyGenerator))
      (steps_nonempty : steps ≠ [])
      (event_ids_sound :
        steps.map (fun step => step.1) = touchedEventIds) :
      GraphicalEditProgram
        (.framedIsotopy touchedEventIds nonempty)
  | oneOverOne
      (orientation : BandOrientation)
      (slidingDottedId stationaryDottedId : String)
      (distinct : slidingDottedId ≠ stationaryDottedId) :
      GraphicalEditProgram
        (.oneOverOne orientation
          slidingDottedId stationaryDottedId distinct)
  | twoOverOne
      (orientation : BandOrientation)
      (slidingTwoHandleId stationaryDottedId : String)
      (distinct : slidingTwoHandleId ≠ stationaryDottedId) :
      GraphicalEditProgram
        (.twoOverOne orientation
          slidingTwoHandleId stationaryDottedId distinct)
  | twoOverTwo
      (orientation : BandOrientation)
      (slidingTwoHandleId stationaryTwoHandleId : String)
      (distinct : slidingTwoHandleId ≠ stationaryTwoHandleId) :
      GraphicalEditProgram
        (.twoOverTwo orientation
          slidingTwoHandleId stationaryTwoHandleId distinct)
  | oneTwoBirth
      (newDottedId newTwoHandleId : String)
      (distinct : newDottedId ≠ newTwoHandleId)
      (script :
        OneTwoCancellationScript newDottedId newTwoHandleId) :
      GraphicalEditProgram
        (.oneTwoBirth newDottedId newTwoHandleId distinct)
  | oneTwoDeath
      (removedDottedId removedTwoHandleId : String)
      (distinct : removedDottedId ≠ removedTwoHandleId)
      (script :
        OneTwoCancellationScript removedDottedId removedTwoHandleId) :
      GraphicalEditProgram
        (.oneTwoDeath removedDottedId removedTwoHandleId distinct)
  | twoThreeBirth
      (newTwoHandleId : String)
      (script : TwoThreeCancellationScript newTwoHandleId) :
      GraphicalEditProgram (.twoThreeBirth newTwoHandleId)
  | twoThreeDeath
      (removedTwoHandleId : String)
      (script : TwoThreeCancellationScript removedTwoHandleId) :
      GraphicalEditProgram (.twoThreeDeath removedTwoHandleId)

/--
Concrete event-window obligation imposed by a graphical program.

Cancellation cases are literal list equalities.  They do not assert
isotopy, evaluator equality, or handle-chain transport.
-/
def GraphicalEditProgram.MatchesWindow
    {kind : RecipeKind}
    {source target : FormalPresentation}
    {edit : HandleEdit kind}
    (program : GraphicalEditProgram edit)
    (window : PresentationWindowEdit source target) : Prop :=
  match program with
  | .framedIsotopy .. => True
  | .oneOverOne .. => True
  | .twoOverOne .. => True
  | .twoOverTwo .. => True
  | .oneTwoBirth _ _ _ script =>
      window.sourceEventWindow = script.identityEvents ∧
        window.targetEventWindow = script.hopfEvents
  | .oneTwoDeath _ _ _ script =>
      window.sourceEventWindow = script.hopfEvents ∧
        window.targetEventWindow = script.identityEvents
  | .twoThreeBirth _ script =>
      window.sourceEventWindow = script.identityEvents ∧
        window.targetEventWindow = script.zeroFramedEvents
  | .twoThreeDeath _ script =>
      window.sourceEventWindow = script.zeroFramedEvents ∧
        window.targetEventWindow = script.identityEvents

namespace GraphicalEditProgram

/-- Read a one--two birth script without exposing the edit constructor. -/
def oneTwoBirthScriptOfEdit
    (edit : HandleEdit .oneTwoBirth)
    (program : GraphicalEditProgram edit) :
    OneTwoCancellationScript
      (HandleEdit.oneTwoBirthDottedId edit)
      (HandleEdit.oneTwoBirthTwoHandleId edit) :=
  match edit, program with
  | .oneTwoBirth _ _ _, .oneTwoBirth _ _ _ script => script

/-- Read the exact one--two birth script from its indexed program. -/
def oneTwoBirthScript
    {dottedId twoHandleId : String}
    {distinct : dottedId ≠ twoHandleId} :
    GraphicalEditProgram (.oneTwoBirth dottedId twoHandleId distinct) →
      OneTwoCancellationScript dottedId twoHandleId
  | .oneTwoBirth _ _ _ script => script

/-- Read a one--two death script without exposing the edit constructor. -/
def oneTwoDeathScriptOfEdit
    (edit : HandleEdit .oneTwoDeath)
    (program : GraphicalEditProgram edit) :
    OneTwoCancellationScript
      (HandleEdit.oneTwoDeathDottedId edit)
      (HandleEdit.oneTwoDeathTwoHandleId edit) :=
  match edit, program with
  | .oneTwoDeath _ _ _, .oneTwoDeath _ _ _ script => script

/-- Read the exact one--two death script from its indexed program. -/
def oneTwoDeathScript
    {dottedId twoHandleId : String}
    {distinct : dottedId ≠ twoHandleId} :
    GraphicalEditProgram (.oneTwoDeath dottedId twoHandleId distinct) →
      OneTwoCancellationScript dottedId twoHandleId
  | .oneTwoDeath _ _ _ script => script

/-- Read a two--three birth script without exposing the edit constructor. -/
def twoThreeBirthScriptOfEdit
    (edit : HandleEdit .twoThreeBirth)
    (program : GraphicalEditProgram edit) :
    TwoThreeCancellationScript
      (HandleEdit.twoThreeBirthTwoHandleId edit) :=
  match edit, program with
  | .twoThreeBirth _, .twoThreeBirth _ script => script

/-- Read the exact two--three birth script from its indexed program. -/
def twoThreeBirthScript
    {twoHandleId : String} :
    GraphicalEditProgram (.twoThreeBirth twoHandleId) →
      TwoThreeCancellationScript twoHandleId
  | .twoThreeBirth _ script => script

/-- Read a two--three death script without exposing the edit constructor. -/
def twoThreeDeathScriptOfEdit
    (edit : HandleEdit .twoThreeDeath)
    (program : GraphicalEditProgram edit) :
    TwoThreeCancellationScript
      (HandleEdit.twoThreeDeathTwoHandleId edit) :=
  match edit, program with
  | .twoThreeDeath _, .twoThreeDeath _ script => script

/-- Read the exact two--three death script from its indexed program. -/
def twoThreeDeathScript
    {twoHandleId : String} :
    GraphicalEditProgram (.twoThreeDeath twoHandleId) →
      TwoThreeCancellationScript twoHandleId
  | .twoThreeDeath _ script => script

/-- Expand a one--two birth window certificate to its two literal scripts. -/
theorem oneTwoBirth_matchesWindow
    {source target : FormalPresentation}
    (edit : HandleEdit .oneTwoBirth)
    (program : GraphicalEditProgram edit)
    (window : PresentationWindowEdit source target)
    (sound : program.MatchesWindow window) :
    window.sourceEventWindow =
        (oneTwoBirthScriptOfEdit edit program).identityEvents ∧
      window.targetEventWindow =
        (oneTwoBirthScriptOfEdit edit program).hopfEvents := by
  cases edit
  cases program
  exact sound

/-- Expand a one--two death window certificate to its two literal scripts. -/
theorem oneTwoDeath_matchesWindow
    {source target : FormalPresentation}
    (edit : HandleEdit .oneTwoDeath)
    (program : GraphicalEditProgram edit)
    (window : PresentationWindowEdit source target)
    (sound : program.MatchesWindow window) :
    window.sourceEventWindow =
        (oneTwoDeathScriptOfEdit edit program).hopfEvents ∧
      window.targetEventWindow =
        (oneTwoDeathScriptOfEdit edit program).identityEvents := by
  cases edit
  cases program
  exact sound

/-- Expand a two--three birth window certificate to its two literal scripts. -/
theorem twoThreeBirth_matchesWindow
    {source target : FormalPresentation}
    (edit : HandleEdit .twoThreeBirth)
    (program : GraphicalEditProgram edit)
    (window : PresentationWindowEdit source target)
    (sound : program.MatchesWindow window) :
    window.sourceEventWindow =
        (twoThreeBirthScriptOfEdit edit program).identityEvents ∧
      window.targetEventWindow =
        (twoThreeBirthScriptOfEdit edit program).zeroFramedEvents := by
  cases edit
  cases program
  exact sound

/-- Expand a two--three death window certificate to its two literal scripts. -/
theorem twoThreeDeath_matchesWindow
    {source target : FormalPresentation}
    (edit : HandleEdit .twoThreeDeath)
    (program : GraphicalEditProgram edit)
    (window : PresentationWindowEdit source target)
    (sound : program.MatchesWindow window) :
    window.sourceEventWindow =
        (twoThreeDeathScriptOfEdit edit program).zeroFramedEvents ∧
      window.targetEventWindow =
        (twoThreeDeathScriptOfEdit edit program).identityEvents := by
  cases edit
  cases program
  exact sound

end GraphicalEditProgram

/--
One immutable local recipe shared by graphical and chain compilation.

There is one identity and one content hash for both downstream consumers.
The structure does not have separate graphical and chain recipe IDs, so those
IDs cannot silently drift apart.
-/
structure SourceBoundRecipe
    (kind : RecipeKind)
    (source target : FormalPresentation) where
  recipeId : String
  recipe_id_nonempty : recipeId ≠ ""
  sourcePresentationHash : String
  source_hash_sound :
    sourcePresentationHash = source.pinnedSourceHash
  targetPresentationHash : String
  target_hash_sound :
    targetPresentationHash = target.pinnedSourceHash
  window : PresentationWindowEdit source target
  handleEdit : HandleEdit kind
  componentIndexChange :
    ComponentIndexChange source target handleEdit
  graphicalProgram : GraphicalEditProgram handleEdit
  graphical_window_sound :
    graphicalProgram.MatchesWindow window
  recipeSnapshotHash : String
  recipe_snapshot_hash_shape :
    RawPresentation.sha256Shape recipeSnapshotHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace SourceBoundRecipe

/-- Graphical compilation is pinned to the sole shared recipe identity. -/
def graphicalCompilerRecipeId
    {kind : RecipeKind}
    {source target : FormalPresentation}
    (recipe : SourceBoundRecipe kind source target) : String :=
  recipe.recipeId

/-- Handle-chain compilation is pinned to the same shared recipe identity. -/
def chainCompilerRecipeId
    {kind : RecipeKind}
    {source target : FormalPresentation}
    (recipe : SourceBoundRecipe kind source target) : String :=
  recipe.recipeId

theorem graphical_and_chain_recipe_ids_agree
    {kind : RecipeKind}
    {source target : FormalPresentation}
    (recipe : SourceBoundRecipe kind source target) :
    recipe.graphicalCompilerRecipeId =
      recipe.chainCompilerRecipeId := by
  rfl

end SourceBoundRecipe

end TwistedYetter.Kirby.SourceBoundLocalMoveRecipe
