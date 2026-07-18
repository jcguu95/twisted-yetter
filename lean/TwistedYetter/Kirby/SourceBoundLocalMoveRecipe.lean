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
