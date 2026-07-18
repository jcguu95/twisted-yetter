import TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

namespace TwistedYetter.Mutations.FinalEqualityInsideLocalMoveRecipe

open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

/--
This must fail: a source-bound recipe has no field for the desired final
evaluator equality.
-/
def unsafeRecipe
    {source target : FormalPresentation}
    (window : PresentationWindowEdit source target)
    (edit : HandleEdit .twoThreeDeath)
    (sourceHash targetHash recipeHash : String)
    (sourceSound : sourceHash = source.pinnedSourceHash)
    (targetSound : targetHash = target.pinnedSourceHash)
    (hashShape : RawPresentation.sha256Shape recipeHash = true) :
    SourceBoundRecipe .twoThreeDeath source target where
  recipeId := "unsafe-final-equality"
  recipe_id_nonempty := by decide
  sourcePresentationHash := sourceHash
  source_hash_sound := sourceSound
  targetPresentationHash := targetHash
  target_hash_sound := targetSound
  window := window
  handleEdit := edit
  recipeSnapshotHash := recipeHash
  recipe_snapshot_hash_shape := hashShape
  sourceRefs := []
  exactScope := ""
  sourceScopeCaveat := ""
  normalizedEvaluationEquality := True

end TwistedYetter.Mutations.FinalEqualityInsideLocalMoveRecipe
