import TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

namespace TwistedYetter.Mutations.MissingGraphicalProgramInLocalRecipe

open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

/--
This must fail: a source-bound recipe cannot omit the exact closed graphical
program that is shared with its handle edit.
-/
def unsafeRecipe
    {source target : FormalPresentation}
    (window : PresentationWindowEdit source target)
    (edit : HandleEdit .oneTwoBirth)
    (sourceHash targetHash recipeHash : String)
    (sourceSound : sourceHash = source.pinnedSourceHash)
    (targetSound : targetHash = target.pinnedSourceHash)
    (hashShape : RawPresentation.sha256Shape recipeHash = true) :
    SourceBoundRecipe .oneTwoBirth source target where
  recipeId := "unsafe-missing-graphical-program"
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

end TwistedYetter.Mutations.MissingGraphicalProgramInLocalRecipe
