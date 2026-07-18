import TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

namespace TwistedYetter.Mutations.WrongGraphicalProgramKind

open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

/--
This must fail: a two--three graphical program cannot be attached to a
one--two handle edit.
-/
def unsafeRecipe
    {source target : FormalPresentation}
    (window : PresentationWindowEdit source target)
    (edit : HandleEdit .oneTwoBirth)
    (wrongEdit : HandleEdit .twoThreeBirth)
    (wrongProgram : GraphicalEditProgram wrongEdit)
    (sourceHash targetHash recipeHash : String)
    (sourceSound : sourceHash = source.pinnedSourceHash)
    (targetSound : targetHash = target.pinnedSourceHash)
    (hashShape : RawPresentation.sha256Shape recipeHash = true) :
    SourceBoundRecipe .oneTwoBirth source target where
  recipeId := "unsafe-wrong-graphical-program-kind"
  recipe_id_nonempty := by decide
  sourcePresentationHash := sourceHash
  source_hash_sound := sourceSound
  targetPresentationHash := targetHash
  target_hash_sound := targetSound
  window := window
  handleEdit := edit
  graphicalProgram := wrongProgram
  recipeSnapshotHash := recipeHash
  recipe_snapshot_hash_shape := hashShape
  sourceRefs := []
  exactScope := ""
  sourceScopeCaveat := ""

end TwistedYetter.Mutations.WrongGraphicalProgramKind
