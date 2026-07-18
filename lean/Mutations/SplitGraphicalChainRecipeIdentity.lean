import TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

namespace TwistedYetter.Mutations.SplitGraphicalChainRecipeIdentity

open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

/--
This must fail: graphical and chain consumers cannot carry independently
chosen recipe identities.
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
  graphicalRecipeId := "graphical-recipe"
  chainRecipeId := "different-chain-recipe"
  recipeId := "shared-recipe"
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

end TwistedYetter.Mutations.SplitGraphicalChainRecipeIdentity
