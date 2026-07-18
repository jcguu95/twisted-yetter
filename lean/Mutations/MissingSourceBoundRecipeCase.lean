import TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

namespace TwistedYetter.Mutations.MissingSourceBoundRecipeCase

open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

/-- This must fail: omitting one directed case changes the denominator. -/
def incompleteKinds : List RecipeKind :=
  [
    .framedIsotopy,
    .oneOverOne,
    .twoOverOne,
    .twoOverTwo,
    .oneTwoBirth,
    .oneTwoDeath,
    .twoThreeBirth
  ]

theorem unsafeCount : incompleteKinds.length = 8 := by
  rfl

end TwistedYetter.Mutations.MissingSourceBoundRecipeCase
