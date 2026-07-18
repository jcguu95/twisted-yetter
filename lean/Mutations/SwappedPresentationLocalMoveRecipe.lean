import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.SwappedPresentationLocalMoveRecipe

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe u

/--
This must fail: a recipe indexed by target-to-source cannot be attached to
source-to-target metadata.
-/
def unsafeMetadata
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type u} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (recipe :
      SourceBoundRecipe .oneOverOne target.formal source.formal) :
    TableTwoMoveMetadata .oneOverOne source target where
  recipe := recipe

end TwistedYetter.Mutations.SwappedPresentationLocalMoveRecipe
