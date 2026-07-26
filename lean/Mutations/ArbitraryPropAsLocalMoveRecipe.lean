import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.ArbitraryPropAsLocalMoveRecipe

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe u

/--
This must fail: metadata no longer accepts an arbitrary proposition and its
witness as a substitute for a typed local recipe.
-/
def unsafeMetadata
    {H2 : Type u} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (claim : Prop)
    (witness : claim) :
    TableTwoMoveMetadata .framedIsotopy source target where
  locallyRealizesTableTwoMove := claim
  local_topology_witness := witness

end TwistedYetter.Mutations.ArbitraryPropAsLocalMoveRecipe
