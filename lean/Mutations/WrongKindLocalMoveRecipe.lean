import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.WrongKindLocalMoveRecipe

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe u

/--
This must fail: a two-three-death recipe cannot populate the framed-isotopy
constructor.
-/
def unsafeMove
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type u} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (metadata : TableTwoMoveMetadata .twoThreeDeath source target)
    (counts : source.counts = target.counts)
    (transport : MarkedH2Transport source target) :
    TableTwoMove source target :=
  .framedIsotopy metadata counts transport

end TwistedYetter.Mutations.WrongKindLocalMoveRecipe
