import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.ZeroOneAsTableTwoMove

open TwistedYetter.Kirby.KirbyCompleteness

universe u

/-- This must fail: zero--one moves belong to general Cerf, not Table 2. -/
def unsafeMove
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type u}
    {source target : SpecialKirbyPresentation manifold H2}
    (metadata : TableTwoMoveMetadata source target)
    (transport : MarkedH2Transport source target) :
    TableTwoMove source target :=
  .zeroOneBirth metadata transport

end TwistedYetter.Mutations.ZeroOneAsTableTwoMove
