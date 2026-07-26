import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.ZeroOneAsTableTwoMove

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe u

/-- This must fail: zero--one moves belong to general Cerf, not Table 2. -/
def unsafeMove
    {H2 : Type u} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata .oneTwoBirth source target)
    (transport : MarkedH2Transport source target) :
    TableTwoMove source target :=
  .zeroOneBirth metadata transport

end TwistedYetter.Mutations.ZeroOneAsTableTwoMove
