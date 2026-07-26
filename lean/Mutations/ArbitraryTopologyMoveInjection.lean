import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.ArbitraryTopologyMoveInjection

open TwistedYetter.Kirby.KirbyCompleteness

universe u

/-- This must fail: an arbitrary relation cannot enter the closed whitelist. -/
def unsafeMove
    {H2 : Type u} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (arbitraryRelation : Prop)
    (witness : arbitraryRelation) :
    TableTwoMove source target :=
  .fromArbitraryRelation arbitraryRelation witness

end TwistedYetter.Mutations.ArbitraryTopologyMoveInjection
