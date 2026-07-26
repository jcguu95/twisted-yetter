import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.HandwrittenMovieTargetCharacter

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.Presentation

universe u

/--
This must fail: even after supplying genuine chain data, the target character
is derived contravariantly and cannot be supplied by hand.
-/
def unsafeTransport
    {H2 : Type u} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (chainEquivalence :
      HandleChainEquivalence source.handleChain target.handleChain) :
    MarkedH2Transport source target where
  chainEquivalence := chainEquivalence
  targetCharacter := fun _ => True

end TwistedYetter.Mutations.HandwrittenMovieTargetCharacter
