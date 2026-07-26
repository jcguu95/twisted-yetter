import TwistedYetter.Kirby.SourceBackedKirbyCompleteness

namespace TwistedYetter.Mutations.SourceCompletenessAsEnrichedMovie

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe u

/--
This must fail: the source axiom gives only a topology movie.  It cannot be
used as a movie carrying chain-derived marked-homology transport.
-/
def unsafeMovie
    {H2 : Type u} [AddCommGroup H2]
    (source target : SpecialKirbyPresentation H2) :
    TableTwoMovie source target :=
  standardSpecialKirbyPresentationsConnected source target

end TwistedYetter.Mutations.SourceCompletenessAsEnrichedMovie
