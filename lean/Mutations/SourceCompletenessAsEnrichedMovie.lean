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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type u} [AddCommGroup H2]
    (source target : SpecialKirbyPresentation manifold H2) :
    TableTwoMovie source target :=
  standardSpecialKirbyCalculusConnected source target

end TwistedYetter.Mutations.SourceCompletenessAsEnrichedMovie
