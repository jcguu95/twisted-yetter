import TwistedYetter.Kirby.SourceBackedKirbyCompleteness

namespace TwistedYetter.Mutations.MissingMovieEnrichmentSound

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe u

/--
This must fail: an enrichment function is not admitted unless forgetting its
chain data recovers the exact source topology movie.
-/
def unsafeEnrichment
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type u) [AddCommGroup H2]
    (enrich :
      {source target : SpecialKirbyPresentation manifold H2} →
        TopologicalTableTwoMovie source target →
          TableTwoMovie source target) :
    TableTwoMovieEnrichment manifold H2 where
  enrich := enrich

end TwistedYetter.Mutations.MissingMovieEnrichmentSound
