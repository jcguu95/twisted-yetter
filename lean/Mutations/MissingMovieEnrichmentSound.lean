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
    (H2 : Type u) [AddCommGroup H2]
    (enrich :
      {source target : SpecialKirbyPresentation H2} →
        TopologicalTableTwoMovie source target →
          TableTwoMovie source target) :
    TableTwoMovieEnrichment H2 where
  enrich := enrich

end TwistedYetter.Mutations.MissingMovieEnrichmentSound
