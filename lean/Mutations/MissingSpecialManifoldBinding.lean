import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.MissingSpecialManifoldBinding

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.PresentationExecutionTrace

universe u

/--
This must fail: a mathematical presentation does not silently become a stored
repository artifact.  The outer provenance wrapper must be supplied explicitly.
-/
def unsafeStoredPresentation
    (H2 : Type u)
    [AddCommGroup H2]
    (presentation : SpecialKirbyPresentation H2) :
    StoredArtifact (SpecialKirbyPresentation H2) where
  payload := presentation

end TwistedYetter.Mutations.MissingSpecialManifoldBinding
