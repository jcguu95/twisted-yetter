import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.HandwrittenMovieTargetCharacter

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation

universe u

/-- This must fail: the target character is derived from the H2 equivalence. -/
def unsafeTransport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type u}
    {source target : SpecialKirbyPresentation manifold H2}
    (equiv : H2 ≃ H2)
    (hash : String)
    (hashShape : RawPresentation.sha256Shape hash = true) :
    MarkedH2Transport source target where
  homologyEquiv := equiv
  chainCertificateHash := hash
  chain_certificate_hash_shape := hashShape
  targetCharacter := fun _ => True

end TwistedYetter.Mutations.HandwrittenMovieTargetCharacter
