import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.MissingInducedH2ChainWitness

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation

universe u

/--
This must fail: an arbitrary equivalence is not accepted without the explicit
claim that the pinned chain map induces it.
-/
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

end TwistedYetter.Mutations.MissingInducedH2ChainWitness
