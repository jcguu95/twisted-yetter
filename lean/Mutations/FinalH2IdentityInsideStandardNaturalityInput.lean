import TwistedYetter.Kirby.SourceBackedHandleChainNaturality

namespace TwistedYetter.Mutations.FinalH2IdentityInsideStandardNaturalityInput

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBackedHandleChainNaturality
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness
open TwistedYetter.Kirby.SourceBoundGeometricH2Compilation

universe uH

/--
This must fail: the imported standard handle-chain package supplies local
chain certificates, not a separately handwritten final identity law.
-/
def unsafeInput
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (input :
      StandardHandleChainNaturalityInput (manifold := manifold) H2) :
    StandardHandleChainNaturalityInput (manifold := manifold) H2 where
  compile := input.compile
  assemblyCertificateHash := input.assemblyCertificateHash
  assembly_certificate_hash_shape :=
    input.assembly_certificate_hash_shape
  transport_is_identity :=
    fun {source target} move =>
      (sourceBackedGeometricH2Compiler manifold H2)
        |>.local_transport_is_identity move

end TwistedYetter.Mutations.FinalH2IdentityInsideStandardNaturalityInput
