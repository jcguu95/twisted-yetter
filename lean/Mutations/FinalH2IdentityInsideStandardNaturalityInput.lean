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
    (H2 : Type uH) [AddCommGroup H2]
    (input : StandardHandleChainNaturality H2) :
    StandardHandleChainNaturality H2 where
  compile := input.compile
  transport_is_identity :=
    fun {source target} move =>
      (sourceBackedGeometricH2Compiler H2)
        |>.local_transport_is_identity move

end TwistedYetter.Mutations.FinalH2IdentityInsideStandardNaturalityInput
