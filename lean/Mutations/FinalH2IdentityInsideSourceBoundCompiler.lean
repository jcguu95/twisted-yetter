import TwistedYetter.Kirby.SourceBoundGeometricH2Compiler

namespace TwistedYetter.Mutations.FinalH2IdentityInsideSourceBoundCompiler

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness
open TwistedYetter.Kirby.SourceBoundGeometricH2Compilation

universe uH

/--
This must fail: the source-bound compiler has no field for a directly supplied
final identity law.
-/
def unsafeCompiler
    (H2 : Type uH)
    [AddCommGroup H2]
    (compile :
      {source target : SpecialKirbyPresentation H2} →
      (move : TopologicalTableTwoMove source target) →
        SourceBoundChainMoveCertificate move)
    (assemblyCertificateHash : String)
    (hashShape :
      RawPresentation.sha256Shape assemblyCertificateHash = true) :
    SourceBoundGeometricH2Compiler H2 where
  compile := compile
  transport_is_identity := by
    intros
    rfl
  assemblyCertificateHash := assemblyCertificateHash
  assembly_certificate_hash_shape := hashShape
  sourceRefs := []
  exactMarkedScope := "mutation"
  sourceScopeCaveat := "mutation"

end TwistedYetter.Mutations.FinalH2IdentityInsideSourceBoundCompiler
