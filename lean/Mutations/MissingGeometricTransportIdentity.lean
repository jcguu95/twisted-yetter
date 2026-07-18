import TwistedYetter.Kirby.ConcreteMarkedPairAssembly

namespace TwistedYetter.Kirby.ConcreteMarkedPairAssembly.Mutations

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uH

example
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (localCompiler : LocalMarkedH2Compiler manifold H2)
    (certificateHash : String)
    (hashShape : RawPresentation.sha256Shape certificateHash = true) :
    GeometricMarkedH2Compiler manifold H2 where
  localCompiler := localCompiler
  assemblyCertificateHash := certificateHash
  assembly_certificate_hash_shape := hashShape
  sourceRefs := []
  exactMarkedScope := ""
  sourceScopeCaveat := ""

end TwistedYetter.Kirby.ConcreteMarkedPairAssembly.Mutations
