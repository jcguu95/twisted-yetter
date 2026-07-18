import TwistedYetter.Kirby.SourceBackedHandleChainNaturality

namespace TwistedYetter.Mutations.EvaluatorEqualityInsideStandardNaturalityInput

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBackedHandleChainNaturality

universe uH

/--
This must fail: the homology-domain package has no categorical evaluator
field.
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
  evaluatorEquality := True

end TwistedYetter.Mutations.EvaluatorEqualityInsideStandardNaturalityInput
