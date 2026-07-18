import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.MissingSpecialManifoldBinding

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.Presentation

universe u

/--
This must fail: a formal link cannot be relabelled as a presentation of an
arbitrary manifold without an explicit representation witness.
-/
def unsafePresentation
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type u)
    (formal : FormalPresentation)
    (counts : HandleCounts)
    (uniqueZero : counts.h0 = 1)
    (uniqueFour : counts.h4 = 1)
    (ordered : Prop)
    (orderedWitness : ordered)
    (representationHash h2Hash : String)
    (representationShape :
      RawPresentation.sha256Shape representationHash = true)
    (h2Shape : RawPresentation.sha256Shape h2Hash = true) :
    SpecialKirbyPresentation manifold H2 where
  formal := formal
  counts := counts
  uniqueZeroHandle := uniqueZero
  uniqueFourHandle := uniqueFour
  orderedByIncreasingIndex := ordered
  ordering_witness := orderedWitness
  representationCertificateHash := representationHash
  representation_certificate_hash_shape := representationShape
  h2ModelCertificateHash := h2Hash
  h2_model_certificate_hash_shape := h2Shape

end TwistedYetter.Mutations.MissingSpecialManifoldBinding
