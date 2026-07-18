import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.MissingUniqueFourHandle

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.PresentationExecutionTrace

universe u

/-- This must fail: the special endpoint normal form requires one 4-handle. -/
def unsafePresentation
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type u)
    [AddCommGroup H2]
    (formal : FormalPresentation)
    (execution : ClosedExecutionCertificate formal)
    (counts : HandleCounts)
    (uniqueZero : counts.h0 = 1)
    (ordered : Prop)
    (orderedWitness : ordered)
    (representedManifoldHash representationHash h2Hash : String)
    (representedManifoldSound :
      representedManifoldHash = manifold.manifoldSnapshotHash)
    (representsFixedManifold : Prop)
    (representationWitness : representsFixedManifold)
    (representationShape :
      RawPresentation.sha256Shape representationHash = true)
    (h2Shape : RawPresentation.sha256Shape h2Hash = true)
    (handleChain : HandleChainModel counts)
    (h2ModelEquiv : handleChain.SecondHomology ≃+ H2) :
    SpecialKirbyPresentation manifold H2 where
  formal := formal
  execution := execution
  counts := counts
  uniqueZeroHandle := uniqueZero
  orderedByIncreasingIndex := ordered
  ordering_witness := orderedWitness
  representedManifoldHash := representedManifoldHash
  represented_manifold_hash_sound := representedManifoldSound
  representsFixedManifold := representsFixedManifold
  representation_witness := representationWitness
  representationCertificateHash := representationHash
  representation_certificate_hash_shape := representationShape
  h2ModelCertificateHash := h2Hash
  h2_model_certificate_hash_shape := h2Shape
  handleChain := handleChain
  h2ModelEquiv := h2ModelEquiv

end TwistedYetter.Mutations.MissingUniqueFourHandle
