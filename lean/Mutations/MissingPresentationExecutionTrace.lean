import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.MissingPresentationExecutionTrace

open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation

universe u

/--
This must fail: a validated JSON wrapper is not enough. Every special Kirby
presentation must carry the exact closed typed execution trace.
-/
def unsafePresentation
    (H2 : Type u)
    [AddCommGroup H2]
    (base : SpecialKirbyPresentation H2) :
    SpecialKirbyPresentation H2 where
  formal := base.formal
  counts := base.counts
  twoHandleComponent := base.twoHandleComponent
  two_handle_component_mem := base.two_handle_component_mem
  two_handle_component_role := base.two_handle_component_role
  twoHandleIndex? := base.twoHandleIndex?
  two_handle_index_roundtrip := base.two_handle_index_roundtrip
  two_handle_index_sound := base.two_handle_index_sound
  every_two_handle_component_indexed := base.every_two_handle_component_indexed
  dotted_component_unindexed := base.dotted_component_unindexed
  componentIndexCertificateHash := base.componentIndexCertificateHash
  component_index_certificate_hash_shape :=
    base.component_index_certificate_hash_shape
  uniqueZeroHandle := base.uniqueZeroHandle
  uniqueFourHandle := base.uniqueFourHandle
  orderedByIncreasingIndex := base.orderedByIncreasingIndex
  ordering_witness := base.ordering_witness
  h2ModelCertificateHash := base.h2ModelCertificateHash
  h2_model_certificate_hash_shape := base.h2_model_certificate_hash_shape
  handleChain := base.handleChain
  h2ModelEquiv := base.h2ModelEquiv

end TwistedYetter.Mutations.MissingPresentationExecutionTrace
