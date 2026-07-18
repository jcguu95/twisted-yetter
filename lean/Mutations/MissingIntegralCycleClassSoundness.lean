import TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler

namespace TwistedYetter.Mutations.MissingIntegralCycleClassSoundness

open TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler
open TwistedYetter.Kirby.KirbyCompleteness

universe uH

/--
This must fail: a cycle vector cannot stand for a marked class until its
projection to handle-chain homology is proved to be that class.
-/
def unsafeModel
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation manifold H2}
    (model : IntegralTwoHandleCycleModel topology) :
    IntegralTwoHandleCycleModel topology where
  twoHandleComponent := model.twoHandleComponent
  two_handle_component_mem := model.two_handle_component_mem
  two_handle_component_role := model.two_handle_component_role
  twoHandleIndex? := model.twoHandleIndex?
  two_handle_index_roundtrip := model.two_handle_index_roundtrip
  two_handle_index_sound := model.two_handle_index_sound
  every_ordinary_component_indexed :=
    model.every_ordinary_component_indexed
  nonordinary_component_unindexed :=
    model.nonordinary_component_unindexed
  no_specially_dotted_components :=
    model.no_specially_dotted_components
  cycleRepresentative := model.cycleRepresentative
  cycleCertificateHash := model.cycleCertificateHash
  cycle_certificate_hash_shape := model.cycle_certificate_hash_shape
  componentIndexCertificateHash := model.componentIndexCertificateHash
  component_index_certificate_hash_shape :=
    model.component_index_certificate_hash_shape
  sourceRefs := model.sourceRefs
  exactScope := model.exactScope
  sourceScopeCaveat := model.sourceScopeCaveat

end TwistedYetter.Mutations.MissingIntegralCycleClassSoundness
