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
  cycleRepresentative := model.cycleRepresentative
  cycle_zero_sound := model.cycle_zero_sound
  cycleCertificateHash := model.cycleCertificateHash
  cycle_certificate_hash_shape := model.cycle_certificate_hash_shape
  sourceRefs := model.sourceRefs
  exactScope := model.exactScope
  sourceScopeCaveat := model.sourceScopeCaveat

end TwistedYetter.Mutations.MissingIntegralCycleClassSoundness
