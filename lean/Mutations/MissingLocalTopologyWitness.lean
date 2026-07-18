import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.MissingLocalTopologyWitness

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation

universe u

/-- This must fail: hashes alone do not assert that a local move occurred. -/
def unsafeMetadata
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type u} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (moveId sourceHash targetHash certificateHash : String)
    (sourceSound : sourceHash = source.formal.pinnedSourceHash)
    (targetSound : targetHash = target.formal.pinnedSourceHash)
    (certificateShape :
      RawPresentation.sha256Shape certificateHash = true) :
    TableTwoMoveMetadata source target where
  moveId := moveId
  sourcePresentationHash := sourceHash
  targetPresentationHash := targetHash
  source_hash_sound := sourceSound
  target_hash_sound := targetSound
  localTopologyCertificateHash := certificateHash
  local_certificate_hash_shape := certificateShape

end TwistedYetter.Mutations.MissingLocalTopologyWitness
