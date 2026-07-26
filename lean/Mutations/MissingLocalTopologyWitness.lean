import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.MissingLocalTopologyWitness

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe u

/-- This must fail: the complete typed local recipe cannot be omitted. -/
def unsafeMetadata
    {H2 : Type u} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (moveId sourceHash targetHash certificateHash : String)
    (sourceSound : sourceHash = source.formal.pinnedSourceHash)
    (targetSound : targetHash = target.formal.pinnedSourceHash)
    (certificateShape :
      RawPresentation.sha256Shape certificateHash = true) :
    TableTwoMoveMetadata .framedIsotopy source target where
  moveId := moveId
  sourcePresentationHash := sourceHash
  targetPresentationHash := targetHash
  source_hash_sound := sourceSound
  target_hash_sound := targetSound
  localTopologyCertificateHash := certificateHash
  local_certificate_hash_shape := certificateShape

end TwistedYetter.Mutations.MissingLocalTopologyWitness
