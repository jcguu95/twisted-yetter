import TwistedYetter.Kirby.ComputationArtifactImporter

open TwistedYetter.Kirby.ComputationArtifactImporter

private def dirtyArtifact : ArtifactEnvelope :=
  { toyExactControl.artifact with recordedDirty := true }

def invalidDirtyExact : ExactInvariantValueCertificate ℚ :=
  { toyExactControl with
    artifact := dirtyArtifact
    clean_source := rfl }
