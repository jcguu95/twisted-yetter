import TwistedYetter.Kirby.ComputationArtifactImporter

open TwistedYetter.Kirby.ComputationArtifactImporter

private def aliasedArtifact : ArtifactEnvelope :=
  { toyExactControl.artifact with mutableAliasCount := 1 }

def invalidAliasedExact : ExactInvariantValueCertificate ℚ :=
  { toyExactControl with
    artifact := aliasedArtifact
    alias_free := rfl }
