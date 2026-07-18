import TwistedYetter.Kirby.ComputationArtifactImporter

open TwistedYetter.Kirby.ComputationArtifactImporter

private def inconclusiveArtifact : ArtifactEnvelope :=
  { toyExactControl.artifact with inconclusiveCount := 1 }

def invalidInconclusiveExact : ExactInvariantValueCertificate ℚ :=
  { toyExactControl with
    artifact := inconclusiveArtifact
    no_inconclusive := rfl }
