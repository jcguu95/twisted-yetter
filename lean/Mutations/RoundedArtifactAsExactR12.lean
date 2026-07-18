import TwistedYetter.Kirby.ComputationArtifactImporter

open TwistedYetter.Kirby.ComputationArtifactImporter

def invalidRoundedExact : ExactInvariantValueCertificate ℚ :=
  { toyExactControl with
    arithmeticMode := .roundedComplex
    exact_arithmetic := Or.inl rfl }
