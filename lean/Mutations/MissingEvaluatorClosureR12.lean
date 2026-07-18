import TwistedYetter.Kirby.ComputationArtifactImporter

open TwistedYetter.Kirby.ComputationArtifactImporter

def invalidTargetWithoutEvaluatorClosure : ExactInvariantTarget ℚ where
  identity := toyExactControl.target.identity
  characterAssignmentHash :=
    toyExactControl.target.characterAssignmentHash
  evaluatorProfileHash := toyExactControl.target.evaluatorProfileHash
  r11BindingCertificateHash :=
    toyExactControl.target.r11BindingCertificateHash
  invariantValue := toyExactControl.target.invariantValue
  r11BindingIsValid := True
  r11_binding_witness := True.intro
