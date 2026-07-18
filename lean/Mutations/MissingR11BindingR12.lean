import TwistedYetter.Kirby.ComputationArtifactImporter

open TwistedYetter.Kirby.ComputationArtifactImporter

def invalidTargetWithoutR11Witness : ExactInvariantTarget ℚ where
  identity := toyExactControl.target.identity
  characterAssignmentHash :=
    toyExactControl.target.characterAssignmentHash
  evaluatorProfileHash := toyExactControl.target.evaluatorProfileHash
  evaluatorClosureHash := toyExactControl.target.evaluatorClosureHash
  r11BindingCertificateHash :=
    toyExactControl.target.r11BindingCertificateHash
  invariantValue := toyExactControl.target.invariantValue
  r11BindingIsValid := True
