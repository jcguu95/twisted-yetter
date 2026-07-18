import TwistedYetter.Kirby.KirbyHandleMoves

namespace TwistedYetter.Mutations.HandwrittenTargetCharacter

open TwistedYetter.Kirby.KirbyHandleMoves

/--
This must fail: a target character is derived contravariantly from the source
character and cannot be supplied independently.
-/
def unsafeTransport (basis : Nat ≃ Nat) :
    HomologicalTransport Nat Bool where
  basisChange := basis
  sourceCharacter := fun _ => false
  targetCharacter := fun _ => true

end TwistedYetter.Mutations.HandwrittenTargetCharacter
