import TwistedYetter.Kirby.KirbyCancellation

namespace TwistedYetter.Mutations.HandwrittenCancellationCharacter

open TwistedYetter.Kirby.KirbyCancellation

/--
This must fail: the character after cancellation is derived through the
homology equivalence and is not an independent field.
-/
def unsafeCharacter (equiv : Nat ≃ Bool) :
    CancellationHomologyTransport Nat Bool Bool where
  homologyEquiv := equiv
  beforeCharacter := fun _ => false
  afterCharacter := fun _ => true

end TwistedYetter.Mutations.HandwrittenCancellationCharacter
