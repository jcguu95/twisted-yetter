import TwistedYetter.Fusion.Insertion

namespace TwistedYetter.Mutations.MissingIdentityResolutionSound

open CategoryTheory
open TwistedYetter.Fusion.Insertion

universe uR uC vC uS uI

variable {R : Type uR} [CommSemiring R]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear R C]
variable {S : Type uS} [Fintype S]
variable {I : S → Type uI} [∀ s, Fintype (I s)]

-- Expected failure: a list of channels is not an insertion theorem without
-- the exact weighted identity-resolution proof.
def forgedResolution
    (T : C)
    (simple : S → C)
    (weight : S → R)
    (projection : (s : S) → I s → (T ⟶ simple s))
    (inclusion : (s : S) → I s → (simple s ⟶ T)) :
    IdentityResolution (R := R) (S := S) (I := I) T where
  simple := simple
  weight := weight
  projection := projection
  inclusion := inclusion

end TwistedYetter.Mutations.MissingIdentityResolutionSound
