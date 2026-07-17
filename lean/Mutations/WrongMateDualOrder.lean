import TwistedYetter.Fusion.FrobeniusLinear

namespace TwistedYetter.Mutations.WrongMateDualOrder

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.FrobeniusLinear

universe uR u v

variable {R : Type uR} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear R C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [MonoidalLinear R C]

-- Expected failure: the forward mate cannot be reused for the oppositely
-- oriented coupon.  Its Hom spaces and exact-pairing orders differ.
noncomputable def forgedOppositeMate
    (X Y Y' Z Z' : C)
    [ExactPairing Y Y'] [ExactPairing Z' Z] :
    (X ⊗ Y' ⟶ Z) ≃ₗ[R] (Z' ⊗ X ⟶ Y) :=
  mateLinearEquiv (R := R) X Y Y' Z Z'

end TwistedYetter.Mutations.WrongMateDualOrder
