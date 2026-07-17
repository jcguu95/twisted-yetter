import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Linear Frobenius reciprocity

Mathlib provides the two rigid-category Hom-set equivalences used to bend a
string, but records them as plain equivalences.  In a linear monoidal category
the same maps are linear.  This module packages that fact and constructs the
specific mate map used in Bärenz--Barrett, Lemma 3.3, equation (3.1.6).
-/

namespace TwistedYetter.Fusion.FrobeniusLinear

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe uR u v

variable {R : Type uR} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear R C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [MonoidalLinear R C]

/-- Linear form of pulling a string on the left through a cup or cap. -/
noncomputable def tensorLeftHomLinearEquiv
    (X Y Y' Z : C) [ExactPairing Y Y'] :
    (Y' ⊗ X ⟶ Z) ≃ₗ[R] (X ⟶ Y ⊗ Z) where
  toFun := tensorLeftHomEquiv X Y Y' Z
  invFun := (tensorLeftHomEquiv X Y Y' Z).symm
  left_inv := (tensorLeftHomEquiv X Y Y' Z).left_inv
  right_inv := (tensorLeftHomEquiv X Y Y' Z).right_inv
  map_add' f g := by
    simp [tensorLeftHomEquiv]
  map_smul' scalar f := by
    simp [tensorLeftHomEquiv]

/-- Linear form of pulling a string on the right through a cup or cap. -/
noncomputable def tensorRightHomLinearEquiv
    (X Y Y' Z : C) [ExactPairing Y Y'] :
    (X ⊗ Y ⟶ Z) ≃ₗ[R] (X ⟶ Z ⊗ Y') where
  toFun := tensorRightHomEquiv X Y Y' Z
  invFun := (tensorRightHomEquiv X Y Y' Z).symm
  left_inv := (tensorRightHomEquiv X Y Y' Z).left_inv
  right_inv := (tensorRightHomEquiv X Y Y' Z).right_inv
  map_add' f g := by
    simp [tensorRightHomEquiv]
  map_smul' scalar f := by
    simp [tensorRightHomEquiv]

/--
The mate change of variables in Bärenz--Barrett (3.1.6):

`Hom(Z, X ⊗ Y') ≃ₗ Hom(Y, Z' ⊗ X)`.

The first inverse Frobenius map bends `Y'` down.  The second Frobenius map
bends `Z` up.  The exact pairings make the two dual conventions explicit.
-/
noncomputable def mateLinearEquiv
    (X Y Y' Z Z' : C)
    [ExactPairing Y Y'] [ExactPairing Z' Z] :
    (Z ⟶ X ⊗ Y') ≃ₗ[R] (Y ⟶ Z' ⊗ X) :=
  (tensorRightHomLinearEquiv (R := R) Z Y Y' X).symm.trans
    (tensorLeftHomLinearEquiv (R := R) Y Z' Z X)

/--
The mate on the oppositely oriented coupon:

`Hom(X ⊗ Y', Z) ≃ₗ Hom(Z' ⊗ X, Y)`.

It is deliberately separate from `mateLinearEquiv`: the two exact pairings
have opposite orders, and conflating them is a pivotal-convention error.
-/
noncomputable def dualMateLinearEquiv
    (X Y Y' Z Z' : C)
    [ExactPairing Y' Y] [ExactPairing Z Z'] :
    (X ⊗ Y' ⟶ Z) ≃ₗ[R] (Z' ⊗ X ⟶ Y) :=
  (tensorRightHomLinearEquiv (R := R) X Y' Y Z).trans
    (tensorLeftHomLinearEquiv (R := R) X Z Z' Y).symm

/-- The mate map is literally the two cup/cap bends, not an opaque bijection. -/
theorem mateLinearEquiv_apply
    (X Y Y' Z Z' : C)
    [ExactPairing Y Y'] [ExactPairing Z' Z]
    (f : Z ⟶ X ⊗ Y') :
    mateLinearEquiv (R := R) X Y Y' Z Z' f =
      tensorLeftHomEquiv Y Z' Z X
        ((tensorRightHomEquiv Z Y Y' X).symm f) :=
  rfl

/-- The inverse mate performs the two bends in the reverse order. -/
theorem mateLinearEquiv_symm_apply
    (X Y Y' Z Z' : C)
    [ExactPairing Y Y'] [ExactPairing Z' Z]
    (f : Y ⟶ Z' ⊗ X) :
    (mateLinearEquiv (R := R) X Y Y' Z Z').symm f =
      tensorRightHomEquiv Z Y Y' X
        ((tensorLeftHomEquiv Y Z' Z X).symm f) :=
  rfl

/-- The oppositely oriented mate is also the literal two-bend composite. -/
theorem dualMateLinearEquiv_apply
    (X Y Y' Z Z' : C)
    [ExactPairing Y' Y] [ExactPairing Z Z']
    (f : X ⊗ Y' ⟶ Z) :
    dualMateLinearEquiv (R := R) X Y Y' Z Z' f =
      (tensorLeftHomEquiv X Z Z' Y).symm
        (tensorRightHomEquiv X Y' Y Z f) :=
  rfl

end TwistedYetter.Fusion.FrobeniusLinear
