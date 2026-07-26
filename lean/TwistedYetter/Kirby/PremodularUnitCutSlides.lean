import TwistedYetter.Kirby.PremodularDottedCutting

/-!
# Premodular dotted slides after tensor-unit cutting

These are the category-side local calculations for 2/1 and 1/1 slides.
The homological character is explicit in every statement.  It disappears
only because the special dotted cut retains tensor-unit channels.
-/

namespace TwistedYetter.Kirby.PremodularUnitCutSlides

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.ModularVacuumProjector
open TwistedYetter.Kirby.PremodularDottedCutting

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
Positive 2/1 local calculation.

The moving two-handle sees an arbitrary integral character coupon on the
puncture object.  The cut absorbs that coupon before braiding naturality
moves the unit channel through the strand.
-/
theorem twoOverOne_positive
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (X Y : C)
    (exponent : ℤ) :
    ((automorphismObjectPower η X exponent ≫
        specialDottedCutOperator 𝒞 X) ▷ Y) ≫
        (β_ X Y).hom =
      (β_ X Y).hom ≫
        (Y ◁ specialDottedCutOperator 𝒞 X) := by
  rw [automorphism_power_specialDottedCut_left]
  exact specialDottedCut_braiding_positive 𝒞 X Y

/-- Negative-crossing version of the same 2/1 calculation. -/
theorem twoOverOne_negative
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (X Y : C)
    (exponent : ℤ) :
    (Y ◁ (specialDottedCutOperator 𝒞 X ≫
        automorphismObjectPower η X exponent)) ≫
        (β_ X Y).inv =
      (β_ X Y).inv ≫
        (specialDottedCutOperator 𝒞 X ▷ Y) := by
  rw [automorphism_power_specialDottedCut_right]
  exact specialDottedCut_braiding_negative 𝒞 X Y

/--
The 1/1 local calculation with independent character exponents.

After both coupons are absorbed, the two disjoint unit cuts commute by the
monoidal interchange law.
-/
theorem oneOverOne
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (X Y : C)
    (leftExponent rightExponent : ℤ) :
    ((automorphismObjectPower η X leftExponent ≫
        specialDottedCutOperator 𝒞 X) ▷ Y) ≫
      (X ◁ (automorphismObjectPower η Y rightExponent ≫
        specialDottedCutOperator 𝒞 Y)) =
    (X ◁ (automorphismObjectPower η Y rightExponent ≫
        specialDottedCutOperator 𝒞 Y)) ≫
      ((automorphismObjectPower η X leftExponent ≫
        specialDottedCutOperator 𝒞 X) ▷ Y) := by
  rw [automorphism_power_specialDottedCut_left]
  rw [automorphism_power_specialDottedCut_left]
  exact disjoint_specialDottedCuts_interchange 𝒞 X Y

/-- Machine-visible scope: local categorical calculations, not global Cerf descent. -/
def currentStatus : String :=
  "PASS_PREMODULAR_UNIT_CUT_2_OVER_1_AND_1_OVER_1_LOCAL_CALCULATIONS"

end TwistedYetter.Kirby.PremodularUnitCutSlides
