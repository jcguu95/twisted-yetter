import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Coupon transport through crossings and extrema

These are direct categorical theorems. They do not assume a custom
"coupons may slide" relation.
-/

namespace TwistedYetter.Kirby.CouponNaturality

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.ExactPairing
open CategoryTheory.HasLeftDual
open CategoryTheory.HasRightDual

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/--
Two arbitrary coupons pass through a positive crossing by braiding
naturality.
-/
theorem slide_through_positive_crossing [BraidedCategory C]
    {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g) ≫ (β_ Y Y').hom =
      (β_ X X').hom ≫ (g ⊗ₘ f) := by
  exact BraidedCategory.braiding_naturality f g

/--
Two arbitrary coupons pass through a negative crossing by inverse-braiding
naturality.
-/
theorem slide_through_negative_crossing [BraidedCategory C]
    {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g) ≫ (β_ Y' Y).inv =
      (β_ X' X).inv ≫ (g ⊗ₘ f) := by
  exact BraidedCategory.braiding_inv_naturality f g

/--
Sliding a coupon across a left-dual cup turns it into its left adjoint mate.
This is derived from the exact-pairing triangle identities.
-/
theorem slide_through_left_cup
    {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    η_ (ᘁY) Y ≫ (ᘁf) ▷ Y =
      η_ (ᘁX) X ≫ (ᘁX) ◁ f := by
  apply_fun (tensorRightHomEquiv _ (ᘁY) Y _).symm
  simp

/--
Sliding a coupon across a left-dual cap turns it into its left adjoint mate.
This is derived from the exact-pairing triangle identities.
-/
theorem slide_through_left_cap
    {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    X ◁ (ᘁf) ≫ ε_ _ _ =
      f ▷ _ ≫ ε_ _ _ := by
  apply_fun tensorLeftHomEquiv _ (ᘁX) X _
  simp

/--
Sliding a coupon across a right-dual cup turns it into its right adjoint
mate.
-/
theorem slide_through_right_cup
    {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    η_ Y (Yᘁ) ≫ _ ◁ (fᘁ) =
      η_ _ _ ≫ f ▷ _ := by
  apply_fun (tensorLeftHomEquiv _ Y (Yᘁ) _).symm
  simp

/--
Sliding a coupon across a right-dual cap turns it into its right adjoint
mate.
-/
theorem slide_through_right_cap
    {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    (fᘁ ▷ X) ≫ ε_ X (Xᘁ) =
      ((Yᘁ) ◁ f) ≫ ε_ Y (Yᘁ) := by
  apply_fun tensorRightHomEquiv _ X (Xᘁ) _
  simp

end TwistedYetter.Kirby.CouponNaturality
