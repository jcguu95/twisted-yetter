import TwistedYetter.Kirby.ComponentBoundaryCharacter
import TwistedYetter.Kirby.LinearContext
import TwistedYetter.Kirby.RoleAwareComponentDiagram

/-!
# Moving a boundary-character scalar into a visible coupon

The role-aware evaluator stores character coefficients as scalars.  Dotted
slide proofs use visible coupons.  This file proves the exact bridge between
those two representations, including arbitrary oriented puncture words and
arbitrary unchanged exterior contexts.
-/

namespace TwistedYetter.Kirby.RoleAwareCharacterCouponBridge

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentBoundaryCharacter
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.LinearContext
open TwistedYetter.Kirby.RoleAwareComponentDiagram

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
One scalar boundary character is exactly one visible character coupon before
the normalized special dotted cut.
-/
theorem scalar_smul_specialCut_eval_eq_characterCouponCut_eval
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId : String)
    (boundary : ComponentBoundary)
    (exponent : ℤ) :
    boundaryCharacterPower 𝒞.toFusionCategoryData η labelOf
        boundary exponent •
      Diagram.eval C
        ((RoleAwareDiagram.specialDottedCut dottedId boundary).interpret
          𝒞 η labelOf) =
      Diagram.eval C
        ((RoleAwareDiagram.comp
          (RoleAwareDiagram.characterPower boundary exponent)
          (RoleAwareDiagram.specialDottedCut dottedId boundary)).interpret
            𝒞 η labelOf) := by
  simp only [RoleAwareDiagram.interpret,
    RoleAwareDiagram.interpretSpecialDottedCut, Diagram.eval]
  rw [automorphismObjectPower_eq_boundaryCharacterPower_smul_identity]
  simp

/-- The identical bridge with the visible coupon placed after the cut. -/
theorem scalar_smul_specialCut_eval_eq_cutCharacterCoupon_eval
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId : String)
    (boundary : ComponentBoundary)
    (exponent : ℤ) :
    boundaryCharacterPower 𝒞.toFusionCategoryData η labelOf
        boundary exponent •
      Diagram.eval C
        ((RoleAwareDiagram.specialDottedCut dottedId boundary).interpret
          𝒞 η labelOf) =
      Diagram.eval C
        ((RoleAwareDiagram.comp
          (RoleAwareDiagram.specialDottedCut dottedId boundary)
          (RoleAwareDiagram.characterPower boundary exponent)).interpret
            𝒞 η labelOf) := by
  simp only [RoleAwareDiagram.interpret,
    RoleAwareDiagram.interpretSpecialDottedCut, Diagram.eval]
  rw [automorphismObjectPower_eq_boundaryCharacterPower_smul_identity]
  simp

/--
The same scalar-to-coupon conversion remains valid in every unchanged
role-aware exterior.
-/
theorem scalar_smul_specialCut_eval_eq_characterCouponCut_eval_inContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId : String)
    (boundary : ComponentBoundary)
    (exponent : ℤ)
    {wholeSource wholeTarget : ComponentBoundary}
    (context :
      RoleAwareDiagram.Context boundary boundary wholeSource wholeTarget) :
    boundaryCharacterPower 𝒞.toFusionCategoryData η labelOf
        boundary exponent •
      Diagram.eval C
        ((context.plug
          (RoleAwareDiagram.specialDottedCut dottedId boundary)).interpret
            𝒞 η labelOf) =
      Diagram.eval C
        ((context.plug
          (RoleAwareDiagram.comp
            (RoleAwareDiagram.characterPower boundary exponent)
            (RoleAwareDiagram.specialDottedCut dottedId boundary))).interpret
              𝒞 η labelOf) := by
  rw [context.interpret_plug, context.interpret_plug]
  let categoricalContext := context.interpret 𝒞 η labelOf
  calc
    _ = boundaryCharacterPower 𝒞.toFusionCategoryData η labelOf
          boundary exponent •
        evalContextLinearMap (R := K) categoricalContext
          (Diagram.eval C
            ((RoleAwareDiagram.specialDottedCut dottedId boundary).interpret
              𝒞 η labelOf)) := by
        rw [evalContextLinearMap_diagram]
    _ = evalContextLinearMap (R := K) categoricalContext
          (boundaryCharacterPower 𝒞.toFusionCategoryData η labelOf
              boundary exponent •
            Diagram.eval C
              ((RoleAwareDiagram.specialDottedCut dottedId boundary).interpret
                𝒞 η labelOf)) := by
        rw [LinearMap.map_smul]
    _ = evalContextLinearMap (R := K) categoricalContext
          (Diagram.eval C
            ((RoleAwareDiagram.comp
              (RoleAwareDiagram.characterPower boundary exponent)
              (RoleAwareDiagram.specialDottedCut dottedId boundary)).interpret
                𝒞 η labelOf)) := by
        rw [scalar_smul_specialCut_eval_eq_characterCouponCut_eval]
    _ = _ := by
        rw [evalContextLinearMap_diagram]

/-- Context closure for the coupon-after-cut convention. -/
theorem scalar_smul_specialCut_eval_eq_cutCharacterCoupon_eval_inContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId : String)
    (boundary : ComponentBoundary)
    (exponent : ℤ)
    {wholeSource wholeTarget : ComponentBoundary}
    (context :
      RoleAwareDiagram.Context boundary boundary wholeSource wholeTarget) :
    boundaryCharacterPower 𝒞.toFusionCategoryData η labelOf
        boundary exponent •
      Diagram.eval C
        ((context.plug
          (RoleAwareDiagram.specialDottedCut dottedId boundary)).interpret
            𝒞 η labelOf) =
      Diagram.eval C
        ((context.plug
          (RoleAwareDiagram.comp
            (RoleAwareDiagram.specialDottedCut dottedId boundary)
            (RoleAwareDiagram.characterPower boundary exponent))).interpret
              𝒞 η labelOf) := by
  rw [context.interpret_plug, context.interpret_plug]
  let categoricalContext := context.interpret 𝒞 η labelOf
  calc
    _ = boundaryCharacterPower 𝒞.toFusionCategoryData η labelOf
          boundary exponent •
        evalContextLinearMap (R := K) categoricalContext
          (Diagram.eval C
            ((RoleAwareDiagram.specialDottedCut dottedId boundary).interpret
              𝒞 η labelOf)) := by
        rw [evalContextLinearMap_diagram]
    _ = evalContextLinearMap (R := K) categoricalContext
          (boundaryCharacterPower 𝒞.toFusionCategoryData η labelOf
              boundary exponent •
            Diagram.eval C
              ((RoleAwareDiagram.specialDottedCut dottedId boundary).interpret
                𝒞 η labelOf)) := by
        rw [LinearMap.map_smul]
    _ = evalContextLinearMap (R := K) categoricalContext
          (Diagram.eval C
            ((RoleAwareDiagram.comp
              (RoleAwareDiagram.specialDottedCut dottedId boundary)
              (RoleAwareDiagram.characterPower boundary exponent)).interpret
                𝒞 η labelOf)) := by
        rw [scalar_smul_specialCut_eval_eq_cutCharacterCoupon_eval]
    _ = _ := by
        rw [evalContextLinearMap_diagram]

/--
A visible character coupon immediately before a special dotted cut is
absorbed, also inside an arbitrary unchanged role-aware exterior.
-/
theorem characterCouponCut_eval_eq_specialCut_eval_inContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId : String)
    (boundary : ComponentBoundary)
    (exponent : ℤ)
    {wholeSource wholeTarget : ComponentBoundary}
    (context :
      RoleAwareDiagram.Context boundary boundary wholeSource wholeTarget) :
    Diagram.eval C
        ((context.plug
          (RoleAwareDiagram.comp
            (RoleAwareDiagram.characterPower boundary exponent)
            (RoleAwareDiagram.specialDottedCut dottedId boundary))).interpret
              𝒞 η labelOf) =
    Diagram.eval C
        ((context.plug
          (RoleAwareDiagram.specialDottedCut dottedId boundary)).interpret
            𝒞 η labelOf) := by
  rw [context.interpret_plug, context.interpret_plug]
  let categoricalContext := context.interpret 𝒞 η labelOf
  calc
    _ = evalContextLinearMap (R := K) categoricalContext
          (Diagram.eval C
            ((RoleAwareDiagram.comp
              (RoleAwareDiagram.characterPower boundary exponent)
              (RoleAwareDiagram.specialDottedCut dottedId boundary)).interpret
                𝒞 η labelOf)) := by
      rw [evalContextLinearMap_diagram]
    _ = evalContextLinearMap (R := K) categoricalContext
          (Diagram.eval C
            ((RoleAwareDiagram.specialDottedCut dottedId boundary).interpret
              𝒞 η labelOf)) := by
      apply congrArg (evalContextLinearMap (R := K) categoricalContext)
      simp only [RoleAwareDiagram.interpret,
        RoleAwareDiagram.interpretSpecialDottedCut, Diagram.eval]
      exact PremodularDottedCutting.automorphism_power_specialDottedCut_left
        𝒞 η _ exponent
    _ = _ := by
      rw [evalContextLinearMap_diagram]

end TwistedYetter.Kirby.RoleAwareCharacterCouponBridge
