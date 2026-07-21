import TwistedYetter.Kirby.ComponentDottedEncircling
import TwistedYetter.Kirby.TensorAutomorphismDuality

/-!
# Tensor-character calculus on an oriented puncture boundary

The dotted spanning disk sees a parenthesized word of positively and
negatively oriented two-handle strands.  This module proves, rather than
assumes, how a monoidal automorphism acts on that word:

* a positive occurrence contributes `chi^n`;
* a negative occurrence contributes `chi^(-n)`; and
* tensoring occurrences multiplies the contributions.

The negative sign is forced by naturality at evaluation and rigidity through
`TensorAutomorphismDuality.hom_app_rightDual`.  The result is the categorical
bridge from signed disk intersections to the character factors in the raw
cycle-colour sum.
-/

namespace TwistedYetter.Kirby.ComponentBoundaryCharacter

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.ModularVacuumProjector
open TwistedYetter.Kirby.TensorAutomorphismDuality

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance componentBoundaryCharacterRightRigid : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/-- Unit-valued character carried by an oriented puncture boundary. -/
noncomputable def boundaryCharacterUnit
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (labelOf : String → S) : ComponentBoundary → Kˣ
  | .unit => 1
  | .atom component =>
      match component.orientation with
      | .positive =>
          data.automorphismSimpleUnit automorphism
            (labelOf component.componentId)
      | .negative =>
          (data.automorphismSimpleUnit automorphism
            (labelOf component.componentId))⁻¹
  | .tensor left right =>
      boundaryCharacterUnit data automorphism labelOf left *
        boundaryCharacterUnit data automorphism labelOf right

/-- Scalar obtained by applying one integral coupon power to the boundary. -/
noncomputable def boundaryCharacterPower
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (boundary : ComponentBoundary)
    (exponent : ℤ) : K :=
  ↑((boundaryCharacterUnit data automorphism labelOf boundary) ^ exponent : Kˣ)

/--
The boundary character only reads labels attached to component IDs which
actually occur in the boundary word.
-/
theorem boundaryCharacterUnit_eq_of_eq_on_componentIds
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (leftLabels rightLabels : String → S)
    (boundary : ComponentBoundary)
    (agree :
      (componentId : String) →
      componentId ∈ boundary.componentIds →
        leftLabels componentId = rightLabels componentId) :
    boundaryCharacterUnit data automorphism leftLabels boundary =
      boundaryCharacterUnit data automorphism rightLabels boundary := by
  induction boundary with
  | unit =>
      rfl
  | atom component =>
      have labelEq :
          leftLabels component.componentId =
            rightLabels component.componentId :=
        agree component.componentId (by
          simp [ComponentBoundary.componentIds])
      cases component.orientation <;>
        simp only [boundaryCharacterUnit] <;>
        rw [labelEq]
  | tensor left right leftIH rightIH =>
      simp only [boundaryCharacterUnit]
      rw [leftIH (fun componentId membership =>
        agree componentId (by
          simp only [ComponentBoundary.componentIds, List.mem_append]
          exact Or.inl membership))]
      rw [rightIH (fun componentId membership =>
        agree componentId (by
          simp only [ComponentBoundary.componentIds, List.mem_append]
          exact Or.inr membership))]

/-- Every integral power has the same finite-support property. -/
theorem boundaryCharacterPower_eq_of_eq_on_componentIds
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (leftLabels rightLabels : String → S)
    (boundary : ComponentBoundary)
    (exponent : ℤ)
    (agree :
      (componentId : String) →
      componentId ∈ boundary.componentIds →
        leftLabels componentId = rightLabels componentId) :
    boundaryCharacterPower data automorphism leftLabels boundary exponent =
      boundaryCharacterPower data automorphism rightLabels boundary exponent := by
  unfold boundaryCharacterPower
  rw [boundaryCharacterUnit_eq_of_eq_on_componentIds
    data automorphism leftLabels rightLabels boundary agree]

/-- Right adjoint mates preserve scalar multiples of an identity. -/
theorem rightAdjointMate_smul_id
    (scalar : K)
    (X : C) :
    (scalar • 𝟙 X)ᘁ = scalar • 𝟙 (Xᘁ) := by
  simp [rightAdjointMate]

/-- On a negative simple strand the forward coupon is the inverse scalar. -/
theorem automorphism_hom_app_rightDual_eq_scalarPower_neg_one
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (simple : S) :
    automorphism.iso.hom.app (data.simple simple)ᘁ =
      data.automorphismScalarPower automorphism simple (-1) •
        𝟙 ((data.simple simple)ᘁ) := by
  have inversePower :
      data.automorphismCouponPower automorphism simple (-1) =
        automorphism.iso.inv.app (data.simple simple) := by
    simp only [FusionCategoryData.automorphismCouponPower,
      zpow_neg_one, Aut.Aut_inv_def]
    rfl
  have inverseMate :
      (automorphism.iso.inv.app (data.simple simple))ᘁ =
        (data.automorphismCouponPower
          automorphism simple (-1))ᘁ :=
    congrArg
      (fun morphism : data.simple simple ⟶ data.simple simple =>
        morphismᘁ)
      inversePower.symm
  have couponMate :
      (data.automorphismCouponPower automorphism simple (-1))ᘁ =
        (data.automorphismScalarPower automorphism simple (-1) •
          𝟙 (data.simple simple))ᘁ :=
    congrArg
      (fun morphism : data.simple simple ⟶ data.simple simple =>
        morphismᘁ)
      (data.automorphismCouponPower_eq_smul_identity
        automorphism simple (-1))
  exact
    (hom_app_rightDual automorphism (data.simple simple)).trans
      (inverseMate.trans
        (couponMate.trans (rightAdjointMate_smul_id _ _)))

/--
The automorphism component on a whole oriented boundary is exactly the
scalar unit obtained by multiplying its signed simple contributions.
-/
theorem automorphism_app_eq_boundaryCharacterUnit
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (boundary : ComponentBoundary) :
    automorphism.iso.app
        (boundary.interpret data labelOf).denote =
      FusionCategoryData.scalarUnitAut
        (K := K) (boundary.interpret data labelOf).denote
        (boundaryCharacterUnit data.toFusionCategoryData
          automorphism labelOf boundary) := by
  induction boundary with
  | unit =>
      apply Aut.ext
      change automorphism.iso.hom.app (𝟙_ C) =
        (((1 : Kˣ) : K) • 𝟙 (𝟙_ C))
      rw [TensorIdentityAutomorphism.unit_hom]
      simp
  | atom component =>
      cases component with
      | mk componentId orientation =>
          cases orientation with
          | positive =>
              exact
                data.toFusionCategoryData.automorphism_app_iso_eq_scalarUnitAut
                  automorphism (labelOf componentId)
          | negative =>
              apply Aut.ext
              change automorphism.iso.hom.app
                  (data.simple (labelOf componentId))ᘁ =
                (((data.toFusionCategoryData.automorphismSimpleUnit
                    automorphism (labelOf componentId))⁻¹ : K) •
                  𝟙 ((data.simple (labelOf componentId))ᘁ))
              rw [automorphism_hom_app_rightDual_eq_scalarPower_neg_one]
              simp [FusionCategoryData.automorphismScalarPower]
  | tensor left right leftIH rightIH =>
      apply Aut.ext
      change automorphism.iso.hom.app
          ((left.interpret data labelOf).denote ⊗
            (right.interpret data labelOf).denote) =
        (((boundaryCharacterUnit data.toFusionCategoryData
              automorphism labelOf left *
            boundaryCharacterUnit data.toFusionCategoryData
              automorphism labelOf right : Kˣ) : K) •
          𝟙 ((left.interpret data labelOf).denote ⊗
            (right.interpret data labelOf).denote))
      rw [TensorIdentityAutomorphism.tensor_hom]
      rw [show automorphism.iso.hom.app
          (left.interpret data labelOf).denote =
            (FusionCategoryData.scalarUnitAut
              (K := K) (left.interpret data labelOf).denote
              (boundaryCharacterUnit data.toFusionCategoryData
                automorphism labelOf left)).hom by
        exact congrArg Iso.hom leftIH]
      rw [show automorphism.iso.hom.app
          (right.interpret data labelOf).denote =
            (FusionCategoryData.scalarUnitAut
              (K := K) (right.interpret data labelOf).denote
              (boundaryCharacterUnit data.toFusionCategoryData
                automorphism labelOf right)).hom by
        exact congrArg Iso.hom rightIH]
      simp [FusionCategoryData.scalarUnitAut, boundaryCharacterUnit,
        tensorHom_def, ← mul_smul, mul_comm]

/-- Every integral coupon power on the boundary is the derived scalar power. -/
theorem automorphismObjectPower_eq_boundaryCharacterPower_smul_identity
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (boundary : ComponentBoundary)
    (exponent : ℤ) :
    automorphismObjectPower automorphism
        (boundary.interpret data labelOf).denote exponent =
      boundaryCharacterPower data.toFusionCategoryData
          automorphism labelOf boundary exponent •
        𝟙 (boundary.interpret data labelOf).denote := by
  rw [automorphismObjectPower,
    automorphism_app_eq_boundaryCharacterUnit data automorphism labelOf]
  change
    ((FusionCategoryData.scalarUnitAut
      (K := K) (boundary.interpret data labelOf).denote
      (boundaryCharacterUnit data.toFusionCategoryData
        automorphism labelOf boundary)) ^ exponent).hom = _
  rw [← map_zpow]
  rfl

@[simp]
theorem boundaryCharacterPower_unit
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (exponent : ℤ) :
    boundaryCharacterPower data automorphism labelOf .unit exponent = 1 := by
  simp [boundaryCharacterPower, boundaryCharacterUnit]

@[simp]
theorem boundaryCharacterPower_positive
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (componentId : String)
    (exponent : ℤ) :
    boundaryCharacterPower data automorphism labelOf
        (.atom (positiveAtom componentId)) exponent =
      data.automorphismScalarPower automorphism
        (labelOf componentId) exponent := by
  rfl

@[simp]
theorem boundaryCharacterPower_negative
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (componentId : String)
    (exponent : ℤ) :
    boundaryCharacterPower data automorphism labelOf
        (.atom (negativeAtom componentId)) exponent =
      data.automorphismScalarPower automorphism
        (labelOf componentId) (-exponent) := by
  simp [boundaryCharacterPower, boundaryCharacterUnit, negativeAtom,
    FusionCategoryData.automorphismScalarPower]

@[simp]
theorem boundaryCharacterPower_tensor
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (left right : ComponentBoundary)
    (exponent : ℤ) :
    boundaryCharacterPower data automorphism labelOf
        (.tensor left right) exponent =
      boundaryCharacterPower data automorphism labelOf left exponent *
        boundaryCharacterPower data automorphism labelOf right exponent := by
  simp [boundaryCharacterPower, boundaryCharacterUnit, mul_zpow]

/-- Machine-visible result: all orientation signs are derived. -/
def currentStatus : String :=
  "PASS_ORIENTED_BOUNDARY_CHARACTER_POWER_DERIVED_FROM_DUALITY"

end TwistedYetter.Kirby.ComponentBoundaryCharacter
