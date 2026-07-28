import TwistedYetter.Kirby.ModularVacuumProjector
import TwistedYetter.Fusion.EGNOPremodularModular

/-!
# Premodular special-dotted cutting

The special dotted component is not replaced by an ordinary Kirby-coloured
component.  Its local operator is the projector onto the complete tensor-unit
isotypic summand.

The proofs in this file use only fusion, ribbon, and monoidal-natural
automorphism data.  In particular, no modularity or transparent-sector
collapse is used.
-/

namespace TwistedYetter.Kirby.PremodularDottedCutting

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.ModularVacuumProjector

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
The operator represented by cutting a special dotted component.

This is Tham's index-three map from Definition 5.11: it retains every copy of
the tensor unit and no transparent non-unit summand.  It carries no additional
global-dimension scalar.
-/
noncomputable def specialDottedCutOperator
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (X : C) : X ⟶ X :=
  unitSummandProjector 𝒞.toFusionCategoryData X

/-- On a simple puncture, the special cut keeps exactly the tensor unit. -/
theorem specialDottedCutOperator_simple
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (s : S) :
    specialDottedCutOperator 𝒞 (𝒞.simple s) =
      if s = 𝒞.toFusionCategoryData.unitIndex then
        𝟙 (𝒞.simple s)
      else
        0 := by
  rw [specialDottedCutOperator,
    unitSummandProjector_simple 𝒞.toFusionCategoryData s]

/-- A character coupon is invisible immediately before a special cut. -/
theorem automorphism_power_specialDottedCut_left
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (X : C)
    (exponent : ℤ) :
    automorphismObjectPower η X exponent ≫
        specialDottedCutOperator 𝒞 X =
      specialDottedCutOperator 𝒞 X := by
  unfold specialDottedCutOperator
  exact automorphism_power_projector_left
    𝒞.toFusionCategoryData η X exponent

/-- A character coupon is invisible immediately after a special cut. -/
theorem automorphism_power_specialDottedCut_right
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (X : C)
    (exponent : ℤ) :
    specialDottedCutOperator 𝒞 X ≫
        automorphismObjectPower η X exponent =
      specialDottedCutOperator 𝒞 X := by
  unfold specialDottedCutOperator
  exact automorphism_power_projector_right
    𝒞.toFusionCategoryData η X exponent

/--
A positive crossing carries the special cut from one side of the crossing to
the other.  This is ordinary braiding naturality; modularity is irrelevant.
-/
theorem specialDottedCut_braiding_positive
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (X Y : C) :
    specialDottedCutOperator 𝒞 X ▷ Y ≫
        (β_ X Y).hom =
      (β_ X Y).hom ≫
        Y ◁ specialDottedCutOperator 𝒞 X := by
  exact BraidedCategory.braiding_naturality_left
    (specialDottedCutOperator 𝒞 X) Y

/-- The same transport law for a negative crossing. -/
theorem specialDottedCut_braiding_negative
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (X Y : C) :
    Y ◁ specialDottedCutOperator 𝒞 X ≫
        (β_ X Y).inv =
      (β_ X Y).inv ≫
        specialDottedCutOperator 𝒞 X ▷ Y := by
  exact BraidedCategory.braiding_inv_naturality_right Y
    (specialDottedCutOperator 𝒞 X)

/--
Two disjoint special cuts commute under the monoidal interchange law.

This is the order-independence needed when simultaneous dotted disks are
processed in different component-index orders.
-/
theorem disjoint_specialDottedCuts_interchange
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (X Y : C) :
    specialDottedCutOperator 𝒞 X ▷ Y ≫
        X ◁ specialDottedCutOperator 𝒞 Y =
      X ◁ specialDottedCutOperator 𝒞 Y ≫
        specialDottedCutOperator 𝒞 X ▷ Y := by
  exact (MonoidalCategory.whisker_exchange
    (specialDottedCutOperator 𝒞 X)
    (specialDottedCutOperator 𝒞 Y)).symm

/--
The modular specialization uses exactly the same unit-summand projector.

This theorem is deliberately definitional: modularity changes which ordinary
Kirby encircling calculations are available, not the special-cut operator.
-/
theorem modular_specialization
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (X : C) :
    specialDottedCutOperator 𝒞.premodular X =
      unitSummandProjector
        𝒞.premodular.toFusionCategoryData X :=
  rfl

/-- Machine-visible status of the category-side special-cut calculation. -/
def currentStatus : String :=
  "PASS_PREMODULAR_SPECIAL_DOTTED_UNIT_CUT_CHARACTER_NEUTRALITY"

end TwistedYetter.Kirby.PremodularDottedCutting
