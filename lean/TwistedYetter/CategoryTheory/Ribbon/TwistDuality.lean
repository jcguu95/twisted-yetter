import TwistedYetter.CategoryTheory.Ribbon.Basic
import TwistedYetter.CategoryTheory.Rigid.TensorExactPairing

/-!
# Moving a ribbon twist through cups and caps

These are the algebraic forms of the two elementary ribbon isotopies which
move a twist across a chosen right-duality cup or cap.  They follow directly
from the ribbon duality law and Mathlib's right-adjoint mate identities.
-/

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/-- A ribbon twist can be moved from a strand to its right dual across a cup. -/
theorem coevaluation_comp_dualTwist
    (ribbon : RibbonStructure C) (X : C) :
    η_ X (Xᘁ) ≫ X ◁ ribbon.twist.hom.app (Xᘁ) =
      η_ X (Xᘁ) ≫ ribbon.twist.hom.app X ▷ (Xᘁ) := by
  rw [← ribbon.duality X]
  exact coevaluation_comp_rightAdjointMate (ribbon.twist.hom.app X)

/-- A ribbon twist can be moved from a dual strand to its primal strand across a cap. -/
@[reassoc]
theorem dualTwist_comp_evaluation
    (ribbon : RibbonStructure C) (X : C) :
    (ribbon.twist.hom.app (Xᘁ) ▷ X) ≫ ε_ X (Xᘁ) =
      ((Xᘁ) ◁ ribbon.twist.hom.app X) ≫ ε_ X (Xᘁ) := by
  rw [← ribbon.duality X]
  exact rightAdjointMate_comp_evaluation (ribbon.twist.hom.app X)

/-- Ribbon duality for the componentwise cap of a tensor product. -/
@[reassoc]
theorem tensorDualTwists_comp_tensorExactPairing_evaluation
    (ribbon : RibbonStructure C) (X Y : C) :
    ((ribbon.twist.hom.app (Yᘁ) ⊗ₘ ribbon.twist.hom.app (Xᘁ)) ▷
          (X ⊗ Y)) ≫
        @ExactPairing.evaluation C _ _ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)
          tensorExactPairing =
      ((Yᘁ ⊗ Xᘁ) ◁
          (ribbon.twist.hom.app X ⊗ₘ ribbon.twist.hom.app Y)) ≫
        @ExactPairing.evaluation C _ _ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)
          tensorExactPairing := by
  let tX : X ⟶ X := ribbon.twist.hom.app X
  let tY : Y ⟶ Y := ribbon.twist.hom.app Y
  let tXd : Xᘁ ⟶ Xᘁ := ribbon.twist.hom.app (Xᘁ)
  let tYd : Yᘁ ⟶ Yᘁ := ribbon.twist.hom.app (Yᘁ)
  have hX : (tXd ▷ X) ≫ ε_ X (Xᘁ) =
      ((Xᘁ) ◁ tX) ≫ ε_ X (Xᘁ) := by
    simpa [tX, tXd] using dualTwist_comp_evaluation ribbon X
  have hY : (tYd ▷ Y) ≫ ε_ Y (Yᘁ) =
      ((Yᘁ) ◁ tY) ≫ ε_ Y (Yᘁ) := by
    simpa [tY, tYd] using dualTwist_comp_evaluation ribbon Y
  rw [tensorExactPairing_evaluation]
  simp only [whiskerRight_tensor, Category.assoc]
  simp only [← tensorHom_id]
  simp only [Functor.id_obj]
  have hAssoc := associator_inv_naturality
    (ribbon.twist.hom.app (Yᘁ) ⊗ₘ ribbon.twist.hom.app (Xᘁ))
    (𝟙 X) (𝟙 Y)
  simp only [Functor.id_obj] at hAssoc
  slice_lhs 1 2 => rw [← hAssoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    MonoidalCategory.id_tensorHom_id]
  let kDual : Xᘁ ⊗ (X ⊗ Y) ⟶ Y :=
    (α_ Xᘁ X Y).inv ≫
      (((tXd ▷ X) ≫ ε_ X (Xᘁ)) ▷ Y) ≫
        (λ_ Y).hom
  let kPrimal : Xᘁ ⊗ (X ⊗ Y) ⟶ Y :=
    (α_ Xᘁ X Y).inv ≫
      ((((Xᘁ) ◁ tX) ≫ ε_ X (Xᘁ)) ▷ Y) ≫
        (λ_ Y).hom
  have k_eq : kDual = kPrimal := by
    dsimp [kDual, kPrimal]
    rw [hX]
  have kPrimal_comp_tY : kPrimal ≫ tY =
      (α_ Xᘁ X Y).inv ≫
        (((Xᘁ) ◁ tX) ⊗ₘ tY) ≫
        (ε_ X (Xᘁ) ▷ Y) ≫
        (λ_ Y).hom := by
    dsimp [kPrimal]
    simp only [Category.assoc]
    rw [← MonoidalCategory.leftUnitor_naturality tY]
    rw [MonoidalCategory.comp_whiskerRight]
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [← whisker_exchange (ε_ X (Xᘁ)) tY]
    slice_lhs 2 3 => rw [← tensorHom_def]
    monoidal
  calc
    _ = (α_ Yᘁ Xᘁ (X ⊗ Y)).hom ≫
          (tYd ▷ (Xᘁ ⊗ (X ⊗ Y))) ≫
          (Yᘁ ◁ kDual) ≫ ε_ Y (Yᘁ) := by
        dsimp [kDual]
        simp only [tensorHom_def]
        monoidal
    _ = (α_ Yᘁ Xᘁ (X ⊗ Y)).hom ≫
          (tYd ▷ (Xᘁ ⊗ (X ⊗ Y))) ≫
          (Yᘁ ◁ kPrimal) ≫ ε_ Y (Yᘁ) := by rw [k_eq]
    _ = (α_ Yᘁ Xᘁ (X ⊗ Y)).hom ≫
          (Yᘁ ◁ kPrimal) ≫
          (tYd ▷ Y) ≫ ε_ Y (Yᘁ) := by
        slice_lhs 2 3 => rw [← whisker_exchange tYd kPrimal]
        simp only [Category.assoc]
    _ = (α_ Yᘁ Xᘁ (X ⊗ Y)).hom ≫
          (Yᘁ ◁ kPrimal) ≫
          ((Yᘁ) ◁ tY) ≫ ε_ Y (Yᘁ) := by rw [hY]
    _ = _ := by
      slice_lhs 1 3 => rw [← MonoidalCategory.whiskerLeft_comp]
      rw [kPrimal_comp_tY]
      monoidal

end CategoryTheory
