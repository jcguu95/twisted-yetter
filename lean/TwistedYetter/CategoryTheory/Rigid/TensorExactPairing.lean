import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Tensor products of exact pairings

The right dual of `X ⊗ Y` is represented componentwise by `Y' ⊗ X'` when
`X'` and `Y'` are right duals of `X` and `Y`.  This proof follows the
`ExactPairing.tensor` construction on current Mathlib master.
-/

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The componentwise exact pairing of `X₁ ⊗ X₂` with `Y₂ ⊗ Y₁`. -/
@[implicit_reducible]
def tensorExactPairing
    {X₁ X₂ Y₁ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    ExactPairing (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) where
  coevaluation' := η_ X₁ Y₁ ⊗≫ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ ⊗≫ 𝟙 _
  evaluation' := 𝟙 _ ⊗≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) ⊗≫ ε_ X₂ Y₂
  coevaluation_evaluation' := by
    calc
      _ = (Y₂ ⊗ Y₁) ◁ η_ X₁ Y₁ ⊗≫
          (Y₂ ⊗ Y₁) ◁ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ ⊗≫
          (Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂)) ▷ (Y₂ ⊗ Y₁) ⊗≫
          ε_ X₂ Y₂ ▷ (Y₂ ⊗ Y₁) := by monoidal
      _ = (Y₂ ⊗ Y₁) ◁ η_ X₁ Y₁ ⊗≫
          Y₂ ◁ ((Y₁ ⊗ X₁) ◁ η_ X₂ Y₂ ≫
            ε_ X₁ Y₁ ▷ (X₂ ⊗ Y₂)) ▷ Y₁ ⊗≫
          ε_ X₂ Y₂ ▷ (Y₂ ⊗ Y₁) := by monoidal
      _ = (Y₂ ⊗ Y₁) ◁ η_ X₁ Y₁ ⊗≫
          Y₂ ◁ (ε_ X₁ Y₁ ▷ (𝟙_ C) ≫
            (𝟙_ C) ◁ η_ X₂ Y₂) ▷ Y₁ ⊗≫
          ε_ X₂ Y₂ ▷ (Y₂ ⊗ Y₁) := by
        rw [whisker_exchange]
      _ = 𝟙 _ ⊗≫
          Y₂ ◁ (Y₁ ◁ η_ X₁ Y₁ ⊗≫ ε_ X₁ Y₁ ▷ Y₁) ⊗≫
          (Y₂ ◁ η_ X₂ Y₂ ⊗≫ ε_ X₂ Y₂ ▷ Y₂) ▷ Y₁ ⊗≫
          𝟙 _ := by monoidal
      _ = _ := by
        rw [ExactPairing.coevaluation_evaluation'',
          ExactPairing.coevaluation_evaluation'']
        monoidal
  evaluation_coevaluation' := by
    calc
      _ = η_ X₁ Y₁ ▷ (X₁ ⊗ X₂) ⊗≫
          (X₁ ◁ η_ X₂ Y₂) ▷ (Y₁ ⊗ X₁ ⊗ X₂) ⊗≫
          (X₁ ⊗ X₂) ◁ (Y₂ ◁ ε_ X₁ Y₁ ▷ X₂) ⊗≫
          (X₁ ⊗ X₂) ◁ ε_ X₂ Y₂ := by monoidal
      _ = η_ X₁ Y₁ ▷ (X₁ ⊗ X₂) ⊗≫
          X₁ ◁ (η_ X₂ Y₂ ▷ (Y₁ ⊗ X₁) ≫
            (X₂ ⊗ Y₂) ◁ ε_ X₁ Y₁) ▷ X₂ ⊗≫
          (X₁ ⊗ X₂) ◁ ε_ X₂ Y₂ := by monoidal
      _ = η_ X₁ Y₁ ▷ (X₁ ⊗ X₂) ⊗≫
          X₁ ◁ ((𝟙_ C) ◁ ε_ X₁ Y₁ ≫
            η_ X₂ Y₂ ▷ (𝟙_ C)) ▷ X₂ ⊗≫
          (X₁ ⊗ X₂) ◁ ε_ X₂ Y₂ := by
        rw [← whisker_exchange]
      _ = 𝟙 _ ⊗≫
          (η_ X₁ Y₁ ▷ X₁ ⊗≫ X₁ ◁ ε_ X₁ Y₁) ▷ X₂ ⊗≫
          X₁ ◁ (η_ X₂ Y₂ ▷ X₂ ⊗≫ X₂ ◁ ε_ X₂ Y₂) ⊗≫
          𝟙 _ := by monoidal
      _ = _ := by
        rw [ExactPairing.evaluation_coevaluation'',
          ExactPairing.evaluation_coevaluation'']
        monoidal

/-- The componentwise coevaluation formula for a tensor product. -/
theorem tensorExactPairing_coevaluation
    {X₁ X₂ Y₁ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    @ExactPairing.coevaluation C _ _ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁)
        tensorExactPairing =
      η_ X₁ Y₁ ⊗≫ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ ⊗≫ 𝟙 _ :=
  rfl

/-- The componentwise evaluation formula for a tensor product. -/
theorem tensorExactPairing_evaluation
    {X₁ X₂ Y₁ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    @ExactPairing.evaluation C _ _ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁)
        tensorExactPairing =
      𝟙 _ ⊗≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) ⊗≫ ε_ X₂ Y₂ :=
  rfl

/-- The canonical isomorphism between right duals carries one coevaluation to the other. -/
theorem coevaluation_comp_rightDualIso_hom
    {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    @ExactPairing.coevaluation C _ _ X Y₁ p₁ ≫
        X ◁ (rightDualIso p₁ p₂).hom =
      @ExactPairing.coevaluation C _ _ X Y₂ p₂ := by
  simpa only [rightDualIso, MonoidalCategory.whiskerLeft_id,
    MonoidalCategory.id_whiskerRight, Category.comp_id] using
    (@coevaluation_comp_rightAdjointMate C _ _ X X
      ({ rightDual := Y₂, exact := p₂ } : HasRightDual X)
      ({ rightDual := Y₁, exact := p₁ } : HasRightDual X) (𝟙 X))

/-- The inverse canonical isomorphism between right duals carries evaluation back. -/
theorem rightDualIso_inv_comp_evaluation
    {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    (rightDualIso p₁ p₂).inv ▷ X ≫
        @ExactPairing.evaluation C _ _ X Y₁ p₁ =
      @ExactPairing.evaluation C _ _ X Y₂ p₂ := by
  simpa only [rightDualIso, MonoidalCategory.whiskerLeft_id,
    Category.id_comp] using
    (@rightAdjointMate_comp_evaluation C _ _ X X
      ({ rightDual := Y₁, exact := p₁ } : HasRightDual X)
      ({ rightDual := Y₂, exact := p₂ } : HasRightDual X) (𝟙 X))

/-- Express the first coevaluation through the second right dual. -/
theorem coevaluation_eq_comp_rightDualIso_inv
    {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    @ExactPairing.coevaluation C _ _ X Y₁ p₁ =
      @ExactPairing.coevaluation C _ _ X Y₂ p₂ ≫
        X ◁ (rightDualIso p₁ p₂).inv := by
  calc
    _ = @ExactPairing.coevaluation C _ _ X Y₁ p₁ ≫
        X ◁ ((rightDualIso p₁ p₂).hom ≫
          (rightDualIso p₁ p₂).inv) := by simp
    _ = (@ExactPairing.coevaluation C _ _ X Y₁ p₁ ≫
          X ◁ (rightDualIso p₁ p₂).hom) ≫
        X ◁ (rightDualIso p₁ p₂).inv := by
      rw [MonoidalCategory.whiskerLeft_comp]
      simp only [Category.assoc]
    _ = _ := by rw [coevaluation_comp_rightDualIso_hom]

section Braided

variable [BraidedCategory C]

/-- Closing an endomorphism is independent of the chosen exact right dual. -/
theorem rightDualClosure_eq
    {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂)
    (f : X ⟶ X) :
    @ExactPairing.coevaluation C _ _ X Y₁ p₁ ≫
        (f ⊗ₘ 𝟙 Y₁) ≫ (β_ X Y₁).hom ≫
        @ExactPairing.evaluation C _ _ X Y₁ p₁ =
      @ExactPairing.coevaluation C _ _ X Y₂ p₂ ≫
        (f ⊗ₘ 𝟙 Y₂) ≫ (β_ X Y₂).hom ≫
        @ExactPairing.evaluation C _ _ X Y₂ p₂ := by
  rw [coevaluation_eq_comp_rightDualIso_inv p₁ p₂]
  calc
    _ = @ExactPairing.coevaluation C _ _ X Y₂ p₂ ≫
        (f ⊗ₘ 𝟙 Y₂) ≫ (β_ X Y₂).hom ≫
        ((rightDualIso p₁ p₂).inv ▷ X ≫
          @ExactPairing.evaluation C _ _ X Y₁ p₁) := by
      simp only [← MonoidalCategory.id_tensorHom,
        ← MonoidalCategory.tensorHom_id, Category.assoc]
      slice_lhs 2 3 => rw [MonoidalCategory.tensorHom_comp_tensorHom]
      slice_lhs 2 3 => rw [BraidedCategory.braiding_naturality]
      slice_rhs 2 3 => rw [BraidedCategory.braiding_naturality]
      slice_rhs 3 4 => rw [MonoidalCategory.tensorHom_comp_tensorHom]
      simp only [Category.id_comp, Category.comp_id, Category.assoc]
    _ = _ := by
      rw [rightDualIso_inv_comp_evaluation p₁ p₂]

end Braided

end CategoryTheory
