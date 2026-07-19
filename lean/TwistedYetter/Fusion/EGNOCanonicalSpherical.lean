import TwistedYetter.Fusion.EGNOCanonicalPivotal

/-!
# The EGNO canonical spherical structure

This module proves the ribbon-to-spherical direction of EGNO Proposition
8.10.12, printed page 220. The canonical pivotal dimension is first rewritten
as the ribbon loop of EGNO equation (8.41). A direct mate-and-braiding
calculation then identifies the loop of `X` with the loop of its chosen right
dual `X*`.

The proof uses only the typed braided right-rigid structure, naturality of the
twist, and the ribbon dual law. It does not assume semisimplicity, a finite
simple-object set, or a concrete fusion category.
-/

namespace TwistedYetter.Fusion.EGNO

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

section DualComparison

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/--
The canonical comparison between two right duals preserves evaluation.
-/
theorem rightDualIso_hom_evaluation {A B D : C}
    (p₁ : ExactPairing A B) (p₂ : ExactPairing A D) :
    ((rightDualIso p₁ p₂).hom ▷ A) ≫
        @ExactPairing.evaluation C _ _ A D p₂ =
      @ExactPairing.evaluation C _ _ A B p₁ := by
  simpa only [rightDualIso, whiskerLeft_id, Category.id_comp] using
    (@rightAdjointMate_comp_evaluation C _ _ A A
      ({ rightDual := D, exact := p₂ } : HasRightDual A)
      ({ rightDual := B, exact := p₁ } : HasRightDual A)
      (𝟙 A))

/--
The canonical comparison between two right duals preserves coevaluation.
-/
theorem rightDualIso_coevaluation_hom {A B D : C}
    (p₁ : ExactPairing A B) (p₂ : ExactPairing A D) :
    @ExactPairing.coevaluation C _ _ A B p₁ ≫
        A ◁ (rightDualIso p₁ p₂).hom =
      @ExactPairing.coevaluation C _ _ A D p₂ := by
  simpa only [rightDualIso, id_whiskerRight, Category.comp_id] using
    (@coevaluation_comp_rightAdjointMate C _ _ A A
      ({ rightDual := D, exact := p₂ } : HasRightDual A)
      ({ rightDual := B, exact := p₁ } : HasRightDual A)
      (𝟙 A))

end DualComparison

section Spherical

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/--
The evaluation compatibility of the Drinfeld comparison.

The positive crossing is forced by the braided-swapped exact pairing.
-/
theorem drinfeldHom_tensor_evaluation (X : C) :
    (drinfeldHom X ⊗ₘ 𝟙 (Xᘁ)) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) := by
  simpa [drinfeldHom, drinfeldIso, tensorHom_id,
    BraidedCategory.exactPairing_swap, ExactPairing.evaluation] using
      (rightDualIso_hom_evaluation
        (BraidedCategory.exactPairing_swap X (Xᘁ))
        (inferInstance : ExactPairing (Xᘁ) ((Xᘁ)ᘁ)))

/--
The coevaluation compatibility of the Drinfeld comparison, before expanding
the braided-swapped exact pairing.
-/
theorem drinfeldHom_coevaluation_pairing (X : C) :
    @ExactPairing.coevaluation C _ _ (Xᘁ) X
        (BraidedCategory.exactPairing_swap X (Xᘁ)) ≫
        (Xᘁ) ◁ drinfeldHom X =
      η_ (Xᘁ) ((Xᘁ)ᘁ) := by
  simpa [drinfeldHom, drinfeldIso] using
    (rightDualIso_coevaluation_hom
      (BraidedCategory.exactPairing_swap X (Xᘁ))
      (inferInstance : ExactPairing (Xᘁ) ((Xᘁ)ᘁ)))

/-- The swapped coevaluation is a cup followed by the inverse crossing. -/
theorem swappedPairing_coevaluation (X : C) :
    @ExactPairing.coevaluation C _ _ (Xᘁ) X
        (BraidedCategory.exactPairing_swap X (Xᘁ)) =
      η_ X (Xᘁ) ≫ (β_ (Xᘁ) X).inv :=
  rfl

/--
The expanded coevaluation compatibility of the Drinfeld comparison.
-/
theorem drinfeldHom_coevaluation (X : C) :
    (η_ X (Xᘁ) ≫ (β_ (Xᘁ) X).inv) ≫
        (Xᘁ) ◁ drinfeldHom X =
      η_ (Xᘁ) ((Xᘁ)ᘁ) := by
  rw [← swappedPairing_coevaluation]
  exact drinfeldHom_coevaluation_pairing X

/--
The ribbon loop appearing in EGNO equation (8.41).
-/
def ribbonLoop (twist : BalancedTwist C) (X : C) :
    𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ) ≫
    (twist.iso.hom.app X ⊗ₘ 𝟙 (Xᘁ)) ≫
    (β_ X (Xᘁ)).hom ≫
    ε_ X (Xᘁ)

/--
The canonical pivotal dimension is the ribbon loop of EGNO equation (8.41).
-/
theorem canonicalPivotalDimension_eq_ribbonLoop
    (ribbon : RibbonStructure C) (X : C) :
    pivotalDimension (canonicalPivotalStructure ribbon) X =
      ribbonLoop ribbon.toBalancedTwist X := by
  simp only [pivotalDimension, leftCategoricalTrace,
    canonicalPivotalStructure, canonicalPivotalIso_hom_app,
    canonicalPivotalHom, ribbonLoop]
  simp only [Functor.id_obj]
  let θX : X ⟶ X := ribbon.toBalancedTwist.iso.hom.app X
  change
    η_ X (Xᘁ) ≫ ((θX ≫ drinfeldHom X) ⊗ₘ 𝟙 (Xᘁ)) ≫
        ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      η_ X (Xᘁ) ≫ (θX ⊗ₘ 𝟙 (Xᘁ)) ≫
        (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ)
  have hTensor :
      ((θX ≫ drinfeldHom X) ⊗ₘ 𝟙 (Xᘁ)) =
        (θX ⊗ₘ 𝟙 (Xᘁ)) ≫
          (drinfeldHom X ⊗ₘ 𝟙 (Xᘁ)) := by
    simpa only [Category.comp_id] using
      (MonoidalCategory.tensorHom_comp_tensorHom
        θX (𝟙 (Xᘁ))
        (drinfeldHom X) (𝟙 (Xᘁ))).symm
  rw [hTensor]
  simp only [Category.assoc]
  rw [drinfeldHom_tensor_evaluation]

/--
Moving the dual twist through evaluation gives the primal twist.

This is the only step that uses the ribbon dual law. The remaining rewrites
are evaluation mates and naturality of the twist.
-/
theorem drinfeldHom_tensor_twist_evaluation
    (ribbon : RibbonStructure C) (X : C) :
    (drinfeldHom X ⊗ₘ
        ribbon.toBalancedTwist.iso.hom.app (Xᘁ)) ≫
        ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      (ribbon.toBalancedTwist.iso.hom.app X ⊗ₘ 𝟙 (Xᘁ)) ≫
        (β_ X (Xᘁ)).hom ≫
        ε_ X (Xᘁ) := by
  let θX : X ⟶ X := ribbon.toBalancedTwist.iso.hom.app X
  let θXd : (Xᘁ) ⟶ (Xᘁ) :=
    ribbon.toBalancedTwist.iso.hom.app (Xᘁ)
  change
    (drinfeldHom X ⊗ₘ θXd) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      (θX ⊗ₘ 𝟙 (Xᘁ)) ≫
        (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ)
  have hSplit :
      (drinfeldHom X ⊗ₘ θXd) =
        (drinfeldHom X ⊗ₘ 𝟙 (Xᘁ)) ≫
          (𝟙 ((Xᘁ)ᘁ) ⊗ₘ θXd) := by
    simpa only [Category.comp_id, Category.id_comp] using
      (MonoidalCategory.tensorHom_comp_tensorHom
        (drinfeldHom X) (𝟙 (Xᘁ))
        (𝟙 ((Xᘁ)ᘁ)) θXd).symm
  rw [hSplit]
  simp only [Category.assoc]
  rw [id_tensorHom]
  rw [← rightAdjointMate_comp_evaluation θXd]
  rw [← tensorHom_id]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  simp only [Category.comp_id]
  have hDual :
      θXdᘁ =
        ribbon.toBalancedTwist.iso.hom.app ((Xᘁ)ᘁ) := by
    simpa only [θXd] using ribbon.dual (Xᘁ)
  rw [hDual]
  have hNatural :
      drinfeldHom X ≫
          ribbon.toBalancedTwist.iso.hom.app ((Xᘁ)ᘁ) =
        θX ≫ drinfeldHom X := by
    simpa only [θX, Functor.id_map] using
      ribbon.toBalancedTwist.iso.hom.naturality (drinfeldHom X)
  slice_lhs 1 1 =>
    exact congrArg (fun f => f ⊗ₘ 𝟙 (Xᘁ)) hNatural
  change
    ((θX ≫ drinfeldHom X) ⊗ₘ 𝟙 (Xᘁ)) ≫
        ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      (θX ⊗ₘ 𝟙 (Xᘁ)) ≫
        (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ)
  have hExpand :
      ((θX ≫ drinfeldHom X) ⊗ₘ 𝟙 (Xᘁ)) =
        (θX ⊗ₘ 𝟙 (Xᘁ)) ≫
          (drinfeldHom X ⊗ₘ 𝟙 (Xᘁ)) := by
    simpa only [Category.id_comp] using
      (MonoidalCategory.tensorHom_comp_tensorHom
        θX (𝟙 (Xᘁ)) (drinfeldHom X) (𝟙 (Xᘁ))).symm
  rw [hExpand]
  simp only [Category.assoc]
  rw [drinfeldHom_tensor_evaluation]

/--
The ribbon loop is unchanged by replacing an object with its chosen right
dual.
-/
theorem ribbonLoop_dual (ribbon : RibbonStructure C) (X : C) :
    ribbonLoop ribbon.toBalancedTwist X =
      ribbonLoop ribbon.toBalancedTwist (Xᘁ) := by
  symm
  simp only [ribbonLoop]
  let θX : X ⟶ X := ribbon.toBalancedTwist.iso.hom.app X
  let θXd : (Xᘁ) ⟶ (Xᘁ) :=
    ribbon.toBalancedTwist.iso.hom.app (Xᘁ)
  change
    η_ (Xᘁ) ((Xᘁ)ᘁ) ≫
        (θXd ⊗ₘ 𝟙 ((Xᘁ)ᘁ)) ≫
        (β_ (Xᘁ) ((Xᘁ)ᘁ)).hom ≫
        ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      η_ X (Xᘁ) ≫
        (θX ⊗ₘ 𝟙 (Xᘁ)) ≫
        (β_ X (Xᘁ)).hom ≫
        ε_ X (Xᘁ)
  rw [← drinfeldHom_coevaluation X]
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    rw [← id_tensorHom]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_naturality_assoc θXd (drinfeldHom X)]
  rw [Iso.inv_hom_id_assoc]
  dsimp only [θX, θXd]
  have hTwistEvaluation :=
    drinfeldHom_tensor_twist_evaluation ribbon X
  simp only [Functor.id_obj] at hTwistEvaluation
  slice_lhs 2 3 =>
    exact hTwistEvaluation

/--
The canonical pivotal dimension is invariant under the chosen right dual.
-/
theorem canonicalPivotal_dimension_dual
    (ribbon : RibbonStructure C) (X : C) :
    pivotalDimension (canonicalPivotalStructure ribbon) X =
      pivotalDimension (canonicalPivotalStructure ribbon) (Xᘁ) := by
  rw [canonicalPivotalDimension_eq_ribbonLoop,
    canonicalPivotalDimension_eq_ribbonLoop]
  exact ribbonLoop_dual ribbon X

/--
Every ribbon structure determines the canonical spherical structure.

This is the ribbon-to-spherical implication of EGNO Proposition 8.10.12.
-/
def canonicalSphericalStructure (ribbon : RibbonStructure C) :
    SphericalStructure (C := C) where
  toPivotalStructure := canonicalPivotalStructure ribbon
  dimension_dual := canonicalPivotal_dimension_dual ribbon

/-- The underlying pivotal structure is the canonical pivotal structure. -/
theorem canonicalSphericalStructure_toPivotal
    (ribbon : RibbonStructure C) :
    (canonicalSphericalStructure ribbon).toPivotalStructure =
      canonicalPivotalStructure ribbon :=
  rfl

end Spherical

end TwistedYetter.Fusion.EGNO
