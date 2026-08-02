import TwistedYetter.CategoryTheory.Ribbon.CanonicalSpherical

/-!
# The Drinfeld trace is invariant under duality

This file isolates the graphical trace identity used in the converse half of
EGNO, Proposition 8.10.12.  EGNO obtains it from Theorem 8.10.7 and
Corollary 7.21.8.  In the braided rigid setting needed here, the same identity
is the equality of the two closures of the Drinfeld isomorphism, and can be
proved directly from rigidity and braiding coherence.
-/

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RigidCategory C]

local instance drinfeldTraceRightRigidCategory : RightRigidCategory C :=
  RigidCategory.toRightRigidCategory

/-- The left categorical trace of the Drinfeld isomorphism, written as a loop. -/
def drinfeldLoop (X : C) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ) ≫
    (β_ X (Xᘁ)).hom ≫
    ε_ X (Xᘁ)

/-- Close the Drinfeld strand after inserting a natural automorphism. -/
def naturalTwistedDrinfeldLoop (twist : 𝟭 C ≅ 𝟭 C) (X : C) :
    𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ) ≫
    (twist.hom.app X ⊗ₘ 𝟙 (Xᘁ)) ≫
    (β_ X (Xᘁ)).hom ≫
    ε_ X (Xᘁ)

/-- Closing the Drinfeld isomorphism gives the Drinfeld loop. -/
theorem leftCategoricalTrace_drinfeldHom (X : C) :
    leftCategoricalTrace (drinfeldHom X) = drinfeldLoop X := by
  simp only [leftCategoricalTrace, drinfeldLoop]
  rw [drinfeldHom_tensor_evaluation]

/-- A dual-compatible natural automorphism has a dual-invariant Drinfeld loop. -/
theorem naturalTwistedDrinfeldLoop_dual
    (twist : 𝟭 C ≅ 𝟭 C)
    (duality : ∀ X : C,
      (twist.hom.app X)ᘁ = twist.hom.app (Xᘁ))
    (X : C) :
    naturalTwistedDrinfeldLoop twist X =
      naturalTwistedDrinfeldLoop twist (Xᘁ) := by
  symm
  simp only [naturalTwistedDrinfeldLoop]
  let θX : X ⟶ X := twist.hom.app X
  let θXd : (Xᘁ) ⟶ (Xᘁ) := twist.hom.app (Xᘁ)
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
  have hDual : θXdᘁ = twist.hom.app ((Xᘁ)ᘁ) := by
    simpa only [θXd] using duality (Xᘁ)
  rw [hDual]
  have hNatural :
      drinfeldHom X ≫ twist.hom.app ((Xᘁ)ᘁ) =
        θX ≫ drinfeldHom X := by
    simpa only [θX, Functor.id_map] using
      twist.hom.naturality (drinfeldHom X)
  slice_lhs 2 2 =>
    exact congrArg (fun f => f ⊗ₘ 𝟙 (Xᘁ)) hNatural
  change
    η_ X (Xᘁ) ≫
      ((θX ≫ drinfeldHom X) ⊗ₘ 𝟙 (Xᘁ)) ≫
        ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      η_ X (Xᘁ) ≫
        (θX ⊗ₘ 𝟙 (Xᘁ)) ≫
        (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ)
  have hExpand :
      ((θX ≫ drinfeldHom X) ⊗ₘ 𝟙 (Xᘁ)) =
        (θX ⊗ₘ 𝟙 (Xᘁ)) ≫
          (drinfeldHom X ⊗ₘ 𝟙 (Xᘁ)) := by
    simpa only [Category.id_comp] using
      (MonoidalCategory.tensorHom_comp_tensorHom
        θX (𝟙 (Xᘁ)) (drinfeldHom X) (𝟙 (Xᘁ))).symm
  slice_lhs 2 2 => exact hExpand
  simp only [Category.assoc]
  rw [drinfeldHom_tensor_evaluation]

/--
The Drinfeld loop is unchanged by replacing an object by its chosen right
dual.  This is the graphical form of the Radford trace identity used in EGNO,
Proposition 8.10.12.
-/
theorem drinfeldLoop_dual (X : C) :
    drinfeldLoop X = drinfeldLoop (Xᘁ) := by
  let identityTwist : 𝟭 C ≅ 𝟭 C := Iso.refl (𝟭 C)
  have identityDuality : ∀ Y : C,
      (identityTwist.hom.app Y)ᘁ =
        identityTwist.hom.app (Yᘁ) := by
    intro Y
    dsimp [identityTwist]
    exact rightAdjointMate_id
  simpa [drinfeldLoop, naturalTwistedDrinfeldLoop, identityTwist] using
    naturalTwistedDrinfeldLoop_dual identityTwist identityDuality X

/-- The left trace of the Drinfeld isomorphism is dual-invariant. -/
theorem leftCategoricalTrace_drinfeldHom_dual (X : C) :
    leftCategoricalTrace (drinfeldHom X) =
      leftCategoricalTrace (drinfeldHom (Xᘁ)) := by
  rw [leftCategoricalTrace_drinfeldHom,
    leftCategoricalTrace_drinfeldHom, drinfeldLoop_dual]

end CategoryTheory
