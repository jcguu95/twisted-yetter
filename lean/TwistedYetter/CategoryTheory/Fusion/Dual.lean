import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Opposite
import TwistedYetter.CategoryTheory.FiniteSemisimple.Simple
import TwistedYetter.CategoryTheory.Fusion.Basic
import TwistedYetter.CategoryTheory.Fusion.Schur
import TwistedYetter.CategoryTheory.Pivotal.Basic

/-!
# Additivity of selected duality

In a preadditive monoidal category whose tensor product is additive in each
variable, taking a selected right mate is additive on morphisms.
-/

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [Preadditive C] [MonoidalPreadditive C]

/-- Taking the selected right mate preserves zero. -/
@[simp]
theorem rightAdjointMate_zero {X Y : C} :
    rightAdjointMate (0 : X ⟶ Y) = 0 := by
  simp [rightAdjointMate]

/-- Taking the selected right mate preserves addition. -/
theorem rightAdjointMate_add {X Y : C} (f g : X ⟶ Y) :
    rightAdjointMate (f + g) = rightAdjointMate f + rightAdjointMate g := by
  simp [rightAdjointMate]

/-- Taking the selected right mate preserves finite sums. -/
theorem rightAdjointMate_sum {X Y : C} {I : Type*} [Fintype I]
    (f : I → (X ⟶ Y)) :
    rightAdjointMate (∑ i, f i) = ∑ i, rightAdjointMate (f i) := by
  classical
  let mateAddHom : (X ⟶ Y) →+ ((Yᘁ) ⟶ (Xᘁ)) :=
    { toFun := rightAdjointMate
      map_zero' := by simp [rightAdjointMate]
      map_add' := rightAdjointMate_add }
  exact map_sum mateAddHom f Finset.univ

section Linear

universe uK

variable (K : Type uK) [Field K] [Linear K C] [MonoidalLinear K C]

/-- Taking the selected right mate preserves scalar multiplication. -/
theorem rightAdjointMate_smul {X Y : C} (scalar : K) (f : X ⟶ Y) :
    rightAdjointMate (scalar • f) = scalar • rightAdjointMate f := by
  simp [rightAdjointMate]

/-- Selected right mate as a linear map on one Hom space. -/
def rightAdjointMateLinearMap (X Y : C) :
    (X ⟶ Y) →ₗ[K] ((Yᘁ) ⟶ (Xᘁ)) where
  toFun := rightAdjointMate
  map_add' := rightAdjointMate_add
  map_smul' := rightAdjointMate_smul K

end Linear

section Pivotal

universe uK uI

variable
  (K : Type uK) [Field K] [IsAlgClosed K]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear K C]
  [MonoidalCategory C] [RigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear K C]
  [FusionCategory.{v, uK, u, uI} K C]
  [(rightDoubleDualFunctor C).Monoidal]

/-- A pivotal structure makes selected right mate faithful on every Hom space. -/
theorem rightAdjointMate_injective_of_pivotal
    (pivotal : PivotalStructure C) {X Y : C} :
    Function.Injective
      (rightAdjointMateLinearMap (C := C) K X Y) := by
  intro f g mate_eq
  change fᘁ = gᘁ at mate_eq
  have double_mate_eq := congrArg rightAdjointMate mate_eq
  rw [rightAdjointMate_rightAdjointMate pivotal f,
    rightAdjointMate_rightAdjointMate pivotal g] at double_mate_eq
  have cancel_right :
      pivotal.iso.inv.app X ≫ f = pivotal.iso.inv.app X ≫ g :=
    (cancel_mono (pivotal.iso.hom.app Y)).1
      (by simpa only [← Category.assoc] using double_mate_eq)
  exact (cancel_epi (pivotal.iso.inv.app X)).1 cancel_right

include K

/-- In a pivotal fusion category, the selected right dual of a simple is simple. -/
theorem simple_rightDual_of_pivotal
    (pivotal : PivotalStructure C) (X : C) [Simple X] :
    Simple (Xᘁ) := by
  let doubleDualIso : ((Xᘁ)ᘁ) ≅ X := by
    simpa using (pivotal.iso.app X).symm
  letI : Simple ((Xᘁ)ᘁ) := Simple.of_iso doubleDualIso
  letI : FiniteDimensional K ((Xᘁ) ⟶ (Xᘁ)) :=
    FiniteSemisimpleCategory.hom_finite (Xᘁ) (Xᘁ)
  letI : FiniteDimensional K (((Xᘁ)ᘁ) ⟶ ((Xᘁ)ᘁ)) :=
    FiniteSemisimpleCategory.hom_finite ((Xᘁ)ᘁ) ((Xᘁ)ᘁ)
  have finrank_le :
      Module.finrank K ((Xᘁ) ⟶ (Xᘁ)) ≤
        Module.finrank K (((Xᘁ)ᘁ) ⟶ ((Xᘁ)ᘁ)) :=
    (rightAdjointMateLinearMap (C := C) K (Xᘁ) (Xᘁ)).finrank_le_finrank_of_injective
      (rightAdjointMate_injective_of_pivotal K pivotal)
  have target_finrank :
      Module.finrank K (((Xᘁ)ᘁ) ⟶ ((Xᘁ)ᘁ)) = 1 :=
    finrank_endomorphism_simple_eq_one K ((Xᘁ)ᘁ)
  have source_nonzero : (𝟙 (Xᘁ) : (Xᘁ) ⟶ (Xᘁ)) ≠ 0 := by
    intro identity_zero
    have mapped_zero := congrArg
      (rightAdjointMateLinearMap (C := C) K (Xᘁ) (Xᘁ)) identity_zero
    change rightAdjointMate (𝟙 (Xᘁ)) = rightAdjointMate 0 at mapped_zero
    exact id_nonzero ((Xᘁ)ᘁ) (by simpa using mapped_zero)
  have source_finrank_ne_zero :
      Module.finrank K ((Xᘁ) ⟶ (Xᘁ)) ≠ 0 := by
    intro rank_zero
    have all_zero := finrank_zero_iff_forall_zero.mp rank_zero
    exact source_nonzero (all_zero (𝟙 (Xᘁ)))
  have source_finrank : Module.finrank K ((Xᘁ) ⟶ (Xᘁ)) = 1 := by
    rw [target_finrank] at finrank_le
    omega
  exact simple_of_finrank_end_eq_one K (Xᘁ) source_finrank

end Pivotal

end CategoryTheory
