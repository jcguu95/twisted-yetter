import TwistedYetter.CategoryTheory.Fusion.PivotalTrace
import TwistedYetter.Fusion.FrobeniusLinear

/-!
# Nonvanishing of pivotal dimensions on simple objects

This file proves EGNO, Proposition 4.8.4, in the finite semisimple interface.
The proof first shows that composition through a simple object is separating.
Rigidity then identifies `Hom(X, X)` with the cup space
`Hom(1, X tensor X*)`.  Schur's lemma makes that cup space one-dimensional,
so a nonzero pivotal cap cannot annihilate the canonical cup.
-/

namespace CategoryTheory

open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.FrobeniusLinear

universe v uK uC uI

variable
  (K : Type uK) [Field K] [IsAlgClosed K]
  {C : Type uC} [Category.{v} C] [Abelian C] [Linear K C]
  [MonoidalCategory C] [RigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear K C]
  [FusionCategory.{v, uK, uC, uI} K C]
  [(rightDoubleDualFunctor C).Monoidal]

include K

/--
Composition through a simple object separates morphisms into that object.
This is the semisimple composition-pairing argument of
Bärenz--Barrett, Lemma 2.9.
-/
theorem simpleComposition_right_separating
    (Z A : C) [Simple Z]
    (g : A ⟶ Z)
    (vanishes : ∀ f : Z ⟶ A, f ≫ g = 0) :
    g = 0 := by
  let decomposition := Classical.choice
    (FiniteSemisimpleCategory.finite_simple_decomposition (K := K) A)
  have summand_zero :
      ∀ i : decomposition.SummandIndex,
        decomposition.inclusion i ≫ g = 0 := by
    intro i
    letI : Simple (decomposition.summandObject i) :=
      decomposition.summand_isSimple i
    by_contra nonzero
    letI : IsIso (decomposition.inclusion i ≫ g) :=
      (isIso_iff_nonzero (decomposition.inclusion i ≫ g)).mpr nonzero
    have contradiction := vanishes
      (inv (decomposition.inclusion i ≫ g) ≫ decomposition.inclusion i)
    have identity_zero : 𝟙 Z = 0 := by
      rw [Category.assoc, IsIso.inv_hom_id] at contradiction
      exact contradiction
    exact id_nonzero Z identity_zero
  calc
    g = 𝟙 A ≫ g := by simp
    _ =
        (∑ i : decomposition.SummandIndex,
          decomposition.projection i ≫ decomposition.inclusion i) ≫ g := by
          rw [decomposition.resolution_identity]
    _ =
        ∑ i : decomposition.SummandIndex,
          decomposition.projection i ≫ decomposition.inclusion i ≫ g := by
          rw [Preadditive.sum_comp]
          simp only [Category.assoc]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          simp [summand_zero i]

/-- Bend an endomorphism into the selected right-dual cup. -/
noncomputable def rightDualCupLinearEquiv (X Y : C) :
    (X ⟶ Y) ≃ₗ[K] (𝟙_ C ⟶ Y ⊗ (Xᘁ)) :=
  (CategoryTheory.Linear.homCongr K
      (λ_ X).symm (Iso.refl Y)).trans
    (tensorRightHomLinearEquiv
      (R := K) (𝟙_ C) X (Xᘁ) Y)

/-- The cup equivalence is coevaluation followed by its coupon. -/
theorem rightDualCupLinearEquiv_apply (X Y : C) (f : X ⟶ Y) :
    rightDualCupLinearEquiv K X Y f =
      η_ X (Xᘁ) ≫ (f ⊗ₘ 𝟙 (Xᘁ)) := by
  dsimp [rightDualCupLinearEquiv,
    TwistedYetter.Fusion.FrobeniusLinear.tensorRightHomLinearEquiv,
    tensorRightHomEquiv, CategoryTheory.Linear.homCongr]
  monoidal

/-- Bend an endomorphism into the pivotal cap. -/
noncomputable def pivotalCapLinearEquiv
    (pivotal : PivotalStructure C) (X Y : C) :
    (Y ⟶ X) ≃ₗ[K] (Y ⊗ (Xᘁ) ⟶ 𝟙_ C) :=
  (CategoryTheory.Linear.homCongr K
      (Iso.refl Y)
      ((pivotal.iso.app X) ≪≫ (λ_ ((Xᘁ)ᘁ)).symm)).trans
    (tensorRightHomLinearEquiv
      (R := K) Y (Xᘁ) ((Xᘁ)ᘁ) (𝟙_ C)).symm

/-- The pivotal cap is evaluation preceded by the pivotal coupon. -/
theorem pivotalCapLinearEquiv_apply
    (pivotal : PivotalStructure C) (X Y : C) (g : Y ⟶ X) :
    pivotalCapLinearEquiv K pivotal X Y g =
      ((g ≫ pivotal.iso.hom.app X) ⊗ₘ 𝟙 (Xᘁ)) ≫
        ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
  unfold pivotalCapLinearEquiv
  change
    (tensorRightHomLinearEquiv
      (R := K) Y (Xᘁ) ((Xᘁ)ᘁ) (𝟙_ C)).symm
        (CategoryTheory.Linear.homCongr K
          (Iso.refl Y)
          ((pivotal.iso.app X) ≪≫ (λ_ ((Xᘁ)ᘁ)).symm) g) = _
  rw [CategoryTheory.Linear.homCongr_apply]
  simp only [Iso.refl_inv, Category.id_comp, Iso.trans_hom]
  dsimp [
    TwistedYetter.Fusion.FrobeniusLinear.tensorRightHomLinearEquiv,
    tensorRightHomEquiv, CategoryTheory.Linear.homCongr]
  monoidal

/-- Joining the canonical cup to the pivotal cap is the pivotal dimension. -/
theorem cup_comp_pivotalCap_identity
    (pivotal : PivotalStructure C) (X : C) :
    rightDualCupLinearEquiv K X X (𝟙 X) ≫
        pivotalCapLinearEquiv K pivotal X X (𝟙 X) =
      pivotalDimension pivotal X := by
  rw [rightDualCupLinearEquiv_apply, pivotalCapLinearEquiv_apply]
  simp only [Category.id_comp]
  dsimp [pivotalDimension, leftCategoricalTrace]
  monoidal

/-- EGNO, Proposition 4.8.4: a simple object's pivotal dimension is nonzero. -/
theorem pivotalDimension_ne_zero_of_simple
    (pivotal : PivotalStructure C) (X : C) [Simple X] :
    pivotalDimension pivotal X ≠ 0 := by
  let cup := rightDualCupLinearEquiv K X X (𝟙 X)
  let cap := pivotalCapLinearEquiv K pivotal X X (𝟙 X)
  have cap_ne_zero : cap ≠ 0 := by
    intro cap_zero
    have identity_zero : (𝟙 X : X ⟶ X) = 0 := by
      apply (pivotalCapLinearEquiv K pivotal X X).injective
      simpa [cap] using cap_zero
    exact id_nonzero X identity_zero
  intro dimension_zero
  have cup_cap_zero : cup ≫ cap = 0 := by
    change
      rightDualCupLinearEquiv K X X (𝟙 X) ≫
        pivotalCapLinearEquiv K pivotal X X (𝟙 X) = 0
    rw [cup_comp_pivotalCap_identity K pivotal X]
    exact dimension_zero
  have all_cups_vanish :
      ∀ f : 𝟙_ C ⟶ X ⊗ (Xᘁ), f ≫ cap = 0 := by
    intro f
    let h : X ⟶ X := (rightDualCupLinearEquiv K X X).symm f
    letI : FiniteDimensional K (X ⟶ X) :=
      FiniteSemisimpleCategory.hom_finite X X
    obtain ⟨scalar, h_scalar⟩ := endomorphism_simple_eq_smul_id K h
    have f_scalar : f = scalar • cup := by
      calc
        f = rightDualCupLinearEquiv K X X h := by
          simp [h]
        _ = rightDualCupLinearEquiv K X X (scalar • 𝟙 X) := by
          rw [← h_scalar]
        _ = scalar • cup := by
          simp [cup]
    rw [f_scalar, CategoryTheory.Linear.smul_comp, cup_cap_zero, smul_zero]
  letI : Simple (𝟙_ C) := FusionCategory.tensorUnit_simple (K := K)
  have cap_zero := simpleComposition_right_separating K (𝟙_ C)
    (X ⊗ (Xᘁ)) cap all_cups_vanish
  exact cap_ne_zero cap_zero

/--
On a simple object of a fusion category, pivotal trace equality detects
endomorphism equality without any additional nonvanishing hypothesis.
-/
theorem simple_endomorphism_eq_of_pivotalTrace_eq_of_fusion
    (pivotal : PivotalStructure C) (X : C) [Simple X]
    {f g : X ⟶ X}
    (trace_eq : pivotalTrace pivotal f = pivotalTrace pivotal g) :
    f = g :=
  simple_endomorphism_eq_of_pivotalTrace_eq K pivotal X
    (pivotalDimension_ne_zero_of_simple K pivotal X) trace_eq

end CategoryTheory
