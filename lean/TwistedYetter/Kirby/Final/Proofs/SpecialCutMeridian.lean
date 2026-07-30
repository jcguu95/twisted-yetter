import TwistedYetter.Kirby.Final.Proofs.RepresentativeIndependence

namespace TwistedYetter.Kirby.Final.Proofs

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

theorem ribbonTwist_tensorUnit
    (𝒞 : PremodularFusionCategory K) :
    𝒞.ribbon.twist.hom.app (𝟙_ 𝒞.C) =
      𝟙 (𝟙_ 𝒞.C) := by
  let theta := 𝒞.ribbon.twist.hom.app (𝟙_ 𝒞.C)
  let scalar := 𝒞.closedScalar theta
  have theta_eq : theta = scalar • 𝟙 (𝟙_ 𝒞.C) :=
    (𝒞.unitEndLinearEquiv.apply_symm_apply theta).symm
  have balance :=
    𝒞.ribbon.balancing (𝟙_ 𝒞.C) (𝟙_ 𝒞.C)
  have naturality :=
    𝒞.ribbon.twist.hom.naturality (λ_ (𝟙_ 𝒞.C)).hom
  rw [balance] at naturality
  dsimp only [theta] at theta_eq
  rw [theta_eq] at naturality
  simp [MonoidalCategory.tensorHom_def, ← mul_smul] at naturality
  have coherence :
      (ρ_ (𝟙_ 𝒞.C)).hom ≫
          (λ_ (𝟙_ 𝒞.C)).inv ≫
          (ρ_ (𝟙_ 𝒞.C)).hom =
        (λ_ (𝟙_ 𝒞.C)).hom := by
    monoidal
  rw [coherence] at naturality
  letI : CategoryTheory.Simple (𝟙_ 𝒞.C) := 𝒞.unit_isSimple
  have leftUnitor_ne_zero :
      (λ_ (𝟙_ 𝒞.C)).hom ≠ 0 := by
    intro hom_zero
    have inverse_hom := (λ_ (𝟙_ 𝒞.C)).inv_hom_id
    simp [hom_zero] at inverse_hom
    exact CategoryTheory.id_nonzero (𝟙_ 𝒞.C) inverse_hom.symm
  have scalar_idempotent : scalar = scalar * scalar :=
    (smul_left_injective K leftUnitor_ne_zero).eq_iff.mp naturality
  have theta_ne_zero :
      𝒞.ribbon.twist.hom.app (𝟙_ 𝒞.C) ≠ 0 :=
    by
      intro hom_zero
      have inverse_hom :=
        𝒞.ribbon.twist.inv_hom_id_app (𝟙_ 𝒞.C)
      rw [hom_zero, CategoryTheory.Limits.comp_zero] at inverse_hom
      exact CategoryTheory.id_nonzero (𝟙_ 𝒞.C) inverse_hom.symm
  have scalar_ne_zero : scalar ≠ 0 := by
    intro scalar_zero
    apply theta_ne_zero
    rw [theta_eq, scalar_zero, zero_smul]
    rfl
  have scalar_eq_one : scalar = 1 := by
    apply (mul_left_cancel₀ scalar_ne_zero)
    rw [← scalar_idempotent]
    simp
  rw [theta_eq, scalar_eq_one, one_smul]

theorem ribbonTwist_tensorUnitSimple
    (𝒞 : PremodularFusionCategory K) :
    𝒞.ribbon.twist.hom.app
        (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) =
      𝟙 (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) := by
  apply (cancel_mono 𝒞.simples.unitIso.hom).1
  have naturality :=
    𝒞.ribbon.twist.hom.naturality 𝒞.simples.unitIso.hom
  simp only [Functor.id_map] at naturality
  rw [ribbonTwist_tensorUnit] at naturality
  simpa using naturality.symm

theorem tensorUnitProjector_comp_ribbonTwist_simple
    (𝒞 : PremodularFusionCategory K)
    (simple : 𝒞.simples.Simple) :
    tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) ≫
        𝒞.ribbon.twist.hom.app (𝒞.simples.simpleObject simple) =
      tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) := by
  classical
  rw [tensorUnitProjector_simple]
  by_cases unitCase : simple = 𝒞.simples.tensorUnit
  · subst simple
    simp [ribbonTwist_tensorUnitSimple]
  · simp [unitCase]

theorem ribbonTwist_comp_tensorUnitProjector_simple
    (𝒞 : PremodularFusionCategory K)
    (simple : 𝒞.simples.Simple) :
    𝒞.ribbon.twist.hom.app (𝒞.simples.simpleObject simple) ≫
        tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) =
      tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) := by
  have naturality :=
    𝒞.ribbon.twist.hom.naturality
      (tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple))
  simp only [Functor.id_map] at naturality
  exact Eq.trans naturality.symm
    (tensorUnitProjector_comp_ribbonTwist_simple 𝒞 simple)

theorem tensorUnitProjector_eq_zero_of_simple_not_unit
    (𝒞 : PremodularFusionCategory K)
    (X : 𝒞.C)
    [CategoryTheory.Simple X]
    (notUnit :
      (X ≅ 𝒞.simples.simpleObject 𝒞.simples.tensorUnit) → False) :
    tensorUnitProjector 𝒞 X = 0 := by
  classical
  letI : CategoryTheory.Simple
      (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) :=
    𝒞.simples.simple_isSimple 𝒞.simples.tensorUnit
  letI : FiniteDimensional K
      (X ⟶ 𝒞.simples.simpleObject 𝒞.simples.tensorUnit) :=
    𝒞.simples.hom_finite _ _
  unfold tensorUnitProjector
  apply Finset.sum_eq_zero
  intro i _
  have projectionZero :
      𝒞.simples.summandProjection X
          ⟨𝒞.simples.tensorUnit, i⟩ = 0 := by
    apply
      (finrank_zero_iff_forall_zero.mp
        (CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso
          K notUnit))
  simp [projectionZero]

theorem tensorUnitProjector_eq_identity_of_simple_unit
    (𝒞 : PremodularFusionCategory K)
    (X : 𝒞.C)
    [CategoryTheory.Simple X]
    (unitIso :
      X ≅ 𝒞.simples.simpleObject 𝒞.simples.tensorUnit) :
    tensorUnitProjector 𝒞 X = 𝟙 X := by
  classical
  unfold tensorUnitProjector
  rw [← 𝒞.simples.resolution_identity X]
  symm
  apply Finset.sum_eq_single 𝒞.simples.tensorUnit
  · intro other _ different
    letI : CategoryTheory.Simple
        (𝒞.simples.simpleObject other) :=
      𝒞.simples.simple_isSimple other
    letI : FiniteDimensional K
        (X ⟶ 𝒞.simples.simpleObject other) :=
      𝒞.simples.hom_finite _ _
    apply Finset.sum_eq_zero
    intro i _
    have noIso :
        (X ≅ 𝒞.simples.simpleObject other) → False := by
      intro otherIso
      have unitToOther :
          𝒞.simples.simpleObject 𝒞.simples.tensorUnit ≅
            𝒞.simples.simpleObject other :=
        unitIso.symm.trans otherIso
      exact different
        (𝒞.simples.simple_pairwise
          ⟨unitToOther.symm⟩)
    have projectionZero :
        𝒞.simples.summandProjection X ⟨other, i⟩ = 0 := by
      apply
        (finrank_zero_iff_forall_zero.mp
          (CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso
            K noIso))
    simp [projectionZero]
  · simp

theorem tensorUnitProjector_singleton_forward_word
    (𝒞 : PremodularFusionCategory K)
    (simple : 𝒞.simples.Simple) :
    tensorUnitProjector 𝒞
        (ribbonWordObject 𝒞
          [{ label := simple, direction := .forward }]) =
      tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) ⊗ₘ
        𝟙 (𝟙_ 𝒞.C) := by
  classical
  letI : CategoryTheory.Simple (𝒞.simples.simpleObject simple) :=
    𝒞.simples.simple_isSimple simple
  letI : CategoryTheory.Simple
      (𝒞.simples.simpleObject simple ⊗ 𝟙_ 𝒞.C) :=
    CategoryTheory.Simple.of_iso
      (ρ_ (𝒞.simples.simpleObject simple))
  simp only [ribbonWordObject, orientedSimpleObject]
  by_cases unitCase : simple = 𝒞.simples.tensorUnit
  · subst simple
    rw [tensorUnitProjector_eq_identity_of_simple_unit 𝒞
      (𝒞.simples.simpleObject 𝒞.simples.tensorUnit ⊗ 𝟙_ 𝒞.C)
      (ρ_ (𝒞.simples.simpleObject 𝒞.simples.tensorUnit))]
    rw [tensorUnitProjector_simple]
    simp
  · have simpleNotUnit :
        (𝒞.simples.simpleObject simple ≅
          𝒞.simples.simpleObject 𝒞.simples.tensorUnit) → False := by
      intro iso
      exact unitCase (𝒞.simples.simple_pairwise ⟨iso⟩)
    have tensorNotUnit :
        (𝒞.simples.simpleObject simple ⊗ 𝟙_ 𝒞.C ≅
          𝒞.simples.simpleObject 𝒞.simples.tensorUnit) → False := by
      intro iso
      exact simpleNotUnit
        ((ρ_ (𝒞.simples.simpleObject simple)).symm ≪≫ iso)
    rw [tensorUnitProjector_eq_zero_of_simple_not_unit 𝒞
      (𝒞.simples.simpleObject simple ⊗ 𝟙_ 𝒞.C) tensorNotUnit]
    rw [tensorUnitProjector_simple]
    simp [unitCase]

def specialCutMeridianMorphismWithoutExplicitTwist
    (𝒞 : PremodularFusionCategory K)
    (simple : 𝒞.simples.Simple) :
    𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C :=
  let X := 𝒞.simples.simpleObject simple
  η_ X (Xᘁ) ≫
    (tensorUnitProjector 𝒞 X ⊗ₘ 𝟙 (Xᘁ)) ≫
    (β_ X (Xᘁ)).hom ≫
    ε_ X (Xᘁ)

theorem specialCutMeridianMorphismWithoutExplicitTwist_eq
    (𝒞 : PremodularFusionCategory K)
    (simple : 𝒞.simples.Simple) :
    specialCutMeridianMorphismWithoutExplicitTwist 𝒞 simple =
      ribbonTraceMorphism 𝒞 simple
        (tensorUnitProjector 𝒞
          (𝒞.simples.simpleObject simple)) := by
  unfold specialCutMeridianMorphismWithoutExplicitTwist
  unfold ribbonTraceMorphism
  dsimp only
  have absorbTensor :
      (tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) ⊗ₘ
          𝟙 ((𝒞.simples.simpleObject simple)ᘁ)) ≫
          (𝒞.ribbon.twist.hom.app
              (𝒞.simples.simpleObject simple) ⊗ₘ
            𝟙 ((𝒞.simples.simpleObject simple)ᘁ)) =
        tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) ⊗ₘ
          𝟙 ((𝒞.simples.simpleObject simple)ᘁ) := by
    rw [tensorHom_comp_tensorHom,
      tensorUnitProjector_comp_ribbonTwist_simple,
      Category.comp_id]
    rfl
  slice_rhs 2 3 =>
    rw [absorbTensor]
  simp only [Category.assoc]
  rfl

end

end TwistedYetter.Kirby.Final.Proofs
