import TwistedYetter.Kirby.Final.Proofs.RepresentativeIndependence

namespace TwistedYetter.Kirby.Final.Proofs

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

theorem ribbonTwist_tensorUnit
    (𝒞 : BundledPremodularCategory K) :
    𝒞.twist.hom.app (𝟙_ 𝒞.C) =
      𝟙 (𝟙_ 𝒞.C) := by
  exact balancedTwist_unit 𝒞.balancing

theorem ribbonTwist_tensorUnitSimple
    (𝒞 : BundledPremodularCategory K) :
    𝒞.twist.hom.app
        (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) =
      𝟙 (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) := by
  have naturality :=
    𝒞.twist.hom.naturality 𝒞.simples.unitIso.hom
  simp only [Functor.id_map] at naturality
  rw [ribbonTwist_tensorUnit] at naturality
  have postcomposition :
      𝒞.twist.hom.app
          (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) ≫
          𝒞.simples.unitIso.hom =
        𝟙 (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) ≫
          𝒞.simples.unitIso.hom := by
    simpa using naturality.symm
  exact (cancel_mono 𝒞.simples.unitIso.hom).mp postcomposition

theorem tensorUnitProjector_comp_ribbonTwist_simple
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple) :
    tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) ≫
        𝒞.twist.hom.app (𝒞.simples.simpleObject simple) =
      tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) := by
  classical
  rw [tensorUnitProjector_simple]
  by_cases unitCase : simple = 𝒞.simples.tensorUnit
  · subst simple
    simp [ribbonTwist_tensorUnitSimple]
  · simp [unitCase]

theorem ribbonTwist_comp_tensorUnitProjector_simple
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple) :
    𝒞.twist.hom.app (𝒞.simples.simpleObject simple) ≫
        tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) =
      tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) := by
  have naturality :=
    𝒞.twist.hom.naturality
      (tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple))
  simp only [Functor.id_map] at naturality
  exact Eq.trans naturality.symm
    (tensorUnitProjector_comp_ribbonTwist_simple 𝒞 simple)

theorem tensorUnitProjector_eq_zero_of_simple_not_unit
    (𝒞 : BundledPremodularCategory K)
    (X : 𝒞.C)
    [CategoryTheory.Simple X]
    (notUnit :
      (X ≅ 𝒞.simples.simpleObject 𝒞.simples.tensorUnit) → False) :
    tensorUnitProjector 𝒞 X = 0 := by
  classical
  unfold tensorUnitProjector
  apply Finset.sum_eq_zero
  intro i _
  have notUnitSummand : ¬ IsTensorUnitSummand 𝒞 X i := by
    rintro ⟨summandToUnit⟩
    letI : CategoryTheory.Simple ((𝒞.decomposition X).summandObject i) :=
      (𝒞.decomposition X).summand_isSimple i
    have inclusion_ne_zero : (𝒞.decomposition X).inclusion i ≠ 0 := by
      intro inclusion_zero
      have identity_zero :
          𝟙 ((𝒞.decomposition X).summandObject i) = 0 := by
        rw [← (𝒞.decomposition X).pairing_same i, inclusion_zero,
          CategoryTheory.Limits.zero_comp]
      exact CategoryTheory.id_nonzero _ identity_zero
    letI : IsIso ((𝒞.decomposition X).inclusion i) :=
      CategoryTheory.isIso_of_hom_simple inclusion_ne_zero
    exact notUnit
      ((asIso ((𝒞.decomposition X).inclusion i)).symm ≪≫
        summandToUnit ≪≫ 𝒞.simples.unitIso.symm)
  rw [if_neg notUnitSummand]

theorem tensorUnitProjector_eq_identity_of_simple_unit
    (𝒞 : BundledPremodularCategory K)
    (X : 𝒞.C)
    [CategoryTheory.Simple X]
    (unitIso :
      X ≅ 𝒞.simples.simpleObject 𝒞.simples.tensorUnit) :
    tensorUnitProjector 𝒞 X = 𝟙 X := by
  classical
  unfold tensorUnitProjector
  rw [show
    (∑ i : (𝒞.decomposition X).SummandIndex,
      if IsTensorUnitSummand 𝒞 X i then
        (𝒞.decomposition X).projection i ≫
          (𝒞.decomposition X).inclusion i else 0) =
      ∑ i : (𝒞.decomposition X).SummandIndex,
        (𝒞.decomposition X).projection i ≫
          (𝒞.decomposition X).inclusion i by
    apply Finset.sum_congr rfl
    intro i _
    rw [if_pos]
    letI : CategoryTheory.Simple ((𝒞.decomposition X).summandObject i) :=
      (𝒞.decomposition X).summand_isSimple i
    have inclusion_ne_zero : (𝒞.decomposition X).inclusion i ≠ 0 := by
      intro inclusion_zero
      have identity_zero :
          𝟙 ((𝒞.decomposition X).summandObject i) = 0 := by
        rw [← (𝒞.decomposition X).pairing_same i, inclusion_zero,
          CategoryTheory.Limits.zero_comp]
      exact CategoryTheory.id_nonzero _ identity_zero
    letI : IsIso ((𝒞.decomposition X).inclusion i) :=
      CategoryTheory.isIso_of_hom_simple inclusion_ne_zero
    exact ⟨asIso ((𝒞.decomposition X).inclusion i) ≪≫
      unitIso ≪≫ 𝒞.simples.unitIso⟩]
  exact (𝒞.decomposition X).resolution_identity

theorem tensorUnitProjector_singleton_forward_word
    (𝒞 : BundledPremodularCategory K)
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
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple) :
    𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C :=
  let X := 𝒞.simples.simpleObject simple
  η_ X (Xᘁ) ≫
    (tensorUnitProjector 𝒞 X ⊗ₘ 𝟙 (Xᘁ)) ≫
    (β_ X (Xᘁ)).hom ≫
    ε_ X (Xᘁ)

theorem specialCutMeridianMorphismWithoutExplicitTwist_eq
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple) :
    specialCutMeridianMorphismWithoutExplicitTwist 𝒞 simple =
      ribbonTraceMorphism 𝒞 simple
        (tensorUnitProjector 𝒞
          (𝒞.simples.simpleObject simple)) := by
  unfold specialCutMeridianMorphismWithoutExplicitTwist
  rw [ribbonTraceMorphism,
    𝒞.canonicalRibbonTrace_eq_ribbonClosure]
  dsimp only
  have absorbTensor :
      (tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) ⊗ₘ
          𝟙 ((𝒞.simples.simpleObject simple)ᘁ)) ≫
          (𝒞.twist.hom.app
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
