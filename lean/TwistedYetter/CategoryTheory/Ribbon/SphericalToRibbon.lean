import TwistedYetter.CategoryTheory.FiniteSemisimple.Ext
import TwistedYetter.CategoryTheory.Fusion.Dual
import TwistedYetter.CategoryTheory.Fusion.Schur
import TwistedYetter.CategoryTheory.Fusion.TraceNonzero
import TwistedYetter.CategoryTheory.Ribbon.CanonicalSpherical
import TwistedYetter.CategoryTheory.Ribbon.DrinfeldTrace

/-!
# From pivotal structures to balancings

This file formalizes the algebraic first half of the converse direction of
EGNO Proposition 8.10.12. A pivotal structure for the Drinfeld double-dual
tensorator determines a balancing by `theta = psi ≫ u⁻¹`, and reconstructing
the canonical pivotal structure recovers the original pivotal structure.

The remaining implication from sphericality to the ribbon duality equation is
not claimed here. EGNO's proof additionally uses automatic unimodularity of a
fusion category, its canonical Radford quadruple-dual isomorphism, and the
trace identity in Corollary 7.21.8.
-/

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

universe u v

section Balancing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

local instance : (rightDoubleDualFunctor C).Monoidal :=
  drinfeldDoubleDualMonoidal (C := C)

/-- EGNO equation (8.35), solved for the twist: `theta = psi ≫ u⁻¹`. -/
def balancingIsoOfPivotal (pivotal : PivotalStructure C) : 𝟭 C ≅ 𝟭 C :=
  pivotal.iso ≪≫ (drinfeldNatIso (C := C)).symm

/-- The component formula for the balancing reconstructed from a pivotal structure. -/
theorem balancingIsoOfPivotal_hom_app
    (pivotal : PivotalStructure C) (X : C) :
    (balancingIsoOfPivotal pivotal).hom.app X =
      pivotal.iso.hom.app X ≫ (drinfeldIso X).inv :=
  rfl

/-- The reconstructed twist satisfies the balancing equation. -/
theorem balancingIsoOfPivotal_tensor
    (pivotal : PivotalStructure C) (X Y : C) :
    (balancingIsoOfPivotal pivotal).hom.app (X ⊗ Y) =
      monodromyHom X Y ≫
        ((balancingIsoOfPivotal pivotal).hom.app X ⊗ₘ
          (balancingIsoOfPivotal pivotal).hom.app Y) := by
  letI : NatTrans.IsMonoidal pivotal.iso.hom := pivotal.monoidal
  let θX := (balancingIsoOfPivotal pivotal).hom.app X
  let θY := (balancingIsoOfPivotal pivotal).hom.app Y
  have pivotalTensor :
      pivotal.iso.hom.app (X ⊗ Y) =
        (pivotal.iso.hom.app X ⊗ₘ pivotal.iso.hom.app Y) ≫
          Functor.LaxMonoidal.μ (rightDoubleDualFunctor C) X Y := by
    have h := NatTrans.IsMonoidal.tensor (τ := pivotal.iso.hom) X Y
    change
      𝟙 (X ⊗ Y) ≫ pivotal.iso.hom.app (X ⊗ Y) =
        (pivotal.iso.hom.app X ⊗ₘ pivotal.iso.hom.app Y) ≫
          Functor.LaxMonoidal.μ (rightDoubleDualFunctor C) X Y at h
    simpa only [Category.id_comp] using h
  have θ_tensor_drinfeld :
      (θX ⊗ₘ θY) ≫
          (drinfeldHom X ⊗ₘ drinfeldHom Y) =
        pivotal.iso.hom.app X ⊗ₘ pivotal.iso.hom.app Y := by
    dsimp [θX, θY]
    change
      ((pivotal.iso.hom.app X ≫ (drinfeldIso X).inv) ⊗ₘ
          (pivotal.iso.hom.app Y ≫ (drinfeldIso Y).inv)) ≫
          ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) = _
    rw [← MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  apply (cancel_mono (drinfeldIso (X ⊗ Y)).hom).1
  simp only [balancingIsoOfPivotal_hom_app, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [pivotalTensor]
  rw [← θ_tensor_drinfeld]
  have hDefect :
      (drinfeldHom X ⊗ₘ drinfeldHom Y) ≫
          Functor.LaxMonoidal.μ (rightDoubleDualFunctor C) X Y =
        monodromyHom X Y ≫ drinfeldHom (X ⊗ Y) :=
    drinfeld_tensor_defect X Y
  slice_lhs 2 3 => exact hDefect
  have hNatural :
      (θX ⊗ₘ θY) ≫ monodromyHom X Y =
        monodromyHom X Y ≫ (θX ⊗ₘ θY) :=
    monodromyHom_naturality θX θY
  have hNaturalAssoc :
      ((θX ⊗ₘ θY) ≫ monodromyHom X Y) ≫ drinfeldHom (X ⊗ Y) =
        (monodromyHom X Y ≫ (θX ⊗ₘ θY)) ≫ drinfeldHom (X ⊗ Y) :=
    congrArg (fun k => k ≫ drinfeldHom (X ⊗ Y)) hNatural
  calc
    (θX ⊗ₘ θY) ≫
          (monodromyHom X Y ≫ drinfeldHom (X ⊗ Y)) =
        ((θX ⊗ₘ θY) ≫ monodromyHom X Y) ≫
          drinfeldHom (X ⊗ Y) := (Category.assoc _ _ _).symm
    _ = (monodromyHom X Y ≫ (θX ⊗ₘ θY)) ≫
          drinfeldHom (X ⊗ Y) := hNaturalAssoc
    _ = _ := by
      rfl

/-- The balancing reconstructed from a pivotal structure. -/
def balancingOfPivotal (pivotal : PivotalStructure C) : Balancing C where
  twist := balancingIsoOfPivotal pivotal
  tensor := by
    intro X Y
    simpa only [monodromyHom, Category.assoc] using
      balancingIsoOfPivotal_tensor pivotal X Y

/-- Reconstructing the canonical pivotal isomorphism recovers the original one. -/
theorem canonicalPivotalIso_balancingOfPivotal
    (pivotal : PivotalStructure C) :
    canonicalPivotalIso (balancingOfPivotal pivotal) = pivotal.iso := by
  ext X
  simp [canonicalPivotalIso, balancingOfPivotal,
    balancingIsoOfPivotal]

/-- A spherical pivotal structure determines the same canonical balancing. -/
def balancingOfSpherical (spherical : SphericalStructure (C := C)) : Balancing C :=
  balancingOfPivotal spherical.toPivotalStructure

/-- The balancing reconstructed from a spherical structure recovers its pivotal isomorphism. -/
theorem canonicalPivotalIso_balancingOfSpherical
    (spherical : SphericalStructure (C := C)) :
    canonicalPivotalIso (balancingOfSpherical spherical) =
      spherical.toPivotalStructure.iso :=
  canonicalPivotalIso_balancingOfPivotal spherical.toPivotalStructure

end Balancing

section SimpleReduction

universe uK uI

variable
  {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
  [MonoidalPreadditive C]

local instance simpleReductionRightRigidCategory : RightRigidCategory C :=
  RigidCategory.toRightRigidCategory

/--
In a finite semisimple category, the ribbon duality equation for a balancing
is determined by its values on simple objects.
-/
noncomputable def ribbonStructureOfBalancing_of_duality_on_simple
    (K : Type uK) [Field K] [Linear K C]
    [FiniteSemisimpleCategory.{v, uK, u, uI} K C]
    (balancing : Balancing C)
    (duality_on_simple : (X : C) → [Simple X] →
      (balancing.twist.hom.app X)ᘁ =
        balancing.twist.hom.app (Xᘁ)) :
    RibbonStructure C where
  toBalancing := balancing
  duality := by
    intro X
    let decomposition := Classical.choice
      (FiniteSemisimpleCategory.finite_simple_decomposition (K := K) X)
    apply hom_ext_of_finite_resolution
      (fun i ↦ rightAdjointMate (decomposition.inclusion i))
      (fun i ↦ rightAdjointMate (decomposition.projection i))
    · calc
        (∑ i, rightAdjointMate (decomposition.inclusion i) ≫
              rightAdjointMate (decomposition.projection i)) =
            ∑ i, rightAdjointMate
              (decomposition.projection i ≫ decomposition.inclusion i) := by
                apply Finset.sum_congr rfl
                intro i _
                exact (comp_rightAdjointMate).symm
        _ = rightAdjointMate
              (∑ i, decomposition.projection i ≫
                decomposition.inclusion i) :=
              (rightAdjointMate_sum _).symm
        _ = 𝟙 (Xᘁ) := by
              rw [decomposition.resolution_identity]
              exact rightAdjointMate_id
    · intro i
      letI : Simple (decomposition.summandObject i) :=
        decomposition.summand_isSimple i
      have dual_naturality := congrArg rightAdjointMate
        (balancing.twist.hom.naturality (decomposition.projection i))
      have target_naturality := balancing.twist.hom.naturality
        (rightAdjointMate (decomposition.projection i))
      simp only [comp_rightAdjointMate] at dual_naturality
      have simple_duality_whiskered :
          rightAdjointMate
                (balancing.twist.hom.app (decomposition.summandObject i)) ≫
              rightAdjointMate (decomposition.projection i) =
            balancing.twist.hom.app
                ((decomposition.summandObject i)ᘁ) ≫
              rightAdjointMate (decomposition.projection i) := by
        simpa using congrArg
          (fun q ↦ q ≫ rightAdjointMate (decomposition.projection i))
          (duality_on_simple (decomposition.summandObject i))
      have target_naturality_clean :
          balancing.twist.hom.app
                ((decomposition.summandObject i)ᘁ) ≫
              rightAdjointMate (decomposition.projection i) =
            rightAdjointMate (decomposition.projection i) ≫
              balancing.twist.hom.app (Xᘁ) := by
        simpa using target_naturality.symm
      exact dual_naturality.symm.trans
        (simple_duality_whiskered.trans target_naturality_clean)

end SimpleReduction

section Converse

universe uK uI

variable
  (K : Type uK) [Field K] [IsAlgClosed K]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear K C]
  [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
  [MonoidalPreadditive C] [MonoidalLinear K C]
  [FusionCategory.{v, uK, u, uI} K C]

local instance converseRightRigidCategory : RightRigidCategory C :=
  RigidCategory.toRightRigidCategory

local instance converseDoubleDualMonoidal :
    (rightDoubleDualFunctor C).Monoidal :=
  drinfeldDoubleDualMonoidal (C := C)

include K

/--
For a simple object, sphericality of the pivotal structure associated to a
balancing forces the balancing to commute with the selected right dual.

This is the Schur-and-trace step in EGNO, Proposition 8.10.12.  The common
nonzero trace closed off in the proof is the graphical form of the expression
identified using EGNO, Theorem 8.10.7 and Corollary 7.21.8.
-/
theorem balancing_duality_on_simple_of_canonicalPivotal_dimension_dual
    (balancing : Balancing C)
    (dimension_dual : ∀ Y : C,
      pivotalDimension (canonicalPivotalStructure balancing) Y =
        pivotalDimension (canonicalPivotalStructure balancing) (Yᘁ))
    (X : C) [Simple X] :
    (balancing.twist.hom.app X)ᘁ =
      balancing.twist.hom.app (Xᘁ) := by
  let pivotal := canonicalPivotalStructure balancing
  letI : Simple (Xᘁ) := simple_rightDual_of_pivotal K pivotal X
  letI : FiniteDimensional K (X ⟶ X) :=
    FiniteSemisimpleCategory.hom_finite X X
  letI : FiniteDimensional K ((Xᘁ) ⟶ (Xᘁ)) :=
    FiniteSemisimpleCategory.hom_finite (Xᘁ) (Xᘁ)
  let θX : X ⟶ X := balancing.twist.hom.app X
  let θXd : (Xᘁ) ⟶ (Xᘁ) := balancing.twist.hom.app (Xᘁ)
  change θXᘁ = θXd
  obtain ⟨a, ha⟩ :=
    endomorphism_simple_eq_smul_id K θX
  obtain ⟨b, hb⟩ :=
    endomorphism_simple_eq_smul_id K θXd
  let t : 𝟙_ C ⟶ 𝟙_ C := leftCategoricalTrace (drinfeldHom X)
  have dimension_X :
      pivotalDimension pivotal X = a • t := by
    change leftCategoricalTrace
      (balancing.twist.hom.app X ≫ drinfeldHom X) = a • t
    change leftCategoricalTrace (θX ≫ drinfeldHom X) = a • t
    rw [← ha]
    simp only [CategoryTheory.Linear.smul_comp, Category.id_comp]
    exact leftCategoricalTrace_smul K a (drinfeldHom X)
  have dimension_dual_X :
      pivotalDimension pivotal (Xᘁ) = b • t := by
    change leftCategoricalTrace
      (balancing.twist.hom.app (Xᘁ) ≫ drinfeldHom (Xᘁ)) = b • t
    change leftCategoricalTrace (θXd ≫ drinfeldHom (Xᘁ)) = b • t
    rw [← hb]
    simp only [CategoryTheory.Linear.smul_comp, Category.id_comp]
    rw [leftCategoricalTrace_smul]
    exact congrArg (fun trace ↦ b • trace)
      (leftCategoricalTrace_drinfeldHom_dual X).symm
  have t_ne_zero : t ≠ 0 := by
    intro t_zero
    have dimension_zero : pivotalDimension pivotal X = 0 := by
      rw [dimension_X, t_zero, smul_zero]
    exact (pivotalDimension_ne_zero_of_simple K pivotal X) dimension_zero
  have scalar_smul_eq : a • t = b • t := by
    calc
      a • t = pivotalDimension pivotal X := dimension_X.symm
      _ = pivotalDimension pivotal (Xᘁ) := dimension_dual X
      _ = b • t := dimension_dual_X
  have scalar_eq : a = b :=
    smul_left_injective K t_ne_zero scalar_smul_eq
  calc
    θXᘁ = (a • 𝟙 X)ᘁ := congrArg rightAdjointMate ha.symm
    _ = a • (𝟙 X)ᘁ := rightAdjointMate_smul K a (𝟙 X)
    _ = a • 𝟙 (Xᘁ) := by rw [rightAdjointMate_id]
    _ = b • 𝟙 (Xᘁ) := by rw [scalar_eq]
    _ = θXd := hb

/--
The spherical-to-ribbon implication of EGNO, Proposition 8.10.12, stated
directly using the dual-invariance of the canonical pivotal dimension.
-/
noncomputable def ribbonStructureOfBalancing_of_canonicalPivotal_dimension_dual
    (balancing : Balancing C)
    (dimension_dual : ∀ X : C,
      pivotalDimension (canonicalPivotalStructure balancing) X =
        pivotalDimension (canonicalPivotalStructure balancing) (Xᘁ)) :
    RibbonStructure C :=
  ribbonStructureOfBalancing_of_duality_on_simple K balancing
    (fun X _ ↦
      balancing_duality_on_simple_of_canonicalPivotal_dimension_dual
        (K := K) balancing dimension_dual X)

/-- A spherical structure recovers a ribbon structure on its associated balancing. -/
noncomputable def ribbonStructureOfSpherical
    (spherical : SphericalStructure (C := C)) :
    RibbonStructure C := by
  let balancing := balancingOfSpherical spherical
  refine ribbonStructureOfBalancing_of_canonicalPivotal_dimension_dual
    (K := K) balancing ?_
  intro X
  change leftCategoricalTrace
      ((canonicalPivotalIso balancing).hom.app X) =
    leftCategoricalTrace
      ((canonicalPivotalIso balancing).hom.app (Xᘁ))
  dsimp only [balancing]
  rw [canonicalPivotalIso_balancingOfSpherical spherical]
  exact spherical.dimension_dual X

end Converse

end CategoryTheory
