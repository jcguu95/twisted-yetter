import TwistedYetter.CategoryTheory.Monoidal.IdentityCharacter
import TwistedYetter.CategoryTheory.Premodular.CanonicalSpherical
import TwistedYetter.CategoryTheory.Fusion.PivotalTrace

/-!
# Bundled premodular categories

This is only a first-class wrapper around the Mathlib-shaped category
instances and `PremodularCategory`.  Finite semisimple coordinates are chosen
noncomputably from the class and are not caller-supplied fields.
-/

namespace CategoryTheory

open Limits MonoidalCategory

universe v uK uC uI

structure BundledPremodularCategory
    (K : Type uK) [Field K] [IsAlgClosed K] [CharZero K] where
  C : Type uC
  category : Category.{v} C
  abelian : @Abelian C category
  linear : @Linear K _ C category abelian.toPreadditive
  monoidal : @MonoidalCategory C category
  rigid : @RigidCategory C category monoidal
  braided : @BraidedCategory C category monoidal
  monoidalPreadditive :
    @MonoidalPreadditive C category abelian.toPreadditive monoidal
  monoidalLinear :
    @MonoidalLinear K _ C category abelian.toPreadditive linear monoidal
      monoidalPreadditive
  premodular :
    @PremodularCategory.{v, uK, uC, uI} K _ _ _ C category abelian linear monoidal rigid
      braided monoidalPreadditive monoidalLinear

namespace BundledPremodularCategory

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

instance (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) : Category.{v} 𝒞.C :=
  𝒞.category
instance (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) : Abelian 𝒞.C :=
  𝒞.abelian
instance (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) : Linear K 𝒞.C :=
  𝒞.linear
instance (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) : MonoidalCategory 𝒞.C :=
  𝒞.monoidal
instance (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) : RigidCategory 𝒞.C :=
  𝒞.rigid
instance (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    RightRigidCategory 𝒞.C :=
  𝒞.rigid.toRightRigidCategory
instance (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) : BraidedCategory 𝒞.C :=
  𝒞.braided
instance (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    MonoidalPreadditive 𝒞.C :=
  𝒞.monoidalPreadditive
instance (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) : MonoidalLinear K 𝒞.C :=
  𝒞.monoidalLinear
noncomputable instance
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    (rightDoubleDualFunctor 𝒞.C).Monoidal :=
  drinfeldDoubleDualMonoidal (C := 𝒞.C)
instance (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    PremodularCategory.{v, uK, uC, uI} K 𝒞.C := 𝒞.premodular

noncomputable def simpleSkeleton
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    FiniteSimpleSkeleton.{v, uC, uI} (C := 𝒞.C) :=
  Classical.choice
    (FiniteSemisimpleCategory.finite_simple_skeleton (K := K) (C := 𝒞.C))

noncomputable def decomposition
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) (X : 𝒞.C) :
    FiniteSimpleDecomposition.{v, uC, uI} X :=
  Classical.choice
    (FiniteSemisimpleCategory.finite_simple_decomposition (K := K) X)

abbrev Simple (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :=
  𝒞.simpleSkeleton.SimpleIndex

noncomputable def simpleObject
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) (s : 𝒞.Simple) : 𝒞.C :=
  𝒞.simpleSkeleton.simpleObject s

noncomputable instance simpleObject_isSimple
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) (s : 𝒞.Simple) :
    CategoryTheory.Simple (𝒞.simpleObject s) :=
  𝒞.simpleSkeleton.simple_isSimple s

noncomputable def canonicalSpherical
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    SphericalStructure (C := 𝒞.C) :=
  PremodularCategory.canonicalSphericalStructure (K := K) (C := 𝒞.C)

/-- The balancing supplied by the premodular-category class. -/
def balancing
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    Balancing 𝒞.C :=
  (PremodularCategory.toRibbonCategory
    (K := K) (C := 𝒞.C)).ribbonStructure.toBalancing

/-- The ribbon twist supplied by the premodular-category class. -/
def twist
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    𝟭 𝒞.C ≅ 𝟭 𝒞.C :=
  𝒞.balancing.twist

noncomputable def closedScalar
  (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K)
    (f : 𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C) : K := by
  letI : CategoryTheory.Simple (𝟙_ 𝒞.C) :=
    FusionCategory.tensorUnit_simple (K := K)
  exact (simpleEndLinearEquiv K (𝟙_ 𝒞.C)).symm f

noncomputable def canonicalRibbonTrace
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K)
    {X : 𝒞.C} (f : X ⟶ X) : 𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C :=
  pivotalTrace 𝒞.canonicalSpherical.toPivotalStructure f

/--
The canonical spherical trace is the usual twist-braiding closure.  This is
EGNO equation (8.41), specialized to the canonical pivotal structure of a
ribbon category.
-/
theorem canonicalRibbonTrace_eq_ribbonClosure
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K)
    {X : 𝒞.C} (f : X ⟶ X) :
    𝒞.canonicalRibbonTrace f =
      η_ X (Xᘁ) ≫
        (f ⊗ₘ 𝟙 (Xᘁ)) ≫
        (𝒞.twist.hom.app X ⊗ₘ 𝟙 (Xᘁ)) ≫
        (β_ X (Xᘁ)).hom ≫
        ε_ X (Xᘁ) := by
  simp only [canonicalRibbonTrace, canonicalSpherical,
    PremodularCategory.canonicalSphericalStructure,
    CategoryTheory.canonicalSphericalStructure,
    CategoryTheory.pivotalTrace,
    CategoryTheory.leftCategoricalTrace,
    CategoryTheory.canonicalPivotalStructure,
    CategoryTheory.canonicalPivotalIso_hom_app,
    CategoryTheory.canonicalPivotalHom, twist, balancing]
  simp only [Functor.id_obj]
  have expandTensor :
      ((f ≫ 𝒞.twist.hom.app X ≫ drinfeldHom X) ⊗ₘ 𝟙 (Xᘁ)) =
        (f ⊗ₘ 𝟙 (Xᘁ)) ≫
          (𝒞.twist.hom.app X ⊗ₘ 𝟙 (Xᘁ)) ≫
          (drinfeldHom X ⊗ₘ 𝟙 (Xᘁ)) := by
    calc
      _ = ((f ≫ 𝒞.twist.hom.app X) ⊗ₘ 𝟙 (Xᘁ)) ≫
            (drinfeldHom X ⊗ₘ 𝟙 (Xᘁ)) := by
              simpa only [Category.assoc, Category.comp_id] using
                (tensorHom_comp_tensorHom
                  (f ≫ 𝒞.twist.hom.app X) (𝟙 (Xᘁ))
                  (drinfeldHom X) (𝟙 (Xᘁ))).symm
      _ = ((f ⊗ₘ 𝟙 (Xᘁ)) ≫
            (𝒞.twist.hom.app X ⊗ₘ 𝟙 (Xᘁ))) ≫
            (drinfeldHom X ⊗ₘ 𝟙 (Xᘁ)) := by
              rw [show
                ((f ≫ 𝒞.twist.hom.app X) ⊗ₘ 𝟙 (Xᘁ)) =
                  (f ⊗ₘ 𝟙 (Xᘁ)) ≫
                    (𝒞.twist.hom.app X ⊗ₘ 𝟙 (Xᘁ)) by
                simpa only [Category.comp_id] using
                  (tensorHom_comp_tensorHom
                    f (𝟙 (Xᘁ))
                    (𝒞.twist.hom.app X) (𝟙 (Xᘁ))).symm]
      _ = _ := by simp only [Category.assoc]
  calc
    _ = η_ X (Xᘁ) ≫
          ((f ⊗ₘ 𝟙 (Xᘁ)) ≫
            (𝒞.twist.hom.app X ⊗ₘ 𝟙 (Xᘁ)) ≫
            (drinfeldHom X ⊗ₘ 𝟙 (Xᘁ))) ≫
          ε_ (Xᘁ) ((Xᘁ)ᘁ) :=
        congrArg
          (fun q => η_ X (Xᘁ) ≫ q ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ))
          expandTensor
    _ = _ := by
      have closeDrinfeld := drinfeldHom_tensor_evaluation X
      simpa only [Category.assoc] using
        congrArg
          (fun q =>
            η_ X (Xᘁ) ≫
              (f ⊗ₘ 𝟙 (Xᘁ)) ≫
              (𝒞.twist.hom.app X ⊗ₘ 𝟙 (Xᘁ)) ≫ q)
          closeDrinfeld

noncomputable def quantumDimension
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) (s : 𝒞.Simple) : K :=
  𝒞.closedScalar (𝒞.canonicalRibbonTrace (𝟙 (𝒞.simpleObject s)))

noncomputable def globalDimension
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) : K :=
  ∑ s : 𝒞.Simple, 𝒞.quantumDimension s * 𝒞.quantumDimension s

/--
Finite labels and the unit/dual representatives chosen from finite
semisimplicity. These coordinates are derived implementation choices, not
fields of the public premodular-category input.
-/
structure ChosenSimpleFamily
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) where
  skeleton : FiniteSimpleSkeleton.{v, uC, uI} (C := 𝒞.C)
  tensorUnit : skeleton.SimpleIndex
  unitIso : skeleton.simpleObject tensorUnit ≅ 𝟙_ 𝒞.C
  dual : skeleton.SimpleIndex → skeleton.SimpleIndex
  dualIso : (s : skeleton.SimpleIndex) →
    (skeleton.simpleObject s)ᘁ ≅ skeleton.simpleObject (dual s)

noncomputable def chosenSimpleFamily
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    ChosenSimpleFamily 𝒞 := by
  let skeleton := 𝒞.simpleSkeleton
  let unitWitness := skeleton.simple_complete (𝟙_ 𝒞.C)
    (FusionCategory.tensorUnit_simple (K := K))
  let tensorUnit := Classical.choose unitWitness
  let unitIso := Classical.choice (Classical.choose_spec unitWitness)
  let pivotal := 𝒞.canonicalSpherical.toPivotalStructure
  let dualWitness : (s : skeleton.SimpleIndex) →
      ∃ t, Nonempty ((skeleton.simpleObject s)ᘁ ≅ skeleton.simpleObject t) := by
    intro s
    letI : CategoryTheory.Simple (skeleton.simpleObject s) :=
      skeleton.simple_isSimple s
    letI : CategoryTheory.Simple ((skeleton.simpleObject s)ᘁ) :=
      simple_rightDual_of_pivotal K pivotal (skeleton.simpleObject s)
    exact skeleton.simple_complete ((skeleton.simpleObject s)ᘁ) inferInstance
  exact
    { skeleton := skeleton
      tensorUnit := tensorUnit
      unitIso := unitIso.symm
      dual := fun s => Classical.choose (dualWitness s)
      dualIso := fun s => Classical.choice (Classical.choose_spec (dualWitness s)) }

noncomputable def simples
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    ChosenSimpleFamily 𝒞 :=
  𝒞.chosenSimpleFamily

namespace ChosenSimpleFamily

variable {𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K}

abbrev Simple (family : ChosenSimpleFamily 𝒞) := family.skeleton.SimpleIndex

instance (family : ChosenSimpleFamily 𝒞) : Fintype family.Simple :=
  family.skeleton.simpleFintype

instance (family : ChosenSimpleFamily 𝒞) : DecidableEq family.Simple :=
  family.skeleton.simpleDecidableEq

def simpleObject (family : ChosenSimpleFamily 𝒞) (s : family.Simple) : 𝒞.C :=
  family.skeleton.simpleObject s

instance simple_isSimple (family : ChosenSimpleFamily 𝒞) (s : family.Simple) :
    CategoryTheory.Simple (family.simpleObject s) :=
  family.skeleton.simple_isSimple s

theorem simple_pairwise (family : ChosenSimpleFamily 𝒞)
    {s t : family.Simple}
    (iso : Nonempty (family.simpleObject s ≅ family.simpleObject t)) : s = t :=
  family.skeleton.simple_pairwise iso

theorem simple_complete (family : ChosenSimpleFamily 𝒞)
    (X : 𝒞.C) [CategoryTheory.Simple X] :
    ∃ s, Nonempty (X ≅ family.simpleObject s) :=
  family.skeleton.simple_complete X inferInstance

theorem hom_finite (X Y : 𝒞.C) :
    FiniteDimensional K (X ⟶ Y) :=
  FiniteSemisimpleCategory.hom_finite X Y

noncomputable def quantumDimension
    (family : ChosenSimpleFamily 𝒞) (s : family.Simple) : K :=
  𝒞.closedScalar
    (𝒞.canonicalRibbonTrace (𝟙 (family.simpleObject s)))

end ChosenSimpleFamily

noncomputable def unitEndLinearEquiv
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    K ≃ₗ[K] (𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C) := by
  letI : CategoryTheory.Simple (𝟙_ 𝒞.C) :=
    FusionCategory.tensorUnit_simple (K := K)
  exact simpleEndLinearEquiv K (𝟙_ 𝒞.C)

theorem closedScalar_identity
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K) :
    𝒞.closedScalar (𝟙 (𝟙_ 𝒞.C)) = 1 := by
  change 𝒞.unitEndLinearEquiv.symm (𝟙 (𝟙_ 𝒞.C)) = 1
  have unit_image :
      𝒞.unitEndLinearEquiv (1 : K) = 𝟙 (𝟙_ 𝒞.C) := by
    change (1 : K) • 𝟙 (𝟙_ 𝒞.C) = 𝟙 (𝟙_ 𝒞.C)
    simp
  rw [← unit_image]
  exact 𝒞.unitEndLinearEquiv.symm_apply_apply 1

theorem closedScalar_smul_identity
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K)
    (scalar : K) :
    𝒞.closedScalar (scalar • 𝟙 (𝟙_ 𝒞.C)) = scalar :=
  𝒞.unitEndLinearEquiv.symm_apply_apply scalar

theorem closedScalar_comp
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K)
    (left right : 𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C) :
    𝒞.closedScalar (left ≫ right) =
      𝒞.closedScalar left * 𝒞.closedScalar right := by
  let leftScalar := 𝒞.closedScalar left
  let rightScalar := 𝒞.closedScalar right
  have left_eq : left = leftScalar • 𝟙 (𝟙_ 𝒞.C) :=
    (𝒞.unitEndLinearEquiv.apply_symm_apply left).symm
  have right_eq : right = rightScalar • 𝟙 (𝟙_ 𝒞.C) :=
    (𝒞.unitEndLinearEquiv.apply_symm_apply right).symm
  rw [left_eq, right_eq]
  simp only [Category.comp_id, CategoryTheory.Linear.comp_smul, smul_smul]
  rw [𝒞.closedScalar_smul_identity, 𝒞.closedScalar_smul_identity,
    𝒞.closedScalar_smul_identity]
  exact mul_comm _ _

theorem closedMorphism_eq_scalar_smul_identity
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K)
    (f : 𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C) :
    f = 𝒞.closedScalar f • 𝟙 (𝟙_ 𝒞.C) :=
  (𝒞.unitEndLinearEquiv.apply_symm_apply f).symm

theorem canonicalRibbonTrace_identity
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K)
    (simple : 𝒞.simples.Simple) :
    𝒞.canonicalRibbonTrace (𝟙 (𝒞.simples.simpleObject simple)) =
      𝒞.simples.quantumDimension simple • 𝟙 (𝟙_ 𝒞.C) :=
  𝒞.closedMorphism_eq_scalar_smul_identity _

theorem canonicalRibbonTrace_zero
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K)
    (X : 𝒞.C) :
    𝒞.canonicalRibbonTrace (0 : X ⟶ X) = 0 := by
  simp [canonicalRibbonTrace, pivotalTrace, leftCategoricalTrace]

theorem simples_quantumDimension_eq
    (𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K)
    (simple : 𝒞.simples.Simple) :
    𝒞.simples.quantumDimension simple = 𝒞.quantumDimension simple := by
  rfl

end BundledPremodularCategory

/-- The clean public algebraic input `(𝒞, η)`. -/
structure TwistedPremodularCategory
    (K : Type uK) [Field K] [IsAlgClosed K] [CharZero K] where
  category : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K
  character : TensorIdentityCharacter (C := category.C)

namespace TensorIdentityCharacter

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {𝒞 : CategoryTheory.BundledPremodularCategory.{v, uK, uC, uI} K}

/-- Character value on a chosen simple label, derived by Schur's lemma. -/
noncomputable def value
    (character : CategoryTheory.TensorIdentityCharacter (C := 𝒞.C))
    (s : 𝒞.simples.Simple) : Kˣ :=
  character.simpleValue (K := K) (𝒞.simples.simpleObject s)

@[simp]
theorem value_val
    (character : CategoryTheory.TensorIdentityCharacter (C := 𝒞.C))
    (s : 𝒞.simples.Simple) :
    (character.value (𝒞 := 𝒞) s : K) =
      character.simpleScalar (K := K) (𝒞.simples.simpleObject s) :=
  rfl

theorem component_on_simple_eq_value_smul_identity
    (character : CategoryTheory.TensorIdentityCharacter (C := 𝒞.C))
    (s : 𝒞.simples.Simple) :
    character.iso.hom.app (𝒞.simples.simpleObject s) =
      (character.value (𝒞 := 𝒞) s : K) •
        𝟙 (𝒞.simples.simpleObject s) :=
  character.component_on_simple_eq_scalar_smul_identity
    (K := K) (𝒞.simples.simpleObject s)

theorem tensorUnitSimple_hom
    (character : CategoryTheory.TensorIdentityCharacter (C := 𝒞.C)) :
    character.iso.hom.app
        (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) =
      𝟙 (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) := by
  change character.iso.hom.app
      (𝒞.simples.skeleton.simpleObject 𝒞.simples.tensorUnit) =
    𝟙 (𝒞.simples.skeleton.simpleObject 𝒞.simples.tensorUnit)
  apply (cancel_mono 𝒞.simples.unitIso.hom).1
  simpa [CategoryTheory.TensorIdentityCharacter.unit_hom character] using
    (character.iso.hom.naturality 𝒞.simples.unitIso.hom).symm

theorem tensorUnitSimple_inv
    (character : CategoryTheory.TensorIdentityCharacter (C := 𝒞.C)) :
    character.iso.inv.app
        (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) =
      𝟙 (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) := by
  rw [← cancel_epi
    (character.iso.hom.app
      (𝒞.simples.simpleObject 𝒞.simples.tensorUnit))]
  rw [character.iso.hom_inv_id_app]
  simp [character.tensorUnitSimple_hom (𝒞 := 𝒞)]

theorem rightAdjointMate_smul_identity
    (scalar : K) (X : 𝒞.C) :
    (scalar • 𝟙 X)ᘁ = scalar • 𝟙 (Xᘁ) :=
  CategoryTheory.rightAdjointMate_smul K scalar (𝟙 X) |>.trans (by simp)

end TensorIdentityCharacter

end CategoryTheory
