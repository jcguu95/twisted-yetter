import Mathlib

/-!
# Independent semantics: proof-relevant premodular algebra

This file is independent of every Kirby evaluator and presentation
implementation in this repository.  It follows:

* EGNO, Definition 4.1.1: fusion categories;
* EGNO, Definitions 4.7.7 and 4.7.14: pivotal and spherical structures;
* EGNO, Definition 8.10.1: balanced and ribbon structures;
* EGNO, Definition 8.13.1: premodular categories are ribbon fusion categories.

Finite semisimplicity is represented by actual simple objects and actual
biproduct decompositions.  Ribbon compatibility is represented by a natural
twist and its equations.  Neither condition is hidden in an opaque
proposition.
-/

namespace TwistedYetter.Semantics.Independent

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe uK uC uS v

/--
The ambient Mathlib structures of a characteristic-zero braided rigid linear
category.  Tensor product is required to be additive and linear in both
variables.
-/
structure PremodularAmbient
    (K : Type uK) [Field K] where
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

/--
Proof-relevant finite semisimple data.

The decomposition is not merely an existence proposition: it gives the
chosen finite biproduct of simple representatives for every object.
-/
structure FusionSemisimpleData
    (K : Type uK) [Field K] [IsAlgClosed K] [CharZero K]
    (ambient : PremodularAmbient.{uK, uC, v} K) where
  Simple : Type uS
  simpleFintype : Fintype Simple
  simpleDecidableEq : DecidableEq Simple
  simpleObject : Simple → ambient.C
  simple_isSimple :
    (s : Simple) →
      let _ := ambient.category
      let _ := ambient.abelian
      CategoryTheory.Simple (simpleObject s)
  simple_pairwise :
    {s t : Simple} →
      let _ := ambient.category
      Nonempty (simpleObject s ≅ simpleObject t) →
      s = t
  simple_complete :
    (X : ambient.C) →
      let _ := ambient.category
      let _ := ambient.abelian
      CategoryTheory.Simple X →
      ∃ s, Nonempty (X ≅ simpleObject s)
  hom_finite :
    (X Y : ambient.C) →
      let _ := ambient.category
      let _ := ambient.abelian
      let _ := ambient.linear
      FiniteDimensional K (X ⟶ Y)
  multiplicity : ambient.C → Simple → ℕ
  summandInclusion :
    (X : ambient.C) →
      (p : Σ s, Fin (multiplicity X s)) →
      let _ := ambient.category
      simpleObject p.1 ⟶ X
  summandProjection :
    (X : ambient.C) →
      (p : Σ s, Fin (multiplicity X s)) →
      let _ := ambient.category
      X ⟶ simpleObject p.1
  summand_pairing_same :
    (X : ambient.C) →
      (s : Simple) →
      (i : Fin (multiplicity X s)) →
      let _ := ambient.category
      summandInclusion X ⟨s, i⟩ ≫ summandProjection X ⟨s, i⟩ =
        𝟙 (simpleObject s)
  summand_pairing_distinct_copy :
    (X : ambient.C) →
      (s : Simple) →
      (i j : Fin (multiplicity X s)) →
      i ≠ j →
      let _ := ambient.category
      let _ := ambient.abelian
      summandInclusion X ⟨s, i⟩ ≫ summandProjection X ⟨s, j⟩ = 0
  summand_pairing_distinct_simple :
    (X : ambient.C) →
      (s t : Simple) →
      (i : Fin (multiplicity X s)) →
      (j : Fin (multiplicity X t)) →
      s ≠ t →
      let _ := ambient.category
      let _ := ambient.abelian
      summandInclusion X ⟨s, i⟩ ≫ summandProjection X ⟨t, j⟩ = 0
  resolution_identity :
    (X : ambient.C) →
      let _ := ambient.category
      let _ := ambient.abelian
      (∑ s : Simple, ∑ i : Fin (multiplicity X s),
        summandProjection X ⟨s, i⟩ ≫ summandInclusion X ⟨s, i⟩) =
          𝟙 X
  tensorUnit : Simple
  unitIso :
    let _ := ambient.category
    let _ := ambient.monoidal
    simpleObject tensorUnit ≅ 𝟙_ ambient.C
  dual : Simple → Simple
  dualIso :
    (s : Simple) →
      let _ := ambient.category
      let _ := ambient.monoidal
      let _ := ambient.rigid
      (simpleObject s)ᘁ ≅ simpleObject (dual s)
  quantumDimension : Simple → K
  dual_involutive : Function.Involutive dual

attribute [instance] FusionSemisimpleData.simpleFintype
attribute [instance] FusionSemisimpleData.simpleDecidableEq

/--
A twist satisfying the balancing and ribbon duality equations of EGNO
Definition 8.10.1.
-/
structure RibbonStructureData
    (K : Type uK) [Field K]
    (ambient : PremodularAmbient.{uK, uC, v} K) where
  twist :
    let _ := ambient.category
    𝟭 ambient.C ≅ 𝟭 ambient.C
  balancing :
    (X Y : ambient.C) →
      let _ := ambient.category
      let _ := ambient.monoidal
      let _ := ambient.braided
      twist.hom.app (X ⊗ Y) =
        (β_ X Y).hom ≫ (β_ Y X).hom ≫
          (twist.hom.app X ⊗ₘ twist.hom.app Y)
  dual :
    (X : ambient.C) →
      let _ := ambient.category
      let _ := ambient.monoidal
      let _ := ambient.rigid
      (twist.hom.app X)ᘁ = twist.hom.app (Xᘁ)

/--
The frozen v4 algebraic input.  By EGNO Definition 8.13.1 this is exactly a
ribbon fusion category, hence a premodular fusion category.
-/
structure PremodularFusionCategory
    (K : Type uK) [Field K] [IsAlgClosed K] [CharZero K] where
  ambient : PremodularAmbient.{uK, uC, v} K
  semisimple :
    FusionSemisimpleData.{uK, uC, uS, v} K ambient
  ribbon : RibbonStructureData.{uK, uC, v} K ambient
  quantumDimension_sound :
    (s : semisimple.Simple) →
      let _ := ambient.category
      let _ := ambient.abelian
      let _ := ambient.linear
      let _ := ambient.monoidal
      let _ := ambient.rigid
      let _ := ambient.braided
      let X := semisimple.simpleObject s
      semisimple.quantumDimension s • 𝟙 (𝟙_ ambient.C) =
        η_ X (Xᘁ) ≫
          (ribbon.twist.hom.app X ⊗ₘ 𝟙 (Xᘁ)) ≫
          (β_ X (Xᘁ)).hom ≫
          ε_ X (Xᘁ)
  globalDimension_nonzero :
    (∑ s : semisimple.Simple,
      semisimple.quantumDimension s * semisimple.quantumDimension s) ≠ 0

abbrev PremodularFusionCategory.C
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :=
  𝒞.ambient.C

abbrev PremodularFusionCategory.simples
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :=
  𝒞.semisimple

instance PremodularFusionCategory.instCategory
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
    Category.{v} 𝒞.C :=
  𝒞.ambient.category

instance PremodularFusionCategory.instPreadditive
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
    Preadditive 𝒞.C :=
  𝒞.ambient.abelian.toPreadditive

instance PremodularFusionCategory.instLinear
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
    Linear K 𝒞.C :=
  𝒞.ambient.linear

instance PremodularFusionCategory.instMonoidal
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
    MonoidalCategory 𝒞.C :=
  𝒞.ambient.monoidal

instance PremodularFusionCategory.instRigid
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
    RigidCategory 𝒞.C :=
  𝒞.ambient.rigid

instance PremodularFusionCategory.instBraided
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
    BraidedCategory 𝒞.C :=
  𝒞.ambient.braided

instance PremodularFusionCategory.instAbelian
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
    Abelian 𝒞.C :=
  𝒞.ambient.abelian

instance PremodularFusionCategory.instMonoidalPreadditive
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
    MonoidalPreadditive 𝒞.C :=
  𝒞.ambient.monoidalPreadditive

instance PremodularFusionCategory.instMonoidalLinear
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
    MonoidalLinear K 𝒞.C :=
  𝒞.ambient.monoidalLinear

namespace PremodularFusionCategory

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable (𝒞 : PremodularFusionCategory.{uK, uC, v, uS} K)

abbrev SummandIndex (X : 𝒞.C) :=
  Σ s, Fin (𝒞.simples.multiplicity X s)

abbrev summand (X : 𝒞.C) (p : 𝒞.SummandIndex X) : 𝒞.C :=
  𝒞.simples.simpleObject p.1

def fusionMultiplicity
    (left right output : 𝒞.simples.Simple) : ℕ :=
  𝒞.simples.multiplicity
    (𝒞.simples.simpleObject left ⊗ 𝒞.simples.simpleObject right)
    output

def fusionInclusion
    (left right output : 𝒞.simples.Simple)
    (i : Fin (𝒞.fusionMultiplicity left right output)) :
    𝒞.simples.simpleObject output ⟶
      𝒞.simples.simpleObject left ⊗ 𝒞.simples.simpleObject right :=
  𝒞.simples.summandInclusion
    (𝒞.simples.simpleObject left ⊗ 𝒞.simples.simpleObject right)
    ⟨output, i⟩

def fusionProjection
    (left right output : 𝒞.simples.Simple)
    (i : Fin (𝒞.fusionMultiplicity left right output)) :
    𝒞.simples.simpleObject left ⊗ 𝒞.simples.simpleObject right ⟶
      𝒞.simples.simpleObject output :=
  𝒞.simples.summandProjection
    (𝒞.simples.simpleObject left ⊗ 𝒞.simples.simpleObject right)
    ⟨output, i⟩

def globalDimension : K :=
  ∑ s : 𝒞.simples.Simple,
    𝒞.simples.quantumDimension s * 𝒞.simples.quantumDimension s

theorem globalDimension_ne_zero :
    𝒞.globalDimension ≠ 0 :=
  𝒞.globalDimension_nonzero

local instance simpleObject_isSimple (s : 𝒞.simples.Simple) :
    CategoryTheory.Simple (𝒞.simples.simpleObject s) :=
  by
    letI := 𝒞.ambient.category
    letI := 𝒞.ambient.abelian
    exact 𝒞.simples.simple_isSimple s

theorem unit_isSimple : CategoryTheory.Simple (𝟙_ 𝒞.C) :=
  CategoryTheory.Simple.of_iso 𝒞.simples.unitIso.symm

def scalarEndLinearMap (X : 𝒞.C) : K →ₗ[K] (X ⟶ X) where
  toFun scalar := scalar • 𝟙 X
  map_add' left right := by simp [add_smul]
  map_smul' left right := by simp [mul_smul]

theorem scalarEndLinearMap_injective
    (X : 𝒞.C) [CategoryTheory.Simple X] :
    Function.Injective (𝒞.scalarEndLinearMap X) := by
  intro left right equality
  change left • 𝟙 X = right • 𝟙 X at equality
  have zero_smul : (left - right) • 𝟙 X = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr equality
  by_contra not_equal
  exact
    (smul_ne_zero (sub_ne_zero.mpr not_equal)
      (CategoryTheory.id_nonzero X)) zero_smul

theorem scalarEndLinearMap_surjective
    (X : 𝒞.C) [CategoryTheory.Simple X] :
    Function.Surjective (𝒞.scalarEndLinearMap X) := by
  letI : FiniteDimensional K (X ⟶ X) := 𝒞.simples.hom_finite X X
  intro f
  obtain ⟨scalar, scalar_sound⟩ :=
    CategoryTheory.endomorphism_simple_eq_smul_id K f
  exact ⟨scalar, scalar_sound⟩

noncomputable def simpleEndLinearEquiv
    (X : 𝒞.C) [CategoryTheory.Simple X] :
    K ≃ₗ[K] (X ⟶ X) :=
  LinearEquiv.ofBijective
    (𝒞.scalarEndLinearMap X)
    ⟨𝒞.scalarEndLinearMap_injective X,
      𝒞.scalarEndLinearMap_surjective X⟩

noncomputable def unitEndLinearEquiv :
    K ≃ₗ[K] (𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C) := by
  letI : CategoryTheory.Simple (𝟙_ 𝒞.C) := 𝒞.unit_isSimple
  exact 𝒞.simpleEndLinearEquiv (𝟙_ 𝒞.C)

noncomputable def closedScalar
    (f : 𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C) : K :=
  𝒞.unitEndLinearEquiv.symm f

theorem closedScalar_identity :
    𝒞.closedScalar (𝟙 (𝟙_ 𝒞.C)) = 1 := by
  apply 𝒞.unitEndLinearEquiv.injective
  simp [closedScalar, unitEndLinearEquiv, simpleEndLinearEquiv,
    scalarEndLinearMap]

end PremodularFusionCategory

/--
A genuine monoidal natural automorphism of the tensor identity.

The stored simple scalars are not a substitute for naturality: `simple_action`
identifies them with the actual components of the automorphism.
-/
structure TensorIdentityCharacter
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) where
  iso : 𝟭 𝒞.C ≅ 𝟭 𝒞.C
  monoidal : NatTrans.IsMonoidal iso.hom
  value : 𝒞.simples.Simple → Kˣ
  simple_action :
    ∀ s,
      iso.hom.app (𝒞.simples.simpleObject s) =
        (value s : K) • 𝟙 (𝒞.simples.simpleObject s)

/-- A premodular category together with its twisting automorphism. -/
structure TwistedPremodularCategory
    (K : Type uK) [Field K] [IsAlgClosed K] [CharZero K] where
  category : PremodularFusionCategory.{uK, uC, v, uS} K
  character : TensorIdentityCharacter.{uK, uC, v, uS} category

end TwistedYetter.Semantics.Independent
