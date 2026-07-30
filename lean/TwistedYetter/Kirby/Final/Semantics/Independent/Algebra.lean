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

The law fields in this file are domain-defining assumptions carried by the
input category itself.  They say what qualifies as a premodular fusion
category; they are not external topology or evaluator axioms.  All external
literature and topology inputs live in `EntranceAxioms`.
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
  twist_dual_compatibility :
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
  /--
  EGNO, Proposition 8.10.14, equation (8.41), printed p. 220:
  the categorical dimension is the scalar obtained by closing the
  twist-braiding ribbon trace.
  -/
  quantumDimension_eq_ribbonTrace :
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

/--
The chosen simple-label duality is involutive.  This is derived from the
stored dual representatives, braided rigidity, uniqueness of right duals,
and uniqueness of the chosen simple representatives.
-/
theorem dual_involutive : Function.Involutive 𝒞.simples.dual := by
  letI : Category 𝒞.C := 𝒞.ambient.category
  letI : MonoidalCategory 𝒞.C := 𝒞.ambient.monoidal
  letI : RightRigidCategory 𝒞.C := 𝒞.ambient.rigid.toRightRigidCategory
  letI : BraidedCategory 𝒞.C := 𝒞.ambient.braided
  intro s
  apply 𝒞.simples.simple_pairwise
  letI : ExactPairing
      (𝒞.simples.simpleObject s)
      (𝒞.simples.simpleObject (𝒞.simples.dual s)) :=
    exactPairingCongrRight (𝒞.simples.dualIso s).symm
  let swapped : ExactPairing
      (𝒞.simples.simpleObject (𝒞.simples.dual s))
      (𝒞.simples.simpleObject s) :=
    BraidedCategory.exactPairing_swap
      (𝒞.simples.simpleObject s)
      (𝒞.simples.simpleObject (𝒞.simples.dual s))
  let comparison :
      𝒞.simples.simpleObject s ≅
        (𝒞.simples.simpleObject (𝒞.simples.dual s))ᘁ :=
    rightDualIso swapped
      (inferInstance :
        ExactPairing
          (𝒞.simples.simpleObject (𝒞.simples.dual s))
          ((𝒞.simples.simpleObject (𝒞.simples.dual s))ᘁ))
  let secondDualIso :
      (𝒞.simples.simpleObject (𝒞.simples.dual s))ᘁ ≅
        𝒞.simples.simpleObject (𝒞.simples.dual (𝒞.simples.dual s)) := by
    simpa only using 𝒞.simples.dualIso (𝒞.simples.dual s)
  exact
    ⟨(comparison ≪≫ secondDualIso).symm⟩

def globalDimension : K :=
  ∑ s : 𝒞.simples.Simple,
    𝒞.simples.quantumDimension s * 𝒞.simples.quantumDimension s

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

/-- A genuine monoidal natural automorphism of the tensor identity. -/
structure TensorIdentityCharacter
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) where
  iso : 𝟭 𝒞.C ≅ 𝟭 𝒞.C
  monoidal : NatTrans.IsMonoidal iso.hom

namespace TensorIdentityCharacter

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {𝒞 : PremodularFusionCategory.{uK, uC, v, uS} K}

/-- Monoidality determines the component on a tensor product. -/
theorem tensor_hom
    (character : TensorIdentityCharacter 𝒞)
    (X Y : 𝒞.C) :
    character.iso.hom.app (X ⊗ Y) =
      character.iso.hom.app X ⊗ₘ character.iso.hom.app Y := by
  letI : NatTrans.IsMonoidal character.iso.hom := character.monoidal
  simpa using
    (NatTrans.IsMonoidal.tensor (τ := character.iso.hom) X Y)

/-- Monoidality determines the component on the tensor unit. -/
theorem unit_hom
    (character : TensorIdentityCharacter 𝒞) :
    character.iso.hom.app (𝟙_ 𝒞.C) = 𝟙 (𝟙_ 𝒞.C) := by
  letI : NatTrans.IsMonoidal character.iso.hom := character.monoidal
  simpa using (NatTrans.IsMonoidal.unit (τ := character.iso.hom))

/-- The character is identity on the chosen simple representative of the unit. -/
theorem tensorUnitSimple_hom
    (character : TensorIdentityCharacter 𝒞) :
    character.iso.hom.app
        (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) =
      𝟙 (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) := by
  apply (cancel_mono 𝒞.simples.unitIso.hom).1
  simpa [unit_hom character] using
    (character.iso.hom.naturality 𝒞.simples.unitIso.hom).symm

/-- The inverse character is likewise identity on the unit representative. -/
theorem tensorUnitSimple_inv
    (character : TensorIdentityCharacter 𝒞) :
    character.iso.inv.app
        (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) =
      𝟙 (𝒞.simples.simpleObject 𝒞.simples.tensorUnit) := by
  rw [← cancel_epi
    (character.iso.hom.app
      (𝒞.simples.simpleObject 𝒞.simples.tensorUnit))]
  rw [character.iso.hom_inv_id_app]
  simp [character.tensorUnitSimple_hom]

/--
The character component on a selected right dual is forced by rigidity: it
is the right mate of the inverse component on the original object.
-/
theorem hom_app_rightDual
    (character : TensorIdentityCharacter 𝒞)
    (X : 𝒞.C) :
    character.iso.hom.app Xᘁ =
      (character.iso.inv.app X)ᘁ := by
  letI : NatTrans.IsMonoidal character.iso.hom := character.monoidal
  have unitLaw :
      character.iso.hom.app (𝟙_ 𝒞.C) = 𝟙 (𝟙_ 𝒞.C) := by
    simpa using
      (NatTrans.IsMonoidal.unit
        (τ := character.iso.hom))
  have tensorLaw :
      character.iso.hom.app (Xᘁ ⊗ X) =
        character.iso.hom.app Xᘁ ⊗ₘ
          character.iso.hom.app X := by
    simpa using
      (NatTrans.IsMonoidal.tensor
        (τ := character.iso.hom) Xᘁ X)
  have evaluationNaturality :
      character.iso.hom.app (Xᘁ ⊗ X) ≫ ε_ X Xᘁ =
        ε_ X Xᘁ := by
    simpa [unitLaw] using
      (character.iso.hom.naturality (ε_ X Xᘁ)).symm
  have expandedNaturality :
      (character.iso.hom.app Xᘁ ▷ X) ≫
          (Xᘁ ◁ character.iso.hom.app X) ≫
          ε_ X Xᘁ =
        ε_ X Xᘁ := by
    have tensorEvaluation :
        (character.iso.hom.app Xᘁ ⊗ₘ
            character.iso.hom.app X) ≫ ε_ X Xᘁ =
          ε_ X Xᘁ := by
      rw [← tensorLaw]
      exact evaluationNaturality
    rw [MonoidalCategory.tensorHom_def] at tensorEvaluation
    simpa only [Category.assoc] using tensorEvaluation
  have dualEvaluation :
      (character.iso.hom.app Xᘁ ▷ X) ≫ ε_ X Xᘁ =
        (Xᘁ ◁ character.iso.inv.app X) ≫ ε_ X Xᘁ := by
    symm
    calc
      (Xᘁ ◁ character.iso.inv.app X) ≫ ε_ X Xᘁ =
          (Xᘁ ◁ character.iso.inv.app X) ≫
            ((character.iso.hom.app Xᘁ ▷ X) ≫
              (Xᘁ ◁ character.iso.hom.app X) ≫
                ε_ X Xᘁ) := by
        simpa [Category.assoc] using
          congrArg
            (fun f => (Xᘁ ◁ character.iso.inv.app X) ≫ f)
            expandedNaturality.symm
      _ = (Xᘁ ◁ character.iso.inv.app X) ≫
            (character.iso.hom.app Xᘁ ▷ X) ≫
            (Xᘁ ◁ character.iso.hom.app X) ≫
            ε_ X Xᘁ := by
        simp only [Category.assoc]
      _ = (character.iso.hom.app Xᘁ ▷ X) ≫
            (Xᘁ ◁ character.iso.inv.app X) ≫
            (Xᘁ ◁ character.iso.hom.app X) ≫
            ε_ X Xᘁ := by
        simpa [Category.assoc] using
          congrArg
            (fun f => f ≫
              (Xᘁ ◁ character.iso.hom.app X) ≫
                ε_ X Xᘁ)
            (whisker_exchange
              (character.iso.hom.app Xᘁ)
              (character.iso.inv.app X))
      _ = (character.iso.hom.app Xᘁ ▷ X) ≫
            (Xᘁ ◁
              (character.iso.inv.app X ≫
                character.iso.hom.app X)) ≫
            ε_ X Xᘁ := by
        simpa [Category.assoc] using
          congrArg
            (fun f =>
              (character.iso.hom.app Xᘁ ▷ X) ≫
                f ≫ ε_ X Xᘁ)
            (MonoidalCategory.whiskerLeft_comp Xᘁ
              (character.iso.inv.app X)
              (character.iso.hom.app X)).symm
      _ = (character.iso.hom.app Xᘁ ▷ X) ≫
            ε_ X Xᘁ := by
        have cancelWhisker :
            Xᘁ ◁
                (character.iso.inv.app X ≫
                  character.iso.hom.app X) =
              𝟙 (Xᘁ ⊗ X) := by
          rw [character.iso.inv_hom_id_app]
          simp
        simpa [Category.assoc] using
          congrArg
            (fun f =>
              (character.iso.hom.app Xᘁ ▷ X) ≫
                f ≫ ε_ X Xᘁ)
            cancelWhisker
  let inverseMate : Xᘁ ⟶ Xᘁ :=
    rightAdjointMate (character.iso.inv.app X)
  have mateEvaluation :
      (inverseMate ▷ X) ≫ ε_ X Xᘁ =
        (Xᘁ ◁ character.iso.inv.app X) ≫ ε_ X Xᘁ :=
    rightAdjointMate_comp_evaluation (character.iso.inv.app X)
  have comparison :
      (character.iso.hom.app Xᘁ ▷ X) ≫ ε_ X Xᘁ =
        (inverseMate ▷ X) ≫ ε_ X Xᘁ :=
    dualEvaluation.trans mateEvaluation.symm
  let e := tensorRightHomEquiv Xᘁ X Xᘁ (𝟙_ 𝒞.C)
  have composed :
      character.iso.hom.app Xᘁ ≫ (λ_ Xᘁ).inv =
        inverseMate ≫ (λ_ Xᘁ).inv := by
    have leftRule :
        e ((character.iso.hom.app Xᘁ ▷ X) ≫ ε_ X Xᘁ) =
          character.iso.hom.app Xᘁ ≫ (λ_ Xᘁ).inv :=
      tensorRightHomEquiv_whiskerRight_comp_evaluation
        (character.iso.hom.app Xᘁ)
    have rightRule :
        e ((inverseMate ▷ X) ≫ ε_ X Xᘁ) =
          inverseMate ≫ (λ_ Xᘁ).inv :=
      tensorRightHomEquiv_whiskerRight_comp_evaluation
        inverseMate
    exact leftRule.symm.trans ((congrArg e comparison).trans rightRule)
  exact (cancel_mono (λ_ Xᘁ).inv).mp composed

/-- Right adjoint mates preserve scalar multiples of an identity. -/
theorem rightAdjointMate_smul_identity
    (scalar : K)
    (X : 𝒞.C) :
    (scalar • 𝟙 X)ᘁ = scalar • 𝟙 (Xᘁ) := by
  simp [rightAdjointMate]

/--
The scalar by which the character acts on a simple object.  This is derived
from the actual natural-automorphism component through Schur's lemma; it is
not separately supplied data.
-/
noncomputable def simpleScalar
    (character : TensorIdentityCharacter 𝒞)
    (s : 𝒞.simples.Simple) : K := by
  letI : CategoryTheory.Simple (𝒞.simples.simpleObject s) :=
    𝒞.simples.simple_isSimple s
  exact
    (𝒞.simpleEndLinearEquiv (𝒞.simples.simpleObject s)).symm
      (character.iso.hom.app (𝒞.simples.simpleObject s))

theorem component_on_simple_eq_scalar_smul_identity
    (character : TensorIdentityCharacter 𝒞)
    (s : 𝒞.simples.Simple) :
    character.iso.hom.app (𝒞.simples.simpleObject s) =
      character.simpleScalar s • 𝟙 (𝒞.simples.simpleObject s) := by
  letI : CategoryTheory.Simple (𝒞.simples.simpleObject s) :=
    𝒞.simples.simple_isSimple s
  exact
    (𝒞.simpleEndLinearEquiv (𝒞.simples.simpleObject s)).apply_symm_apply
      (character.iso.hom.app (𝒞.simples.simpleObject s)) |>.symm

theorem simpleScalar_ne_zero
    (character : TensorIdentityCharacter 𝒞)
    (s : 𝒞.simples.Simple) :
    character.simpleScalar s ≠ 0 := by
  letI : CategoryTheory.Simple (𝒞.simples.simpleObject s) :=
    𝒞.simples.simple_isSimple s
  intro scalar_zero
  have component_zero :
      character.iso.hom.app (𝒞.simples.simpleObject s) = 0 := by
    rw [character.component_on_simple_eq_scalar_smul_identity s, scalar_zero,
      zero_smul]
    rfl
  have identity_zero :
      𝟙 (𝒞.simples.simpleObject s) = 0 := by
    calc
      𝟙 (𝒞.simples.simpleObject s) =
          character.iso.inv.app (𝒞.simples.simpleObject s) ≫
            character.iso.hom.app (𝒞.simples.simpleObject s) :=
        (character.iso.inv_hom_id_app
          (𝒞.simples.simpleObject s)).symm
      _ =
          character.iso.inv.app (𝒞.simples.simpleObject s) ≫ 0 := by
        rw [component_zero]
      _ = 0 := CategoryTheory.Limits.comp_zero
  exact
    CategoryTheory.id_nonzero (𝒞.simples.simpleObject s) identity_zero

/-- The derived nonzero simple scalar, packaged as a unit of `K`. -/
noncomputable def value
    (character : TensorIdentityCharacter 𝒞)
    (s : 𝒞.simples.Simple) : Kˣ :=
  Units.mk0 (character.simpleScalar s) (character.simpleScalar_ne_zero s)

@[simp]
theorem value_val
    (character : TensorIdentityCharacter 𝒞)
    (s : 𝒞.simples.Simple) :
    (character.value s : K) = character.simpleScalar s :=
  rfl

theorem component_on_simple_eq_value_smul_identity
    (character : TensorIdentityCharacter 𝒞)
    (s : 𝒞.simples.Simple) :
    character.iso.hom.app (𝒞.simples.simpleObject s) =
      (character.value s : K) • 𝟙 (𝒞.simples.simpleObject s) :=
  character.component_on_simple_eq_scalar_smul_identity s

end TensorIdentityCharacter

/-- A premodular category together with its twisting automorphism. -/
structure TwistedPremodularCategory
    (K : Type uK) [Field K] [IsAlgClosed K] [CharZero K] where
  category : PremodularFusionCategory.{uK, uC, v, uS} K
  character : TensorIdentityCharacter.{uK, uC, v, uS} category

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 5768
