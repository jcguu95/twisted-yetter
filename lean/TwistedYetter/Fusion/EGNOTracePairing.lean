import Mathlib.LinearAlgebra.Dual.Lemmas
import TwistedYetter.Fusion.EGNOFusionCategory
import TwistedYetter.Fusion.FiniteResolution
import TwistedYetter.Fusion.FrobeniusLinear
import TwistedYetter.Fusion.PairingTransport

/-!
# Nondegenerate spherical trace pairings

Bärenz--Barrett Definition 2.8 and Lemma 2.9 first identify the
composition pairing through a simple object and prove that it is
nondegenerate in a semisimple category.  Definition 2.20 and Lemma 2.21
then apply this to the spherical trace pairing.

This file follows an equivalent cup--cap route.  The finite semisimple
decomposition from `FusionCategoryData` proves that composition through any
simple object is a perfect pairing.  Frobenius reciprocity bends
`Hom(X,Y)` and `Hom(Y,X)` into a cup and a cap through the simple tensor
unit.  Their composite is exactly the pivotal trace, so the trace pairing is
perfect without adding nondegeneracy as a field.
-/

namespace TwistedYetter.Fusion.EGNO

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.FiniteResolution
open TwistedYetter.Fusion.FrobeniusLinear

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

namespace PerfectPairing

universe uV uW uV' uW'

variable {V : Type uV} {W : Type uW}
variable {V' : Type uV'} {W' : Type uW'}
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid W] [Module K W]
variable [AddCommMonoid V'] [Module K V']
variable [AddCommMonoid W'] [Module K W']

/--
Transport a perfect pairing along explicit linear equivalences on both
spaces.  The equivalences convert the new coordinates into the old ones.
-/
noncomputable def transportAlong
    (pairing : PerfectPairing K V W)
    (primalEquiv : V' ≃ₗ[K] V)
    (dualEquiv : W' ≃ₗ[K] W) :
    PerfectPairing K V' W' where
  toDual :=
    dualEquiv.trans
      (pairing.toDual.trans primalEquiv.dualMap)

omit [IsAlgClosed K] in
/-- Transport evaluates the old pairing on the transported vectors. -/
theorem transportAlong_pair
    (pairing : PerfectPairing K V W)
    (primalEquiv : V' ≃ₗ[K] V)
    (dualEquiv : W' ≃ₗ[K] W)
    (primal : V') (dual : W') :
    (transportAlong pairing primalEquiv dualEquiv).pair primal dual =
      pairing.pair (primalEquiv primal) (dualEquiv dual) :=
  rfl

end PerfectPairing

namespace FusionCategoryData

variable (data : FusionCategoryData (K := K) (C := C) (S := S))

/-- Scalarization of an endomorphism of an arbitrary simple object. -/
noncomputable def simpleScalar
    (Z : C) [Simple Z]
    (f : Z ⟶ Z) : K :=
  (data.simpleEndLinearEquiv Z).symm f

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- A simple endomorphism has zero scalar exactly when it is zero. -/
theorem simpleScalar_eq_zero_iff
    (Z : C) [Simple Z]
    (f : Z ⟶ Z) :
    data.simpleScalar Z f = 0 ↔ f = 0 := by
  change (data.simpleEndLinearEquiv Z).symm f = 0 ↔ f = 0
  exact LinearEquiv.map_eq_zero_iff _

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- The identity of a simple object scalarizes to `1`. -/
theorem simpleScalar_identity
    (Z : C) [Simple Z] :
    data.simpleScalar Z (𝟙 Z) = 1 := by
  apply (data.simpleEndLinearEquiv Z).injective
  simp [simpleScalar, simpleEndLinearEquiv, scalarEndLinearMap]

/--
The composition pairing as a linear map from the reverse Hom space into the
dual of the forward Hom space.
-/
noncomputable def simpleCompositionToDual
    (Z X : C) [Simple Z] :
    (X ⟶ Z) →ₗ[K] Module.Dual K (Z ⟶ X) where
  toFun g :=
    { toFun := fun f => data.simpleScalar Z (f ≫ g)
      map_add' := by
        intro f₁ f₂
        simp [simpleScalar]
      map_smul' := by
        intro scalar f
        simp [simpleScalar] }
  map_add' := by
    intro g₁ g₂
    ext f
    simp [simpleScalar]
  map_smul' := by
    intro scalar g
    ext f
    simp [simpleScalar]

/--
The same composition pairing with the two Hom spaces interchanged.

It is used only to prove that the two finite-dimensional Hom spaces have the
same dimension; the formal perfect pairing keeps the conventional order.
-/
noncomputable def simpleCompositionToDualFlip
    (Z X : C) [Simple Z] :
    (Z ⟶ X) →ₗ[K] Module.Dual K (X ⟶ Z) where
  toFun f :=
    { toFun := fun g => data.simpleScalar Z (f ≫ g)
      map_add' := by
        intro g₁ g₂
        simp [simpleScalar]
      map_smul' := by
        intro scalar g
        simp [simpleScalar] }
  map_add' := by
    intro f₁ f₂
    ext g
    simp [simpleScalar]
  map_smul' := by
    intro scalar f
    ext g
    simp [simpleScalar]

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/--
If every composition `Z -> X -> Z` vanishes, then the second morphism
vanishes.  This is the first half of Bärenz--Barrett Lemma 2.9.
-/
theorem simpleComposition_right_separating
    (Z X : C) [Simple Z]
    (g : X ⟶ Z)
    (vanishes :
      ∀ f : Z ⟶ X, data.simpleScalar Z (f ≫ g) = 0) :
    g = 0 := by
  have composition_zero :
      ∀ f : Z ⟶ X, f ≫ g = 0 := by
    intro f
    exact (data.simpleScalar_eq_zero_iff Z (f ≫ g)).mp (vanishes f)
  have summand_zero :
      ∀ p : data.SummandIndex X, data.inclusion X p ≫ g = 0 := by
    intro p
    letI : Simple (data.summand X p) :=
      data.simple_isSimple p.1
    by_contra nonzero
    letI : IsIso (data.inclusion X p ≫ g) :=
      (isIso_iff_nonzero (data.inclusion X p ≫ g)).mpr nonzero
    have contradiction :=
      composition_zero
        (inv (data.inclusion X p ≫ g) ≫ data.inclusion X p)
    have identity_zero : 𝟙 Z = 0 := by
      rw [Category.assoc, IsIso.inv_hom_id] at contradiction
      exact contradiction
    exact CategoryTheory.id_nonzero Z identity_zero
  calc
    g = 𝟙 X ≫ g := by simp
    _ =
        (∑ p : data.SummandIndex X,
          data.projection X p ≫ data.inclusion X p) ≫ g := by
          rw [data.sum_projection_inclusion X]
    _ =
        ∑ p : data.SummandIndex X,
          data.projection X p ≫ data.inclusion X p ≫ g := by
          rw [Preadditive.sum_comp]
          simp only [Category.assoc]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro p _
          simp [summand_zero p]

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/--
If every composition `Z -> X -> Z` vanishes, then the first morphism
vanishes.  This is the second half of Bärenz--Barrett Lemma 2.9.
-/
theorem simpleComposition_left_separating
    (Z X : C) [Simple Z]
    (f : Z ⟶ X)
    (vanishes :
      ∀ g : X ⟶ Z, data.simpleScalar Z (f ≫ g) = 0) :
    f = 0 := by
  have composition_zero :
      ∀ g : X ⟶ Z, f ≫ g = 0 := by
    intro g
    exact (data.simpleScalar_eq_zero_iff Z (f ≫ g)).mp (vanishes g)
  have summand_zero :
      ∀ p : data.SummandIndex X, f ≫ data.projection X p = 0 := by
    intro p
    letI : Simple (data.summand X p) :=
      data.simple_isSimple p.1
    by_contra nonzero
    letI : IsIso (f ≫ data.projection X p) :=
      (isIso_iff_nonzero (f ≫ data.projection X p)).mpr nonzero
    have contradiction :=
      composition_zero
        (data.projection X p ≫ inv (f ≫ data.projection X p))
    have identity_zero : 𝟙 Z = 0 := by
      rw [← Category.assoc, IsIso.hom_inv_id] at contradiction
      exact contradiction
    exact CategoryTheory.id_nonzero Z identity_zero
  calc
    f = f ≫ 𝟙 X := by simp
    _ =
        f ≫
          (∑ p : data.SummandIndex X,
            data.projection X p ≫ data.inclusion X p) := by
          rw [data.sum_projection_inclusion X]
    _ =
        ∑ p : data.SummandIndex X,
          f ≫ data.projection X p ≫ data.inclusion X p := by
          rw [Preadditive.comp_sum]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro p _
          simp [← Category.assoc, summand_zero p]

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- The reverse-to-dual composition map is injective. -/
theorem simpleCompositionToDual_injective
    (Z X : C) [Simple Z] :
    Function.Injective (data.simpleCompositionToDual Z X) := by
  intro g₁ g₂ equality
  apply sub_eq_zero.mp
  apply data.simpleComposition_right_separating Z X (g₁ - g₂)
  intro f
  have mapped_zero :
      data.simpleCompositionToDual Z X (g₁ - g₂) = 0 := by
    rw [map_sub, equality, sub_self]
  exact LinearMap.congr_fun mapped_zero f

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- The forward-to-dual composition map is injective. -/
theorem simpleCompositionToDualFlip_injective
    (Z X : C) [Simple Z] :
    Function.Injective (data.simpleCompositionToDualFlip Z X) := by
  intro f₁ f₂ equality
  apply sub_eq_zero.mp
  apply data.simpleComposition_left_separating Z X (f₁ - f₂)
  intro g
  have mapped_zero :
      data.simpleCompositionToDualFlip Z X (f₁ - f₂) = 0 := by
    rw [map_sub, equality, sub_self]
  exact LinearMap.congr_fun mapped_zero g

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
include data in
/-- The two Hom spaces in the simple composition pairing have equal dimension. -/
theorem simpleComposition_finrank_eq
    (Z X : C) [Simple Z] :
    Module.finrank K (X ⟶ Z) =
      Module.finrank K (Z ⟶ X) := by
  letI : FiniteDimensional K (X ⟶ Z) := data.hom_finite X Z
  letI : FiniteDimensional K (Z ⟶ X) := data.hom_finite Z X
  have right_le :
      Module.finrank K (X ⟶ Z) ≤
        Module.finrank K (Module.Dual K (Z ⟶ X)) :=
    (data.simpleCompositionToDual Z X).finrank_le_finrank_of_injective
      (data.simpleCompositionToDual_injective Z X)
  have left_le :
      Module.finrank K (Z ⟶ X) ≤
        Module.finrank K (Module.Dual K (X ⟶ Z)) :=
    (data.simpleCompositionToDualFlip Z X).finrank_le_finrank_of_injective
      (data.simpleCompositionToDualFlip_injective Z X)
  rw [Subspace.dual_finrank_eq] at right_le left_le
  exact Nat.le_antisymm right_le left_le

omit [MonoidalPreadditive C] [MonoidalLinear K C] in
include data in
/--
Composition through a simple object is a perfect pairing.

This is Bärenz--Barrett Lemma 2.9, derived from the stored semisimple
decomposition rather than assumed.
-/
noncomputable def simpleCompositionPerfectPairing
    (Z X : C) [Simple Z] :
    PerfectPairing K (Z ⟶ X) (X ⟶ Z) where
  toDual := by
    letI : FiniteDimensional K (X ⟶ Z) := data.hom_finite X Z
    letI : FiniteDimensional K (Z ⟶ X) := data.hom_finite Z X
    exact
      (data.simpleCompositionToDual Z X).linearEquivOfInjective
        (data.simpleCompositionToDual_injective Z X)
        (by
        rw [Subspace.dual_finrank_eq]
        exact data.simpleComposition_finrank_eq Z X)

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- The perfect pairing evaluates by scalarizing composition. -/
theorem simpleCompositionPerfectPairing_pair
    (Z X : C) [Simple Z]
    (f : Z ⟶ X) (g : X ⟶ Z) :
    (data.simpleCompositionPerfectPairing Z X).pair f g =
      data.simpleScalar Z (f ≫ g) :=
  rfl

/-- Composition through the simple tensor unit is a perfect pairing. -/
noncomputable def unitCompositionPerfectPairing
    (X : C) :
    PerfectPairing K (𝟙_ C ⟶ X) (X ⟶ 𝟙_ C) := by
  letI : Simple (𝟙_ C) := data.unit_isSimple
  exact data.simpleCompositionPerfectPairing (𝟙_ C) X

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- The unit composition pairing is the derived closed scalar evaluator. -/
theorem unitCompositionPerfectPairing_pair
    (X : C)
    (f : 𝟙_ C ⟶ X) (g : X ⟶ 𝟙_ C) :
    (data.unitCompositionPerfectPairing X).pair f g =
      data.closedScalar (f ≫ g) :=
  rfl

end FusionCategoryData

section PivotalBending

/--
Bend the source of `f : X -> Y` into the selected right-dual cup:
`Hom(X,Y) ≃ Hom(1,Y tensor X*)`.
-/
noncomputable def rightDualCupLinearEquiv
    (X Y : C) :
    (X ⟶ Y) ≃ₗ[K] (𝟙_ C ⟶ Y ⊗ (Xᘁ)) :=
  (CategoryTheory.Linear.homCongr K
      (λ_ X).symm (Iso.refl Y)).trans
    (tensorRightHomLinearEquiv
      (R := K) (𝟙_ C) X (Xᘁ) Y)

omit [IsAlgClosed K] in
/-- The cup equivalence is coevaluation followed by the coupon. -/
theorem rightDualCupLinearEquiv_apply
    (X Y : C) (f : X ⟶ Y) :
    rightDualCupLinearEquiv (K := K) X Y f =
      η_ X (Xᘁ) ≫ (f ⊗ₘ 𝟙 (Xᘁ)) := by
  dsimp [rightDualCupLinearEquiv,
    tensorRightHomLinearEquiv, tensorRightHomEquiv,
    CategoryTheory.Linear.homCongr]
  monoidal

/--
Bend `g : Y -> X` into the matching pivotal cap:
`Hom(Y,X) ≃ Hom(Y tensor X*,1)`.
-/
noncomputable def pivotalCapLinearEquiv
    (pivotal : PivotalStructure C)
    (X Y : C) :
    (Y ⟶ X) ≃ₗ[K] (Y ⊗ (Xᘁ) ⟶ 𝟙_ C) :=
  (CategoryTheory.Linear.homCongr K
      (Iso.refl Y)
      ((pivotal.iso.app X) ≪≫ (λ_ ((Xᘁ)ᘁ)).symm)).trans
    (tensorRightHomLinearEquiv
      (R := K) Y (Xᘁ) ((Xᘁ)ᘁ) (𝟙_ C)).symm

omit [IsAlgClosed K] in
/-- The cap equivalence is the coupon, pivotal map, and evaluation. -/
theorem pivotalCapLinearEquiv_apply
    (pivotal : PivotalStructure C)
    (X Y : C) (g : Y ⟶ X) :
    pivotalCapLinearEquiv (K := K) pivotal X Y g =
      ((g ≫ pivotal.iso.hom.app X) ⊗ₘ 𝟙 (Xᘁ)) ≫
        ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
  unfold pivotalCapLinearEquiv
  change
    (tensorRightHomLinearEquiv
      (R := K) Y (Xᘁ) ((Xᘁ)ᘁ) (𝟙_ C)).symm
        (CategoryTheory.Linear.homCongr K
          (Iso.refl Y)
          ((pivotal.iso.app X) ≪≫ (λ_ ((Xᘁ)ᘁ)).symm) g) =
      ((g ≫ pivotal.iso.hom.app X) ⊗ₘ 𝟙 (Xᘁ)) ≫
        ε_ (Xᘁ) ((Xᘁ)ᘁ)
  rw [CategoryTheory.Linear.homCongr_apply]
  simp only [Iso.refl_inv, Category.id_comp, Iso.trans_hom]
  dsimp [
    tensorRightHomLinearEquiv, tensorRightHomEquiv,
    CategoryTheory.Linear.homCongr]
  monoidal

omit [IsAlgClosed K] in
/-- Joining the bent coupon and cap gives exactly the pivotal trace. -/
theorem pivotalCup_comp_cap
    (pivotal : PivotalStructure C)
    (X Y : C) (f : X ⟶ Y) (g : Y ⟶ X) :
    rightDualCupLinearEquiv (K := K) X Y f ≫
        pivotalCapLinearEquiv (K := K) pivotal X Y g =
      pivotalTrace pivotal (f ≫ g) := by
  rw [rightDualCupLinearEquiv_apply, pivotalCapLinearEquiv_apply]
  simp only [pivotalTrace, leftCategoricalTrace]
  monoidal

/--
The selected right dual `X*` becomes a left dual of `X` through the pivotal
isomorphism `X ≅ X**`.  This is the coherent reverse pairing used when a
coupon is bent in the opposite direction.
-/
@[implicit_reducible]
def pivotalReverseExactPairing
    (pivotal : PivotalStructure C)
    (X : C) :
    ExactPairing (Xᘁ) X :=
  @exactPairingCongrRight C _ _
    (Xᘁ) X ((Xᘁ)ᘁ)
    (inferInstance : ExactPairing (Xᘁ) ((Xᘁ)ᘁ))
    (pivotal.iso.app X)

/--
The canonical primal mate using the selected right duals and the pivotal
reverse pairing.
-/
noncomputable def pivotalMateLinearEquiv
    (pivotal : PivotalStructure C)
    (X Y Z : C) :
    (Z ⟶ X ⊗ (Yᘁ)) ≃ₗ[K] (Y ⟶ (Zᘁ) ⊗ X) := by
  letI : ExactPairing (Zᘁ) Z :=
    pivotalReverseExactPairing pivotal Z
  exact mateLinearEquiv (R := K) X Y (Yᘁ) Z (Zᘁ)

/--
The canonical opposite mate.  Its reverse exact pairing is derived from the
same pivotal structure as the primal mate.
-/
noncomputable def pivotalDualMateLinearEquiv
    (pivotal : PivotalStructure C)
    (X Y Z : C) :
    (X ⊗ (Yᘁ) ⟶ Z) ≃ₗ[K] ((Zᘁ) ⊗ X ⟶ Y) := by
  letI : ExactPairing (Yᘁ) Y :=
    pivotalReverseExactPairing pivotal Y
  exact dualMateLinearEquiv (R := K) X Y (Yᘁ) Z (Zᘁ)

end PivotalBending

namespace FusionCategoryData

variable (data : FusionCategoryData (K := K) (C := C) (S := S))

include data in
/--
The nondegenerate pivotal trace pairing on arbitrary objects.

It is obtained by bending both Hom spaces into the perfect unit-composition
pairing.  Nondegeneracy is therefore derived, not a caller-provided field.
-/
noncomputable def pivotalTracePerfectPairing
    (pivotal : PivotalStructure C)
    (X Y : C) :
    PerfectPairing K (X ⟶ Y) (Y ⟶ X) :=
  PerfectPairing.transportAlong
    (data.unitCompositionPerfectPairing (Y ⊗ (Xᘁ)))
    (rightDualCupLinearEquiv (K := K) X Y)
    (pivotalCapLinearEquiv (K := K) pivotal X Y)

omit [DecidableEq S] in
/-- The derived perfect pairing evaluates as the scalar pivotal trace. -/
theorem pivotalTracePerfectPairing_pair
    (pivotal : PivotalStructure C)
    (X Y : C)
    (f : X ⟶ Y) (g : Y ⟶ X) :
    (data.pivotalTracePerfectPairing pivotal X Y).pair f g =
      data.closedScalar (pivotalTrace pivotal (f ≫ g)) := by
  rw [pivotalTracePerfectPairing,
    PerfectPairing.transportAlong_pair,
    unitCompositionPerfectPairing_pair,
    pivotalCup_comp_cap]

end FusionCategoryData

section GlobalTraceCompatibility

/--
The one global spherical mate theorem consumed by the coupon-transport layer.

This is deliberately quantified over every `X`, `Y`, `Z`, and every pair of
morphisms.  It cannot be supplied independently for a convenient basis or one
Kirby diagram.  The statement is the algebraic form of Bärenz--Barrett
Lemma 3.3, equations (3.1.9)--(3.1.11).

The current Lean development records this standard graphical-calculus theorem
as an explicit source-bound input.  It is not claimed to follow merely from
the type `SphericalStructure`, and no theorem below silently manufactures it.
-/
structure SphericalMateTraceLaw
    (spherical : SphericalStructure (C := C)) where
  preserves :
    (X Y Z : C) →
    (f : Z ⟶ X ⊗ (Yᘁ)) →
    (g : X ⊗ (Yᘁ) ⟶ Z) →
      pivotalTrace spherical.toPivotalStructure
          (pivotalMateLinearEquiv
            (K := K) spherical.toPivotalStructure X Y Z f ≫
           pivotalDualMateLinearEquiv
            (K := K) spherical.toPivotalStructure X Y Z g) =
        pivotalTrace spherical.toPivotalStructure (f ≫ g)
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Lemma 3.3, equations (3.1.9)-(3.1.11), journal pages 683-684"

namespace FusionCategoryData

variable (data : FusionCategoryData (K := K) (C := C) (S := S))

/--
The canonical mate maps preserve the derived perfect trace pairings.

All local pairings and both mate maps are constructed from `data` and the
single pivotal structure.  The only theorem input is the global,
all-objects `SphericalMateTraceLaw`.
-/
noncomputable def sphericalMatePairingTransport
    (spherical : SphericalStructure (C := C))
    (law : SphericalMateTraceLaw (K := K) spherical)
    (X Y Z : C) :
    PairingTransport
      (data.pivotalTracePerfectPairing
        spherical.toPivotalStructure Z (X ⊗ (Yᘁ)))
      (data.pivotalTracePerfectPairing
        spherical.toPivotalStructure Y ((Zᘁ) ⊗ X)) where
  primalEquiv :=
    pivotalMateLinearEquiv
      (K := K) spherical.toPivotalStructure X Y Z
  dualEquiv :=
    pivotalDualMateLinearEquiv
      (K := K) spherical.toPivotalStructure X Y Z
  preserves_pairing f g := by
    rw [data.pivotalTracePerfectPairing_pair,
      data.pivotalTracePerfectPairing_pair]
    exact congrArg data.closedScalar (law.preserves X Y Z f g)

end FusionCategoryData

end GlobalTraceCompatibility

end TwistedYetter.Fusion.EGNO
