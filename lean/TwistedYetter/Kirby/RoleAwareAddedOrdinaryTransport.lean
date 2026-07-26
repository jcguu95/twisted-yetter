import TwistedYetter.Kirby.RoleAwarePremodularEvaluator
import TwistedYetter.Kirby.RoleAwareFiniteSumTransport

/-!
# Added ordinary-component transport for the role-aware evaluator

A cancelling 1--2 birth adds two link components but only one ordinary
Kirby-colour coordinate: the meridian two-handle.  This file records that
finite-set fact directly at the role-filtered denominator and derives the
label, weight, and finite-sum transport used by the evaluator.
-/

namespace TwistedYetter.Kirby.RoleAwareAddedOrdinaryTransport

open scoped BigOperators
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [CategoryTheory.Category.{vC} C]
variable [CategoryTheory.Abelian C]
variable [CategoryTheory.Linear K C]
variable [CategoryTheory.MonoidalCategory C]
variable [CategoryTheory.RigidCategory C]
variable [CategoryTheory.BraidedCategory C]
variable [CategoryTheory.MonoidalPreadditive C]
variable [CategoryTheory.MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
Exact denominator change after adding ordinary components.

For a 1--2 birth `addedCount = 1`; the simultaneously added dotted component
does not occur in either side of this equivalence.
-/
structure AddedOrdinaryIndexChange
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (addedCount : Nat) where
  targetDecomposition :
    CanonicalPresentation.OrdinaryComponentIndex target ≃
      Sum
        (CanonicalPresentation.OrdinaryComponentIndex source)
        (Fin addedCount)
  common_component_id_sound :
    (sourceIndex : CanonicalPresentation.OrdinaryComponentIndex source) →
      (componentAt target.topology.formal
        (targetDecomposition.symm (Sum.inl sourceIndex)).1).componentId =
        (componentAt source.topology.formal sourceIndex.1).componentId
  addedComponentId : Fin addedCount → String
  added_component_id_sound :
    (addedIndex : Fin addedCount) →
      (componentAt target.topology.formal
        (targetDecomposition.symm (Sum.inr addedIndex)).1).componentId =
        addedComponentId addedIndex

namespace AddedOrdinaryIndexChange

/-- Split target ordinary labels into retained labels and added labels. -/
def labelingEquiv
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    (change : AddedOrdinaryIndexChange source target addedCount)
    (Label : Type) :
    CanonicalPresentation.OrdinaryLabeling (S := Label) target ≃
      (CanonicalPresentation.OrdinaryLabeling (S := Label) source ×
        (Fin addedCount → Label)) :=
  (Equiv.arrowCongr change.targetDecomposition (Equiv.refl Label)).trans
    (Equiv.sumArrowEquivProdArrow _ _ Label)

@[simp]
theorem labelingEquiv_symm_common
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    (change : AddedOrdinaryIndexChange source target addedCount)
    {Label : Type}
    (sourceLabeling :
      CanonicalPresentation.OrdinaryLabeling (S := Label) source)
    (addedLabeling : Fin addedCount → Label)
    (sourceIndex :
      CanonicalPresentation.OrdinaryComponentIndex source) :
    (change.labelingEquiv Label).symm
        (sourceLabeling, addedLabeling)
        (change.targetDecomposition.symm (Sum.inl sourceIndex)) =
      sourceLabeling sourceIndex := by
  simp [labelingEquiv,
    Equiv.sumArrowEquivProdArrow_symm_apply_inl]

@[simp]
theorem labelingEquiv_symm_added
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    (change : AddedOrdinaryIndexChange source target addedCount)
    {Label : Type}
    (sourceLabeling :
      CanonicalPresentation.OrdinaryLabeling (S := Label) source)
    (addedLabeling : Fin addedCount → Label)
    (addedIndex : Fin addedCount) :
    (change.labelingEquiv Label).symm
        (sourceLabeling, addedLabeling)
        (change.targetDecomposition.symm (Sum.inr addedIndex)) =
      addedLabeling addedIndex := by
  simp [labelingEquiv,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]

/-- Reindex a complete finite sum along the exact ordinary denominator split. -/
theorem sum_split
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    (change : AddedOrdinaryIndexChange source target addedCount)
    {Value : Type*} [AddCommMonoid Value]
    (summand :
      CanonicalPresentation.OrdinaryLabeling (S := S) target → Value) :
    (∑ targetLabeling, summand targetLabeling) =
      ∑ splitLabeling,
        summand ((change.labelingEquiv S).symm splitLabeling) :=
  (Equiv.sum_comp (change.labelingEquiv S).symm summand).symm

/-- A product over target ordinary indices splits into common and added parts. -/
theorem product_split
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    (change : AddedOrdinaryIndexChange source target addedCount)
    {Value : Type*} [CommMonoid Value]
    (weight :
      CanonicalPresentation.OrdinaryComponentIndex target → Value) :
    (∏ targetIndex, weight targetIndex) =
      (∏ sourceIndex,
        weight (change.targetDecomposition.symm (Sum.inl sourceIndex))) *
      ∏ addedIndex,
        weight (change.targetDecomposition.symm (Sum.inr addedIndex)) := by
  rw [← Equiv.prod_comp change.targetDecomposition.symm weight]
  exact Fintype.prod_sum_type _

/-- Exact degree-two exponent change on the role-filtered ordinary indices. -/
structure ExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    (change : AddedOrdinaryIndexChange source target addedCount)
    (sourceCycle : source.DegreeTwoCycle)
    (targetCycle : target.DegreeTwoCycle) where
  common_exponent_sound :
    (sourceIndex : CanonicalPresentation.OrdinaryComponentIndex source) →
      target.cycleComponentExponent targetCycle
          (componentAt target.topology.formal
            (change.targetDecomposition.symm (Sum.inl sourceIndex)).1) =
        source.cycleComponentExponent sourceCycle
          (componentAt source.topology.formal sourceIndex.1)
  addedExponent : Fin addedCount → ℤ
  added_exponent_sound :
    (addedIndex : Fin addedCount) →
      target.cycleComponentExponent targetCycle
          (componentAt target.topology.formal
            (change.targetDecomposition.symm (Sum.inr addedIndex)).1) =
        addedExponent addedIndex

namespace ExponentTransport

/-- Exact scalar coefficient of the newly added ordinary components. -/
noncomputable def localWeight
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    {change : AddedOrdinaryIndexChange source target addedCount}
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    (transport : ExponentTransport change sourceCycle targetCycle)
    (addedLabeling : Fin addedCount → S) : K :=
  ∏ addedIndex,
    𝒞.quantumDimension (addedLabeling addedIndex) *
      𝒞.toFusionCategoryData.automorphismScalarPower
        η (addedLabeling addedIndex)
        (transport.addedExponent addedIndex)

/-- The complete role-aware coefficient product splits without dotted labels. -/
theorem roleAwareGlobalWeight_split
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    {change : AddedOrdinaryIndexChange source target addedCount}
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    (transport : ExponentTransport change sourceCycle targetCycle)
    (sourceLabeling :
      CanonicalPresentation.OrdinaryLabeling (S := S) source)
    (addedLabeling : Fin addedCount → S) :
    CanonicalPresentation.roleAwareGlobalWeight
        𝒞 η target targetCycle
        ((change.labelingEquiv S).symm
          (sourceLabeling, addedLabeling)) =
      CanonicalPresentation.roleAwareGlobalWeight
          𝒞 η source sourceCycle sourceLabeling *
        transport.localWeight 𝒞 η addedLabeling := by
  classical
  unfold CanonicalPresentation.roleAwareGlobalWeight
  rw [change.product_split]
  congr 1
  · apply Finset.prod_congr rfl
    intro sourceIndex _
    unfold CanonicalPresentation.cycleComponentWeight
    rw [change.labelingEquiv_symm_common]
    have exponentSound :=
      transport.common_exponent_sound sourceIndex
    simp only [componentAt] at exponentSound
    rw [exponentSound]
  · unfold localWeight
    apply Finset.prod_congr rfl
    intro addedIndex _
    unfold CanonicalPresentation.cycleComponentWeight
    rw [change.labelingEquiv_symm_added]
    have exponentSound :=
      transport.added_exponent_sound addedIndex
    simp only [componentAt] at exponentSound
    rw [exponentSound]

end ExponentTransport
end AddedOrdinaryIndexChange

end TwistedYetter.Kirby.RoleAwareAddedOrdinaryTransport
