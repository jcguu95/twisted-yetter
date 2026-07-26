import TwistedYetter.Kirby.HandleChainGeneratorReduction
import TwistedYetter.Kirby.RoleAwareCharacterCouponBridge
import TwistedYetter.Kirby.RoleAwarePremodularEvaluator
import TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation

/-!
# Representative independence of the role-aware premodular evaluator

This file proves that the special-cut evaluator depends only on the
handle-chain `H₂` class.  The proof is source-bound: every degree-three
generator is tied to one actual dotted-cut window in the evaluator diagram.
-/

namespace TwistedYetter.Kirby.RoleAwareRepresentativeIndependence

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.ComponentBoundaryCharacter
open TwistedYetter.Kirby.ComponentBoundarySignedProduct
open TwistedYetter.Kirby.ComponentDottedEncircling
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.DottedBoundaryGeometry
open TwistedYetter.Kirby.HandleChainGeneratorReduction
open TwistedYetter.Kirby.LinearDiagram
open TwistedYetter.Kirby.RoleAwareCharacterCouponBridge
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator.CanonicalPresentation
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

namespace GeneratorGeometry

/-- Resolve a puncture ID in the ordinary-component registry. -/
def ordinaryIndexOf
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (componentId : String) :
    Option (OrdinaryComponentIndex presentation) :=
  match presentation.componentIndexing.indexOf componentId with
  | none => none
  | some index =>
      if dotted :
          (presentation.topology.formal.raw.components.get index).role =
            .dotted then
        none
      else
        some ⟨index, dotted⟩

@[simp]
theorem ordinaryIndexOf_roundtrip
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (index : OrdinaryComponentIndex presentation) :
    ordinaryIndexOf geometry
        (presentation.topology.formal.raw.components.get
          index.1).componentId =
      some index := by
  rcases index with ⟨rawIndex, ordinary⟩
  unfold ordinaryIndexOf
  split
  · rename_i lookupNone
    rw [presentation.componentIndexing.index_roundtrip rawIndex] at lookupNone
    contradiction
  · rename_i selected lookupSome
    have selectedEq : selected = rawIndex := by
      apply Option.some.inj
      rw [← lookupSome,
        presentation.componentIndexing.index_roundtrip rawIndex]
    subst selected
    split
    · rename_i dotted
      exact (ordinary dotted).elim
    · rfl

theorem ordinaryIndexOf_sound
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (componentId : String)
    (index : OrdinaryComponentIndex presentation)
    (resolved : ordinaryIndexOf geometry componentId = some index) :
    componentId =
      (presentation.topology.formal.raw.components.get
        index.1).componentId := by
  unfold ordinaryIndexOf at resolved
  split at resolved
  · contradiction
  · rename_i rawIndex rawResolved
    split at resolved
    · contradiction
    · have subtypeEq : (⟨rawIndex, by assumption⟩ :
          OrdinaryComponentIndex presentation) = index :=
        Option.some.inj resolved
      have rawIndexEq : rawIndex = index.1 :=
        congrArg Subtype.val subtypeEq
      subst rawIndex
      exact presentation.componentIndexing.index_sound
        componentId index.1 rawResolved

theorem puncture_ids_ordinary_indexed
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (componentId : String)
    (membership : componentId ∈ geometry.punctureBoundary.componentIds) :
    ∃ index, ordinaryIndexOf geometry componentId = some index := by
  obtain ⟨twoHandle, indexed⟩ :=
    geometry.puncture_ids_are_two_handles componentId membership
  obtain ⟨rawIndex, rawIndexed⟩ :=
    geometry.puncture_ids_indexed_in_component_registry componentId membership
  have componentIdEq :=
    presentation.topology.two_handle_index_sound
      componentId twoHandle indexed
  have rawIdEq :=
    presentation.componentIndexing.index_sound
      componentId rawIndex rawIndexed
  have ordinary :
      (presentation.topology.formal.raw.components.get rawIndex).role ≠
        .dotted := by
    intro dotted
    have unindexed :=
      presentation.topology.dotted_component_unindexed
        (presentation.topology.formal.raw.components.get rawIndex) dotted
    rw [← rawIdEq, indexed] at unindexed
    contradiction
  refine ⟨⟨rawIndex, ordinary⟩, ?_⟩
  unfold ordinaryIndexOf
  split
  · rename_i lookupNone
    rw [rawIndexed] at lookupNone
    contradiction
  · rename_i selected lookupSome
    have selectedEq : selected = rawIndex := by
      apply Option.some.inj
      rw [← lookupSome, rawIndexed]
    subst selected
    split
    · rename_i dotted
      exact (ordinary dotted).elim
    · rfl

/-- The puncture character is a product over exactly the ordinary registry. -/
theorem boundaryCharacterPower_eq_ordinaryProduct
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (labeling : OrdinaryLabeling (S := S) presentation)
    (coefficient : ℤ) :
    boundaryCharacterPower 𝒞.toFusionCategoryData η
        (roleAwareLabelOf 𝒞 presentation labeling)
        geometry.punctureBoundary coefficient =
      ↑(∏ index : OrdinaryComponentIndex presentation,
        (𝒞.toFusionCategoryData.automorphismSimpleUnit
          η (labeling index)) ^
          (signedMultiplicity
              (presentation.topology.formal.raw.components.get
                index.1).componentId
              geometry.punctureBoundary * coefficient) : Kˣ) := by
  rw [boundaryCharacterPower_eq_signedProduct]
  rw [signedProduct_eq_indexedProduct
    (value := fun componentId =>
      𝒞.toFusionCategoryData.automorphismSimpleUnit
        η (roleAwareLabelOf 𝒞 presentation labeling componentId))
    (coefficient := coefficient)
    (indexOf := ordinaryIndexOf geometry)
    (idOf := fun index =>
      (presentation.topology.formal.raw.components.get index.1).componentId)
    (roundtrip := ordinaryIndexOf_roundtrip geometry)
    (sound := ordinaryIndexOf_sound geometry)
    (boundary := geometry.punctureBoundary)
    (allIndexed := puncture_ids_ordinary_indexed geometry)]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  rw [roleAwareLabelOf_ordinary]

/-- Ordinary Kirby-colour weights acquire exactly the puncture character. -/
theorem roleAwareGlobalWeight_add_integralGenerator
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (cycle : presentation.DegreeTwoCycle)
    (coefficient : ℤ)
    (labeling : OrdinaryLabeling (S := S) presentation) :
    roleAwareGlobalWeight 𝒞 η presentation
        (addBoundary presentation.topology.handleChain cycle
          (coordinateChain presentation.topology.handleChain
            generator coefficient)) labeling =
      boundaryCharacterPower 𝒞.toFusionCategoryData η
          (roleAwareLabelOf 𝒞 presentation labeling)
          geometry.punctureBoundary coefficient *
        roleAwareGlobalWeight 𝒞 η presentation cycle labeling := by
  classical
  rw [boundaryCharacterPower_eq_ordinaryProduct
    𝒞 η presentation geometry labeling coefficient]
  unfold roleAwareGlobalWeight
  rw [show
      (∏ index : OrdinaryComponentIndex presentation,
        presentation.cycleComponentWeight 𝒞 η
          (addBoundary presentation.topology.handleChain cycle
            (coordinateChain presentation.topology.handleChain
              generator coefficient))
          (presentation.topology.formal.raw.components.get index.1)
          (labeling index)) =
        ∏ index : OrdinaryComponentIndex presentation,
          𝒞.toFusionCategoryData.automorphismScalarPower
              η (labeling index)
              (signedMultiplicity
                (presentation.topology.formal.raw.components.get
                  index.1).componentId
                geometry.punctureBoundary * coefficient) *
            presentation.cycleComponentWeight 𝒞 η cycle
              (presentation.topology.formal.raw.components.get index.1)
              (labeling index) by
    apply Finset.prod_congr rfl
    intro index _
    unfold CanonicalPresentation.cycleComponentWeight
    rw [geometry.cycleComponentExponent_add_integralGenerator]
    rw [FusionCategoryData.automorphismScalarPower_add]
    ring]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [FusionCategoryData.automorphismScalarPower]
  simp

end GeneratorGeometry

namespace Presentation

/-- One integral degree-three generator does not change one weighted term. -/
theorem weightedTerm_add_integralGenerator
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : Presentation H2)
    (cycle : presentation.canonicalPresentation.DegreeTwoCycle)
    (generator :
      Fin presentation.canonicalPresentation.topology.counts.turnedOver.h3)
    (coefficient : ℤ)
    (labeling :
      OrdinaryLabeling (S := S) presentation.canonicalPresentation) :
    roleAwareGlobalWeight 𝒞 η presentation.canonicalPresentation
        (addBoundary presentation.canonicalPresentation.topology.handleChain cycle
          (coordinateChain
            presentation.canonicalPresentation.topology.handleChain
            generator coefficient)) labeling •
      Diagram.eval C
        (roleAwareTermDiagram 𝒞 η presentation.canonicalPresentation
          presentation.simultaneousGeometry labeling) =
      roleAwareGlobalWeight 𝒞 η presentation.canonicalPresentation
          cycle labeling •
        Diagram.eval C
          (roleAwareTermDiagram 𝒞 η presentation.canonicalPresentation
            presentation.simultaneousGeometry labeling) := by
  let geometry := presentation.dottedGeometry.geometry generator
  let window := presentation.generatorCutWindow generator
  let labelOf :=
    roleAwareLabelOf 𝒞 presentation.canonicalPresentation labeling
  have termFactorization :
      roleAwareTermDiagram 𝒞 η presentation.canonicalPresentation
          presentation.simultaneousGeometry labeling =
        (window.context.plug
          (.specialDottedCut geometry.dottedComponent.componentId
            geometry.punctureBoundary)).interpret 𝒞 η labelOf := by
    unfold roleAwareTermDiagram
    rw [window.factorization]
  rw [GeneratorGeometry.roleAwareGlobalWeight_add_integralGenerator
    𝒞 η presentation.canonicalPresentation geometry cycle coefficient labeling]
  rw [termFactorization]
  let boundaryPower :=
    boundaryCharacterPower 𝒞.toFusionCategoryData η labelOf
      geometry.punctureBoundary coefficient
  let originalWeight :=
    roleAwareGlobalWeight 𝒞 η presentation.canonicalPresentation cycle labeling
  let termEvaluation :=
    Diagram.eval C
      ((window.context.plug
        (.specialDottedCut geometry.dottedComponent.componentId
          geometry.punctureBoundary)).interpret 𝒞 η labelOf)
  have absorbed : boundaryPower • termEvaluation = termEvaluation := by
    calc
      _ = Diagram.eval C
          ((window.context.plug
            (.comp
              (.characterPower geometry.punctureBoundary coefficient)
              (.specialDottedCut geometry.dottedComponent.componentId
                geometry.punctureBoundary))).interpret 𝒞 η labelOf) := by
        exact
          scalar_smul_specialCut_eval_eq_characterCouponCut_eval_inContext
            𝒞 η labelOf geometry.dottedComponent.componentId
            geometry.punctureBoundary coefficient window.context
      _ = _ :=
        characterCouponCut_eval_eq_specialCut_eval_inContext
          𝒞 η labelOf geometry.dottedComponent.componentId
          geometry.punctureBoundary coefficient window.context
  change (boundaryPower * originalWeight) • termEvaluation =
    originalWeight • termEvaluation
  calc
    _ = originalWeight • (boundaryPower • termEvaluation) := by
      rw [smul_smul]
      congr 1
      ring
    _ = _ := by rw [absorbed]

/-- The complete role-aware finite sum is generator-boundary invariant. -/
theorem roleAwareCycleEval_add_integralGenerator
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : Presentation H2)
    (cycle : presentation.canonicalPresentation.DegreeTwoCycle)
    (generator :
      Fin presentation.canonicalPresentation.topology.counts.turnedOver.h3)
    (coefficient : ℤ) :
    roleAwareCycleEval 𝒞 η presentation.canonicalPresentation
        presentation.simultaneousGeometry
        (addBoundary presentation.canonicalPresentation.topology.handleChain cycle
          (coordinateChain
            presentation.canonicalPresentation.topology.handleChain
            generator coefficient)) =
      roleAwareCycleEval 𝒞 η presentation.canonicalPresentation
        presentation.simultaneousGeometry cycle := by
  classical
  unfold roleAwareCycleEval roleAwareEvaluationState
  unfold KirbyCancellation.EvaluationState.normalized
  congr 1
  unfold roleAwareRawNumerator roleAwareLinearDiagram
  apply congrArg 𝒞.toFusionCategoryData.closedScalar
  simp only [LinearDiagram.eval_weightedSum]
  apply Finset.sum_congr rfl
  intro labeling _
  exact weightedTerm_add_integralGenerator
    𝒞 η presentation cycle generator coefficient labeling

/-- The role-aware evaluator depends only on the handle-chain `H₂` class. -/
theorem roleAwareCycleEval_respects_homology_class
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : Presentation H2)
    (left right : presentation.canonicalPresentation.DegreeTwoCycle)
    (sameClass :
      presentation.canonicalPresentation.topology.handleChain.complex.homologyπ
          2 left =
        presentation.canonicalPresentation.topology.handleChain.complex.homologyπ
          2 right) :
    roleAwareCycleEval 𝒞 η presentation.canonicalPresentation
        presentation.simultaneousGeometry left =
      roleAwareCycleEval 𝒞 η presentation.canonicalPresentation
        presentation.simultaneousGeometry right := by
  apply HandleChainGeneratorReduction.respects_homology_class
    presentation.canonicalPresentation.topology.handleChain
    (roleAwareCycleEval 𝒞 η presentation.canonicalPresentation
      presentation.simultaneousGeometry)
  intro cycle generator coefficient
  exact roleAwareCycleEval_add_integralGenerator
    𝒞 η presentation cycle generator coefficient
  exact sameClass

end Presentation

end TwistedYetter.Kirby.RoleAwareRepresentativeIndependence
