import TwistedYetter.Kirby.DottedBoundaryGeometry

/-!
# The finite dotted-label calculation

This module performs the local calculation left after the topology-side
degree-three boundary has been exposed as one dotted open-meridian window.
All labels outside that window are fixed.  The selected dotted label is then
summed exactly, and the resulting open Kirby operator absorbs every integral
tensor-character power.
-/

namespace TwistedYetter.Kirby.DottedBoundaryGeometry.GeneratorGeometry

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentBoundaryCharacter
open TwistedYetter.Kirby.ComponentDottedEncircling
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LinearContext
open TwistedYetter.Kirby.ModularDottedEncircling
open TwistedYetter.Kirby.SelectedCoordinateFiniteSum

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- The puncture character is independent of the isolated dotted label. -/
theorem boundaryCharacterPower_labelingWithDotted_eq_reference
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (dottedLabel : S)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S)
    (coefficient : ℤ) :
    boundaryCharacterPower
        category.premodular.toFusionCategoryData automorphism
        (presentation.labelOf category.premodular
          (geometry.labelingWithDotted dottedLabel remaining))
        geometry.punctureBoundary coefficient =
      boundaryCharacterPower
        category.premodular.toFusionCategoryData automorphism
        (geometry.referenceLabelOf category presentation remaining)
        geometry.punctureBoundary coefficient := by
  apply boundaryCharacterPower_eq_of_eq_on_componentIds
  exact geometry.labelOf_eq_on_punctures category presentation
    dottedLabel category.premodular.toFusionCategoryData.unitIndex remaining

/-- A boundary-character scalar acts trivially on its open Kirby operator. -/
theorem boundaryCharacterPower_smul_openKirbyEncirclingOperator
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (boundary : ComponentBoundary)
    (coefficient : ℤ) :
    boundaryCharacterPower
        category.premodular.toFusionCategoryData automorphism
        labelOf boundary coefficient •
      openKirbyEncirclingOperator category.premodular
        (boundary.interpret category.premodular labelOf).denote =
      openKirbyEncirclingOperator category.premodular
        (boundary.interpret category.premodular labelOf).denote := by
  have neutral := automorphism_power_openKirbyEncircling_left
    category automorphism
      (boundary.interpret category.premodular labelOf).denote coefficient
  rw [automorphismObjectPower_eq_boundaryCharacterPower_smul_identity
    category.premodular automorphism labelOf boundary coefficient] at neutral
  simpa using neutral

/-- The common boundary character after fixing all non-dotted labels. -/
noncomputable def referenceBoundaryCharacter
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S)
    (coefficient : ℤ) : K :=
  boundaryCharacterPower
    category.premodular.toFusionCategoryData automorphism
    (geometry.referenceLabelOf category presentation remaining)
    geometry.punctureBoundary coefficient

/-- One simple-labelled open-meridian evaluation in the fixed boundary type. -/
noncomputable def referenceOpenEvaluation
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S)
    (dottedLabel : S) :=
  Diagram.eval C
    (source := .atom
      (geometry.punctureBoundary.interpret category.premodular
        (geometry.referenceLabelOf category presentation remaining)).denote)
    (target := .atom
      (geometry.punctureBoundary.interpret category.premodular
        (geometry.referenceLabelOf category presentation remaining)).denote)
    (openEncirclingDiagram category.premodular dottedLabel
      (geometry.punctureBoundary.interpret category.premodular
        (geometry.referenceLabelOf category presentation remaining)).denote)

/-- Closed evaluation of the factorized term at one dotted label. -/
noncomputable def factorizedEvaluation
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S)
    (dottedLabel : S) : (𝟙_ C ⟶ 𝟙_ C) :=
  Diagram.eval C
    ((geometry.exteriorContext.plug
      (ComponentDiagram.openDottedEncircling
        geometry.dottedComponent.componentId
        geometry.punctureBoundary)).interpret
      category.premodular
      (presentation.labelOf category.premodular
        (geometry.labelingWithDotted dottedLabel remaining)))

/-- The factorized closed term is the common context applied to the opening. -/
theorem factorizedEvaluation_eq_context
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S)
    (dottedLabel : S) :
    geometry.factorizedEvaluation category presentation remaining dottedLabel =
      evalContextLinearMap (R := K)
        (geometry.referenceExteriorContext category presentation remaining)
        (geometry.referenceOpenEvaluation
          category presentation remaining dottedLabel) := by
  exact geometry.factorizedTerm_eval_eq_contextOpen
    category presentation dottedLabel remaining

/-- Specialization of character-neutrality to the fixed reference boundary. -/
theorem referenceBoundaryCharacter_smul_openOperator
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S)
    (coefficient : ℤ) :
    geometry.referenceBoundaryCharacter category automorphism presentation
        remaining coefficient •
      openKirbyEncirclingOperator category.premodular
        (geometry.punctureBoundary.interpret category.premodular
          (geometry.referenceLabelOf category presentation remaining)).denote =
      openKirbyEncirclingOperator category.premodular
        (geometry.punctureBoundary.interpret category.premodular
          (geometry.referenceLabelOf category presentation remaining)).denote := by
  exact boundaryCharacterPower_smul_openKirbyEncirclingOperator
    category automorphism
      (geometry.referenceLabelOf category presentation remaining)
      geometry.punctureBoundary coefficient

/--
The exact finite sum over the selected dotted label is unchanged after
inserting any integral boundary-character power.
-/
theorem fixedRemaining_dottedSum_invariant
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S)
    (coefficient : ℤ) :
    (∑ dottedLabel,
      (boundaryCharacterPower
          category.premodular.toFusionCategoryData automorphism
          (presentation.labelOf category.premodular
            (geometry.labelingWithDotted dottedLabel remaining))
          geometry.punctureBoundary coefficient *
        category.premodular.quantumDimension dottedLabel) •
          geometry.factorizedEvaluation
            category presentation remaining dottedLabel) =
      ∑ dottedLabel,
        category.premodular.quantumDimension dottedLabel •
          geometry.factorizedEvaluation
            category presentation remaining dottedLabel := by
  classical
  let context := geometry.referenceExteriorContext category presentation remaining
  let character := geometry.referenceBoundaryCharacter
    category automorphism presentation remaining coefficient
  let operator := openKirbyEncirclingOperator category.premodular
    (geometry.punctureBoundary.interpret category.premodular
      (geometry.referenceLabelOf category presentation remaining)).denote
  calc
    _ = ∑ dottedLabel,
        (character * category.premodular.quantumDimension dottedLabel) •
          evalContextLinearMap (R := K) context
            (geometry.referenceOpenEvaluation
              category presentation remaining dottedLabel) := by
      apply Finset.sum_congr rfl
      intro dottedLabel _
      rw [geometry.boundaryCharacterPower_labelingWithDotted_eq_reference
        category automorphism presentation dottedLabel remaining coefficient]
      rw [geometry.factorizedEvaluation_eq_context
        category presentation remaining dottedLabel]
      rfl
    _ = character •
        (∑ dottedLabel,
          category.premodular.quantumDimension dottedLabel •
            evalContextLinearMap (R := K) context
              (geometry.referenceOpenEvaluation
                category presentation remaining dottedLabel)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro dottedLabel _
      rw [smul_smul]
    _ = character •
        evalContextLinearMap (R := K) context operator := by
      congr 1
      simp_rw [← map_smul]
      rw [← map_sum]
      unfold operator openKirbyEncirclingOperator referenceOpenEvaluation
      rfl
    _ = evalContextLinearMap (R := K) context
        (character • operator) := by
      rw [map_smul]
    _ = evalContextLinearMap (R := K) context operator := by
      rw [geometry.referenceBoundaryCharacter_smul_openOperator
        category automorphism presentation remaining coefficient]
    _ = ∑ dottedLabel,
        category.premodular.quantumDimension dottedLabel •
          evalContextLinearMap (R := K) context
            (geometry.referenceOpenEvaluation
              category presentation remaining dottedLabel) := by
      simp_rw [← map_smul]
      rw [← map_sum]
      unfold operator openKirbyEncirclingOperator referenceOpenEvaluation
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro dottedLabel _
      exact congrArg
        (fun morphism =>
          category.premodular.quantumDimension dottedLabel • morphism)
        (by
          simpa only [context] using
            (geometry.factorizedEvaluation_eq_context
              category presentation remaining dottedLabel).symm)

end TwistedYetter.Kirby.DottedBoundaryGeometry.GeneratorGeometry
