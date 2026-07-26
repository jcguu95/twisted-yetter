import TwistedYetter.Kirby.DottedBoundaryFiniteSum

/-!
# Degree-three boundary invariance from dotted geometry

The local finite dotted-label identity is lifted here to the complete global
label sum, then to the normalized cycle evaluator, and finally through the
actual handle-chain homology quotient.
-/

namespace TwistedYetter.Kirby.DottedBoundaryGeometry.GeneratorGeometry

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentBoundaryCharacter
open TwistedYetter.Kirby.HandleChainGeneratorReduction
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SelectedCoordinateFiniteSum

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- One fixed exterior-label sector is invariant under a generator boundary. -/
theorem fixedRemaining_completeSummand_invariant
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (cycle : presentation.DegreeTwoCycle)
    (remaining : RemainingIndex geometry.dottedComponentIndex → S)
    (coefficient : ℤ) :
    (∑ dottedLabel,
      presentation.cycleGlobalWeight category.premodular automorphism
          (addBoundary presentation.topology.handleChain cycle
            (coordinateChain presentation.topology.handleChain
              generator coefficient))
          (geometry.labelingWithDotted dottedLabel remaining) •
        Diagram.eval C
          (presentation.termDiagram category.premodular
            (geometry.labelingWithDotted dottedLabel remaining))) =
      ∑ dottedLabel,
        presentation.cycleGlobalWeight category.premodular automorphism cycle
            (geometry.labelingWithDotted dottedLabel remaining) •
          Diagram.eval C
            (presentation.termDiagram category.premodular
              (geometry.labelingWithDotted dottedLabel remaining)) := by
  classical
  let remainingWeight := geometry.remainingGlobalWeight
    category automorphism presentation cycle remaining
  calc
    _ = ∑ dottedLabel,
        (boundaryCharacterPower
            category.premodular.toFusionCategoryData automorphism
            (presentation.labelOf category.premodular
              (geometry.labelingWithDotted dottedLabel remaining))
            geometry.punctureBoundary coefficient *
          (category.premodular.quantumDimension dottedLabel *
            remainingWeight)) •
          geometry.factorizedEvaluation
            category presentation remaining dottedLabel := by
      apply Finset.sum_congr rfl
      intro dottedLabel _
      rw [geometry.cycleGlobalWeight_add_integralGenerator
        category automorphism presentation cycle coefficient]
      rw [geometry.cycleGlobalWeight_split_dotted
        category automorphism presentation cycle dottedLabel remaining]
      rw [geometry.termDiagram_eval_eq_factorized
        category presentation
        (geometry.labelingWithDotted dottedLabel remaining)]
      rfl
    _ = remainingWeight •
        (∑ dottedLabel,
          (boundaryCharacterPower
              category.premodular.toFusionCategoryData automorphism
              (presentation.labelOf category.premodular
                (geometry.labelingWithDotted dottedLabel remaining))
              geometry.punctureBoundary coefficient *
            category.premodular.quantumDimension dottedLabel) •
            geometry.factorizedEvaluation
              category presentation remaining dottedLabel) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro dottedLabel _
      rw [smul_smul]
      congr 1
      ring
    _ = remainingWeight •
        (∑ dottedLabel,
          category.premodular.quantumDimension dottedLabel •
            geometry.factorizedEvaluation
              category presentation remaining dottedLabel) := by
      rw [geometry.fixedRemaining_dottedSum_invariant
        category automorphism presentation remaining coefficient]
    _ = ∑ dottedLabel,
        (category.premodular.quantumDimension dottedLabel *
          remainingWeight) •
          geometry.factorizedEvaluation
            category presentation remaining dottedLabel := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro dottedLabel _
      rw [smul_smul]
      congr 1
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro dottedLabel _
      rw [← geometry.cycleGlobalWeight_split_dotted
        category automorphism presentation cycle dottedLabel remaining]
      rw [geometry.termDiagram_eval_eq_factorized
        category presentation
        (geometry.labelingWithDotted dottedLabel remaining)]
      rfl

/-- Reindex a global labeling through this geometry's selected dotted slot. -/
theorem sum_splitAt_geometry
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    {V : Type*} [AddCommMonoid V]
    (summand : presentation.GlobalLabeling (S := S) → V) :
    (∑ labeling, summand labeling) =
      ∑ remaining : RemainingIndex geometry.dottedComponentIndex → S,
        ∑ dottedLabel : S,
          summand (geometry.labelingWithDotted dottedLabel remaining) := by
  exact sum_splitAt geometry.dottedComponentIndex summand

/-- The complete global finite sum is invariant under one integral generator. -/
theorem cycleLinearDiagram_eval_add_integralGenerator
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (cycle : presentation.DegreeTwoCycle)
    (coefficient : ℤ) :
    LinearDiagram.eval
        (presentation.cycleLinearDiagram category.premodular automorphism
          (addBoundary presentation.topology.handleChain cycle
            (coordinateChain presentation.topology.handleChain
              generator coefficient))) =
      LinearDiagram.eval
        (presentation.cycleLinearDiagram category.premodular automorphism cycle) := by
  classical
  rw [presentation.cycleLinearDiagram_eval category.premodular automorphism]
  rw [presentation.cycleLinearDiagram_eval category.premodular automorphism]
  let shiftedCycle :=
    addBoundary presentation.topology.handleChain cycle
      (coordinateChain presentation.topology.handleChain
        generator coefficient)
  let shiftedSummand : presentation.GlobalLabeling (S := S) →
      (𝟙_ C ⟶ 𝟙_ C) := fun labeling =>
    presentation.cycleGlobalWeight category.premodular automorphism
        shiftedCycle labeling •
      Diagram.eval C (presentation.termDiagram category.premodular labeling)
  let originalSummand : presentation.GlobalLabeling (S := S) →
      (𝟙_ C ⟶ 𝟙_ C) := fun labeling =>
    presentation.cycleGlobalWeight category.premodular automorphism cycle labeling •
      Diagram.eval C (presentation.termDiagram category.premodular labeling)
  change (∑ labeling, shiftedSummand labeling) =
    ∑ labeling, originalSummand labeling
  rw [geometry.sum_splitAt_geometry shiftedSummand]
  rw [geometry.sum_splitAt_geometry originalSummand]
  apply Finset.sum_congr rfl
  intro remaining _
  simpa only [shiftedSummand, originalSummand, shiftedCycle] using
    geometry.fixedRemaining_completeSummand_invariant
      category automorphism presentation cycle remaining coefficient

/-- The normalized explicit-cycle evaluator is invariant under one generator. -/
theorem cycleEvalC_add_integralGenerator
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    {generator : Fin presentation.topology.counts.turnedOver.h3}
    (geometry : GeneratorGeometry presentation generator)
    (cycle : presentation.DegreeTwoCycle)
    (coefficient : ℤ) :
    presentation.cycleEvalC category automorphism
        (addBoundary presentation.topology.handleChain cycle
          (coordinateChain presentation.topology.handleChain
            generator coefficient)) =
      presentation.cycleEvalC category automorphism cycle := by
  have linearEvaluation :=
    geometry.cycleLinearDiagram_eval_add_integralGenerator
      category automorphism presentation cycle coefficient
  have rawNumerator := congrArg
    category.premodular.toFusionCategoryData.closedScalar linearEvaluation
  simp only [CanonicalPresentation.cycleEvalC,
    CanonicalPresentation.rawCycleColourEval,
    CanonicalPresentation.cycleEvaluationState,
    CanonicalPresentation.cycleRawNumerator,
    TwistedYetter.Kirby.KirbyCancellation.EvaluationState.normalized]
  rw [rawNumerator]

end TwistedYetter.Kirby.DottedBoundaryGeometry.GeneratorGeometry

namespace TwistedYetter.Kirby.DottedBoundaryGeometry

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.HandleChainGeneratorReduction
open TwistedYetter.Kirby.KirbyCompleteness

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- A complete geometry system supplies every finite generator check. -/
theorem GeometrySystem.generatorInvariant
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    (system : GeometrySystem presentation) :
    IntegralGeneratorBoundaryInvariant
      presentation.topology.handleChain
      (presentation.cycleEvalC category automorphism) := by
  intro cycle generator coefficient
  exact (system.geometry generator).cycleEvalC_add_integralGenerator
    category automorphism presentation cycle coefficient

/-- Therefore the evaluator depends only on the actual handle-chain H2 class. -/
theorem GeometrySystem.respects_homology_class
    {H2 : Type uH} [AddCommGroup H2]
    (category : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    (system : GeometrySystem presentation)
    (left right : presentation.DegreeTwoCycle)
    (sameClass :
      presentation.topology.handleChain.complex.homologyπ 2 left =
        presentation.topology.handleChain.complex.homologyπ 2 right) :
    presentation.cycleEvalC category automorphism left =
      presentation.cycleEvalC category automorphism right := by
  exact HandleChainGeneratorReduction.respects_homology_class
    presentation.topology.handleChain
    (presentation.cycleEvalC category automorphism)
    (system.generatorInvariant category automorphism presentation)
    left right sameClass

/-- Machine-visible status of the completed category-and-homology compiler. -/
def integrationStatus : String :=
  "PASS_DOTTED_GEOMETRY_TO_H2_REPRESENTATIVE_INDEPENDENCE"

/-- Exact scope not supplied by the theorems in this module. -/
def integrationRemainingScope : String :=
  "For a concrete raw presentation, construct its category-neutral "
    ++ "GeometrySystem from source-backed dotted spanning-disk data. No "
    ++ "category calculation or equality of evaluator values remains in "
    ++ "that obligation."

end TwistedYetter.Kirby.DottedBoundaryGeometry
