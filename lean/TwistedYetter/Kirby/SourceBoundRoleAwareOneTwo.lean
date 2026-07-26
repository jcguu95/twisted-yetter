import TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
import TwistedYetter.Kirby.CanonicalCycleMoveGeometry
import TwistedYetter.Kirby.PremodularOneTwoCutCancellation
import TwistedYetter.Kirby.RoleAwareAddedOrdinaryTransport

/-!
# Source-bound role-aware 1--2 cancellation

The source-bound theorem takes category-neutral topology and finite component
bookkeeping as explicit certificate data.  This file declares no global
existence axiom.  All label support, character, finite-sum, scalar, and
normalization equalities are proved below.
-/

namespace TwistedYetter.Kirby.SourceBoundRoleAwareOneTwo

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry
open TwistedYetter.Kirby.PremodularOneTwoCutCancellation
open TwistedYetter.Kirby.RoleAwareAddedOrdinaryTransport
open TwistedYetter.Kirby.RoleAwareComponentDiagram
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.SimultaneousDottedCutGeometry

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Expand the role-aware raw numerator into its actual finite label sum. -/
theorem roleAwareRawNumerator_eq_sum
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation H2)
    (geometry : Geometry presentation)
    (cycle : presentation.DegreeTwoCycle) :
    CanonicalPresentation.roleAwareRawNumerator
        𝒞 η presentation geometry cycle =
      ∑ labeling,
        CanonicalPresentation.roleAwareGlobalWeight
            𝒞 η presentation cycle labeling *
          𝒞.toFusionCategoryData.closedScalar
            (Diagram.eval C
              (CanonicalPresentation.roleAwareTermDiagram
                𝒞 η presentation geometry labeling)) := by
  classical
  unfold CanonicalPresentation.roleAwareRawNumerator
  unfold CanonicalPresentation.roleAwareLinearDiagram
  rw [TwistedYetter.Kirby.LinearDiagram.eval_weightedSum]
  change
    𝒞.toFusionCategoryData.unitEndLinearEquiv.symm
        (∑ labeling,
          CanonicalPresentation.roleAwareGlobalWeight
              𝒞 η presentation cycle labeling •
            Diagram.eval C
              (CanonicalPresentation.roleAwareTermDiagram
                𝒞 η presentation geometry labeling)) =
      _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro labeling _
  exact 𝒞.toFusionCategoryData.closedScalar_smul _ _

/--
Exact category-neutral data for one role-aware 1--2 birth.

No field mentions a category, character, morphism, scalar, or evaluator
equality.
-/
structure BirthTopology
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2) where
  sourceGeometry : Geometry source
  targetGeometry : Geometry target
  newDottedId : String
  newTwoHandleId : String
  distinct_ids : newDottedId ≠ newTwoHandleId
  ordinaryChange : AddedOrdinaryIndexChange source target 1
  added_ordinary_id :
    ordinaryChange.addedComponentId 0 = newTwoHandleId
  target_label_transport :
    {Label : Type} →
    (unitIndex : Label) →
    (sourceLabeling :
      CanonicalPresentation.OrdinaryLabeling
        (S := Label) source) →
    (addedLabeling : Fin 1 → Label) →
      CanonicalPresentation.roleAwareLabelOfWithUnit
          unitIndex target
          ((ordinaryChange.labelingEquiv Label).symm
            (sourceLabeling, addedLabeling)) =
        Function.update
          (CanonicalPresentation.roleAwareLabelOfWithUnit
            unitIndex source sourceLabeling)
          newTwoHandleId (addedLabeling 0)
  new_two_handle_absent_from_source :
    newTwoHandleId ∉ sourceGeometry.cutDiagram.componentIds
  cut_factorization :
    RoleAwareDiagram.GeneratedIsotopy
      targetGeometry.cutDiagram
      (RoleAwareDiagram.closedTensor
        (RoleAwareDiagram.oneTwoCutPair newDottedId newTwoHandleId)
        sourceGeometry.cutDiagram)

namespace BirthTopology

/-- Updating the fresh new ID cannot alter the old exterior evaluation. -/
theorem source_eval_update_fresh
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (topology : BirthTopology source target)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceLabeling :
      CanonicalPresentation.OrdinaryLabeling (S := S) source)
    (newLabel : S) :
    Diagram.eval C
        (topology.sourceGeometry.cutDiagram.interpret 𝒞 η
          (Function.update
            (CanonicalPresentation.roleAwareLabelOf
              𝒞 source sourceLabeling)
            topology.newTwoHandleId newLabel)) =
      Diagram.eval C
        (topology.sourceGeometry.cutDiagram.interpret 𝒞 η
          (CanonicalPresentation.roleAwareLabelOf
            𝒞 source sourceLabeling)) := by
  apply RoleAwareDiagram.eval_interpret_eq_of_eq_on_componentIds
  intro componentId membership
  have different : componentId ≠ topology.newTwoHandleId := by
    intro equality
    apply topology.new_two_handle_absent_from_source
    simpa [equality] using membership
  simp [Function.update, different]

/--
One fixed target-label term factors into the actual local cut pair and the
unchanged source exterior.
-/
theorem target_term_closedScalar_factor
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (topology : BirthTopology source target)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceLabeling :
      CanonicalPresentation.OrdinaryLabeling (S := S) source)
    (addedLabeling : Fin 1 → S) :
    𝒞.toFusionCategoryData.closedScalar
        (Diagram.eval C
          (CanonicalPresentation.roleAwareTermDiagram
            𝒞 η target topology.targetGeometry
            ((topology.ordinaryChange.labelingEquiv S).symm
              (sourceLabeling, addedLabeling)))) =
      specialCutMeridianClosedValue 𝒞 (addedLabeling 0) *
        𝒞.toFusionCategoryData.closedScalar
          (Diagram.eval C
            (CanonicalPresentation.roleAwareTermDiagram
              𝒞 η source topology.sourceGeometry sourceLabeling)) := by
  let sourceLabels :=
    CanonicalPresentation.roleAwareLabelOf 𝒞 source sourceLabeling
  let updatedLabels :=
    Function.update sourceLabels topology.newTwoHandleId (addedLabeling 0)
  have labelsEqCore :=
    topology.target_label_transport
      𝒞.toFusionCategoryData.unitIndex sourceLabeling addedLabeling
  have labelsEq :
      CanonicalPresentation.roleAwareLabelOf
          𝒞 target
          ((topology.ordinaryChange.labelingEquiv S).symm
            (sourceLabeling, addedLabeling)) =
        updatedLabels := by
    simpa [CanonicalPresentation.roleAwareLabelOf,
      sourceLabels, updatedLabels] using labelsEqCore
  have isotopyEval :=
    topology.cut_factorization.eval_eq 𝒞 η updatedLabels
  unfold CanonicalPresentation.roleAwareTermDiagram
  rw [labelsEq]
  have isotopyScalar :=
    congrArg 𝒞.toFusionCategoryData.closedScalar isotopyEval
  apply Eq.trans isotopyScalar
  change
    𝒞.toFusionCategoryData.closedScalar
        (Diagram.eval C
          (TwistedYetter.Kirby.HomologicallyTwistedInvariant.closedTensorDiagram
            ((RoleAwareDiagram.oneTwoCutPair
              topology.newDottedId topology.newTwoHandleId).interpret
                𝒞 η updatedLabels)
            (topology.sourceGeometry.cutDiagram.interpret
              𝒞 η updatedLabels))) =
      _
  rw [closedTensorScalar_multiplicative]
  apply congrArg₂ (· * ·)
  · calc
      _ = specialCutMeridianClosedValue 𝒞
          (updatedLabels topology.newTwoHandleId) :=
        oneTwoCutPair_closedScalar
          𝒞 η topology.newDottedId topology.newTwoHandleId updatedLabels
      _ = specialCutMeridianClosedValue 𝒞 (addedLabeling 0) := by
        simp [updatedLabels]
  · simpa [updatedLabels, sourceLabels] using
      congrArg 𝒞.toFusionCategoryData.closedScalar
        (topology.source_eval_update_fresh
          𝒞 η sourceLabeling (addedLabeling 0))

/-- The newly born ordinary meridian has only its quantum-dimension weight. -/
theorem localWeight_eq_quantumDimension
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (topology : BirthTopology source target)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    (transport :
      topology.ordinaryChange.ExponentTransport sourceCycle targetCycle)
    (addedExponentZero : transport.addedExponent 0 = 0)
    (addedLabeling : Fin 1 → S) :
    transport.localWeight 𝒞 η addedLabeling =
      𝒞.quantumDimension (addedLabeling 0) := by
  classical
  unfold AddedOrdinaryIndexChange.ExponentTransport.localWeight
  rw [Fintype.prod_unique]
  simpa only [Subsingleton.elim (default : Fin 1) 0,
    addedExponentZero,
    FusionCategoryData.automorphismScalarPower_zero, mul_one]

/--
The complete role-aware numerator gains exactly one global-dimension factor
under a source-bound 1--2 birth.
-/
theorem rawNumerator_birth_factor
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (topology : BirthTopology source target)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (targetCycle : target.DegreeTwoCycle)
    (transport :
      topology.ordinaryChange.ExponentTransport sourceCycle targetCycle)
    (addedExponentZero : transport.addedExponent 0 = 0) :
    CanonicalPresentation.roleAwareRawNumerator
        𝒞 η target topology.targetGeometry targetCycle =
      𝒞.globalDimension *
        CanonicalPresentation.roleAwareRawNumerator
          𝒞 η source topology.sourceGeometry sourceCycle := by
  classical
  rw [roleAwareRawNumerator_eq_sum]
  rw [roleAwareRawNumerator_eq_sum]
  rw [topology.ordinaryChange.sum_split]
  rw [Fintype.sum_prod_type]
  have addedSum :
      (∑ addedLabeling : Fin 1 → S,
        𝒞.quantumDimension (addedLabeling 0) *
          specialCutMeridianClosedValue 𝒞 (addedLabeling 0)) =
        𝒞.globalDimension := by
    simpa only [Subsingleton.elim (default : Fin 1) 0] using
      Equiv.sum_comp (Equiv.funUnique (Fin 1) S)
        (fun simple =>
          𝒞.quantumDimension simple *
            specialCutMeridianClosedValue 𝒞 simple)
        |>.trans (specialCutMeridianSum_eq_globalDimension 𝒞)
  change
    (∑ sourceLabeling, ∑ addedLabeling,
      CanonicalPresentation.roleAwareGlobalWeight
          𝒞 η target targetCycle
          ((topology.ordinaryChange.labelingEquiv S).symm
            (sourceLabeling, addedLabeling)) *
        𝒞.toFusionCategoryData.closedScalar
          (Diagram.eval C
            (CanonicalPresentation.roleAwareTermDiagram
              𝒞 η target topology.targetGeometry
              ((topology.ordinaryChange.labelingEquiv S).symm
                (sourceLabeling, addedLabeling))))) =
      𝒞.globalDimension *
        ∑ sourceLabeling,
          CanonicalPresentation.roleAwareGlobalWeight
              𝒞 η source sourceCycle sourceLabeling *
            𝒞.toFusionCategoryData.closedScalar
              (Diagram.eval C
                (CanonicalPresentation.roleAwareTermDiagram
                  𝒞 η source topology.sourceGeometry sourceLabeling))
  calc
    _ =
      ∑ sourceLabeling,
        𝒞.globalDimension *
          (CanonicalPresentation.roleAwareGlobalWeight
              𝒞 η source sourceCycle sourceLabeling *
            𝒞.toFusionCategoryData.closedScalar
              (Diagram.eval C
                (CanonicalPresentation.roleAwareTermDiagram
                  𝒞 η source topology.sourceGeometry sourceLabeling))) := by
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        calc
          (∑ addedLabeling,
              CanonicalPresentation.roleAwareGlobalWeight
                  𝒞 η target targetCycle
                  ((topology.ordinaryChange.labelingEquiv S).symm
                    (sourceLabeling, addedLabeling)) *
                𝒞.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (CanonicalPresentation.roleAwareTermDiagram
                      𝒞 η target topology.targetGeometry
                      ((topology.ordinaryChange.labelingEquiv S).symm
                        (sourceLabeling, addedLabeling))))) =
            ∑ addedLabeling : Fin 1 → S,
              (𝒞.quantumDimension (addedLabeling 0) *
                specialCutMeridianClosedValue 𝒞 (addedLabeling 0)) *
              (CanonicalPresentation.roleAwareGlobalWeight
                  𝒞 η source sourceCycle sourceLabeling *
                𝒞.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (CanonicalPresentation.roleAwareTermDiagram
                      𝒞 η source topology.sourceGeometry sourceLabeling))) := by
              apply Finset.sum_congr rfl
              intro addedLabeling _
              rw [transport.roleAwareGlobalWeight_split
                𝒞 η sourceLabeling addedLabeling]
              rw [topology.localWeight_eq_quantumDimension
                𝒞 η transport addedExponentZero addedLabeling]
              rw [topology.target_term_closedScalar_factor
                𝒞 η sourceLabeling addedLabeling]
              ring
          _ =
            𝒞.globalDimension *
              (CanonicalPresentation.roleAwareGlobalWeight
                  𝒞 η source sourceCycle sourceLabeling *
                𝒞.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (CanonicalPresentation.roleAwareTermDiagram
                      𝒞 η source topology.sourceGeometry sourceLabeling))) := by
              rw [← Finset.sum_mul, addedSum]
    _ = _ := by
      rw [Finset.mul_sum]

/-- Source-bound normalized invariance under a role-aware 1--2 birth. -/
theorem roleAwareCycleEval_birth
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (topology : BirthTopology source target)
    (countsSound :
      target.topology.counts = source.topology.counts.addOneTwo)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (targetCycle : target.DegreeTwoCycle)
    (transport :
      topology.ordinaryChange.ExponentTransport sourceCycle targetCycle)
    (addedExponentZero : transport.addedExponent 0 = 0) :
    CanonicalPresentation.roleAwareCycleEval
        𝒞 η target topology.targetGeometry targetCycle =
      CanonicalPresentation.roleAwareCycleEval
        𝒞 η source topology.sourceGeometry sourceCycle := by
  unfold CanonicalPresentation.roleAwareCycleEval
  exact normalized_eq_of_birth_raw_factor
    𝒞
    (CanonicalPresentation.roleAwareEvaluationState
      𝒞 η source topology.sourceGeometry sourceCycle)
    (CanonicalPresentation.roleAwareEvaluationState
      𝒞 η target topology.targetGeometry targetCycle)
    countsSound
    (topology.rawNumerator_birth_factor
      𝒞 η sourceCycle targetCycle transport addedExponentZero)

/--
Death is the same source-bound theorem read backwards; no second graphical or
evaluation assumption is introduced.
-/
theorem roleAwareCycleEval_death
    {H2 : Type uH} [AddCommGroup H2]
    {before after : CanonicalPresentation H2}
    (reverseBirth : BirthTopology after before)
    (countsSound :
      before.topology.counts = after.topology.counts.addOneTwo)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (afterCycle : after.DegreeTwoCycle)
    (beforeCycle : before.DegreeTwoCycle)
    (transport :
      reverseBirth.ordinaryChange.ExponentTransport afterCycle beforeCycle)
    (addedExponentZero : transport.addedExponent 0 = 0) :
    CanonicalPresentation.roleAwareCycleEval
        𝒞 η before reverseBirth.targetGeometry beforeCycle =
      CanonicalPresentation.roleAwareCycleEval
        𝒞 η after reverseBirth.sourceGeometry afterCycle :=
  reverseBirth.roleAwareCycleEval_birth
    countsSound 𝒞 η afterCycle beforeCycle transport addedExponentZero

end BirthTopology

end TwistedYetter.Kirby.SourceBoundRoleAwareOneTwo
