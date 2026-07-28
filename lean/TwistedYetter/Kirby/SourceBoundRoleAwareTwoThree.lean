import TwistedYetter.Kirby.SourceBoundRoleAwareOneTwo

/-!
# Source-bound role-aware 2--3 cancellation

A cancelling 2--3 birth adds one ordinary zero-framed unknot and no dotted
component.  The transported homology coordinate of that unknot is zero.
Consequently its character factor is the identity, its weighted label sum is
the global dimension, and the standard normalization cancels that factor.
-/

namespace TwistedYetter.Kirby.SourceBoundRoleAwareTwoThree

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.RoleAwareAddedOrdinaryTransport
open TwistedYetter.Kirby.RoleAwareComponentDiagram
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.SimultaneousDottedCutGeometry
open TwistedYetter.Kirby.SourceBoundRoleAwareOneTwo

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
Category-neutral endpoint data for adding one cancelling 2--3 pair.

The sole local graphical statement is that the target cut diagram is the
source exterior disjoint-unioned with one ordinary zero-framed unknot.
-/
structure BirthTopology
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2) where
  sourceGeometry : Geometry source
  targetGeometry : Geometry target
  newTwoHandleId : String
  ordinaryChange : AddedOrdinaryIndexChange source target 1
  added_ordinary_id :
    ordinaryChange.addedComponentId 0 = newTwoHandleId
  target_label_transport :
    {Label : Type} →
    (unitIndex : Label) →
    (sourceLabeling :
      CanonicalPresentation.OrdinaryLabeling (S := Label) source) →
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
        (.ordinary
          (ComponentRibbonDiagram.ComponentDiagram.zeroFramedUnknot
            newTwoHandleId))
        sourceGeometry.cutDiagram)

namespace BirthTopology

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

/-- One fixed target term is the unknot factor times the source exterior. -/
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
      𝒞.quantumDimension (addedLabeling 0) *
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
          (closedTensorDiagram
            ((ComponentRibbonDiagram.ComponentDiagram.zeroFramedUnknot
              topology.newTwoHandleId).interpret 𝒞 updatedLabels)
            (topology.sourceGeometry.cutDiagram.interpret
              𝒞 η updatedLabels))) =
      _
  rw [closedTensorScalar_multiplicative]
  apply congrArg₂ (· * ·)
  · calc
      _ = 𝒞.quantumDimension
          (updatedLabels topology.newTwoHandleId) :=
        ComponentRibbonDiagram.ComponentDiagram.zeroFramedUnknot_closedScalar
          𝒞 updatedLabels topology.newTwoHandleId
      _ = 𝒞.quantumDimension (addedLabeling 0) := by
        simp [updatedLabels]
  · simpa [updatedLabels, sourceLabels] using
      congrArg 𝒞.toFusionCategoryData.closedScalar
        (topology.source_eval_update_fresh
          𝒞 η sourceLabeling (addedLabeling 0))

/-- Zero transported exponent removes the character from the born unknot. -/
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

/-- The complete numerator gains exactly one global-dimension factor. -/
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
  rw [SourceBoundRoleAwareOneTwo.roleAwareRawNumerator_eq_sum]
  rw [SourceBoundRoleAwareOneTwo.roleAwareRawNumerator_eq_sum]
  rw [topology.ordinaryChange.sum_split]
  rw [Fintype.sum_prod_type]
  have addedSum :
      (∑ addedLabeling : Fin 1 → S,
        𝒞.quantumDimension (addedLabeling 0) *
          𝒞.quantumDimension (addedLabeling 0)) =
        𝒞.globalDimension := by
    simpa only [Subsingleton.elim (default : Fin 1) 0] using
      Equiv.sum_comp (Equiv.funUnique (Fin 1) S)
        (fun simple =>
          𝒞.quantumDimension simple * 𝒞.quantumDimension simple)
        |>.trans rfl
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
                𝒞.quantumDimension (addedLabeling 0)) *
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

/-- Source-bound normalized invariance under a role-aware 2--3 birth. -/
theorem roleAwareCycleEval_birth
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (topology : BirthTopology source target)
    (countsSound :
      target.topology.counts = source.topology.counts.addTwoThree)
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
  rw [
    CanonicalPresentation.roleAwareCycleEval,
    CanonicalPresentation.roleAwareCycleEval,
    topology.rawNumerator_birth_factor
      𝒞 η sourceCycle targetCycle transport addedExponentZero,
    CanonicalPresentation.roleAwareNormalizationFactor,
    CanonicalPresentation.roleAwareNormalizationFactor,
    countsSound]
  simp only [KirbyCancellation.HandleCounts.addTwoThree, pow_succ]
  field_simp [𝒞.globalDimension_ne_zero]

/-- Death is the same theorem read in the reverse direction. -/
theorem roleAwareCycleEval_death
    {H2 : Type uH} [AddCommGroup H2]
    {before after : CanonicalPresentation H2}
    (reverseBirth : BirthTopology after before)
    (countsSound :
      before.topology.counts = after.topology.counts.addTwoThree)
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

end TwistedYetter.Kirby.SourceBoundRoleAwareTwoThree
