import TwistedYetter.Kirby.CanonicalCycleMoveGeometry
import TwistedYetter.Kirby.RoleAwareFiniteSumTransport
import TwistedYetter.Kirby.RoleAwarePremodularEvaluator

/-!
# Same-component transport for role-aware label denominators

A slide does not create or delete components.  Its certified component
correspondence preserves both component IDs and component roles.  Hence it
restricts to an equivalence of the ordinary (non-dotted) labeling domains.
This file proves that restriction and the corresponding character-weight
transport.
-/

namespace TwistedYetter.Kirby.RoleAwareSameComponentTransport

open scoped BigOperators
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwareFiniteSumTransport
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

namespace OrdinaryTransport

/-- A role-preserving component correspondence restricts to ordinary indices. -/
def ordinaryIndexEquiv
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal) :
    RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryComponentIndex
        source ≃
      RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryComponentIndex
        target where
  toFun sourceIndex :=
    ⟨change.targetToSource.symm sourceIndex.1, by
      intro targetDotted
      apply sourceIndex.2
      have roleSound :=
        change.component_role_sound
          (change.targetToSource.symm sourceIndex.1)
      simpa only [Equiv.apply_symm_apply] using
        roleSound.symm.trans targetDotted⟩
  invFun targetIndex :=
    ⟨change.targetToSource targetIndex.1, by
      intro sourceDotted
      apply targetIndex.2
      have roleSound := change.component_role_sound targetIndex.1
      exact roleSound.trans sourceDotted⟩
  left_inv sourceIndex := by
    apply Subtype.ext
    exact change.targetToSource.apply_symm_apply sourceIndex.1
  right_inv targetIndex := by
    apply Subtype.ext
    exact change.targetToSource.symm_apply_apply targetIndex.1

/-- Transport an ordinary-only labeling without introducing dotted labels. -/
def ordinaryLabelingEquiv
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal) :
    RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
        (S := S) source ≃
      RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
        (S := S) target :=
  Equiv.arrowCongr (ordinaryIndexEquiv change) (Equiv.refl S)

@[simp]
theorem ordinaryLabelingEquiv_apply
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    (sourceLabeling :
      RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
        (S := S) source)
    (targetIndex :
      RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryComponentIndex
        target) :
    ordinaryLabelingEquiv change sourceLabeling targetIndex =
      sourceLabeling
        ⟨change.targetToSource targetIndex.1, by
          intro sourceDotted
          apply targetIndex.2
          exact
            (change.component_role_sound targetIndex.1).trans
              sourceDotted⟩ := by
  rfl

end OrdinaryTransport

/--
Transporting an ordinary-only labeling preserves the role-aware label
selected by every component ID.  Dotted components remain forced to the
tensor unit on both sides.
-/
theorem roleAwareLabelOf_transport
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    (sourceLabeling :
      RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
        (S := S) source)
    (componentId : String) :
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
        𝒞 target
        (OrdinaryTransport.ordinaryLabelingEquiv change sourceLabeling)
        componentId =
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
        𝒞 source sourceLabeling componentId := by
  unfold
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOfWithUnit
  cases targetLookup :
      target.componentIndexing.indexOf componentId with
  | some targetIndex =>
      have targetId :
          componentId =
            (componentAt target.topology.formal targetIndex).componentId :=
        target.componentIndexing.index_sound
          componentId targetIndex targetLookup
      have sourceLookup :
          source.componentIndexing.indexOf componentId =
            some (change.targetToSource targetIndex) := by
        rw [targetId, change.component_id_sound]
        exact source.componentIndexing.index_roundtrip
          (change.targetToSource targetIndex)
      simp only [targetLookup, sourceLookup]
      split <;> split
      · exact
          OrdinaryTransport.ordinaryLabelingEquiv_apply
            change sourceLabeling ⟨targetIndex, by assumption⟩
      · rename_i targetOrdinary sourceDotted
        have sourceDottedEq :
            (componentAt source.topology.formal
              (change.targetToSource targetIndex)).role = .dotted :=
          not_ne_iff.mp sourceDotted
        exact
          (targetOrdinary
            ((change.component_role_sound targetIndex).trans
              sourceDottedEq)).elim
      · rename_i targetDotted sourceOrdinary
        have targetDottedEq :
            (componentAt target.topology.formal targetIndex).role =
              .dotted :=
          not_ne_iff.mp targetDotted
        exact
          (sourceOrdinary
            ((change.component_role_sound targetIndex).symm.trans
              targetDottedEq)).elim
      · rfl
  | none =>
      have sourceLookup :
          source.componentIndexing.indexOf componentId = none := by
        cases sourceCase :
            source.componentIndexing.indexOf componentId with
        | none =>
            rfl
        | some sourceIndex =>
            have sourceId :
                componentId =
                  (componentAt
                    source.topology.formal sourceIndex).componentId :=
              source.componentIndexing.index_sound
                componentId sourceIndex sourceCase
            let targetIndex := change.targetToSource.symm sourceIndex
            have targetId :
                componentId =
                  (componentAt
                    target.topology.formal targetIndex).componentId := by
              rw [sourceId, change.component_id_sound targetIndex]
              simp [targetIndex]
            have targetRoundtrip :
                target.componentIndexing.indexOf componentId =
                  some targetIndex := by
              rw [targetId]
              exact target.componentIndexing.index_roundtrip targetIndex
            rw [targetLookup] at targetRoundtrip
            contradiction
      simp only [targetLookup, sourceLookup]

/--
Role-aware weights are preserved by exact component and exponent transport.
Only ordinary indices occur in either product.
-/
theorem roleAwareGlobalWeight_transport
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    (transport :
      SameComponentCycleExponentTransport
        source target change sourceCycle targetCycle)
    (sourceLabeling :
      RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
        (S := S) source) :
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareGlobalWeight
        𝒞 η source sourceCycle sourceLabeling =
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareGlobalWeight
        𝒞 η target targetCycle
        (OrdinaryTransport.ordinaryLabelingEquiv change sourceLabeling) := by
  classical
  unfold
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareGlobalWeight
  apply Fintype.prod_equiv (OrdinaryTransport.ordinaryIndexEquiv change)
  intro sourceIndex
  simp only [CanonicalPresentation.cycleComponentWeight]
  let targetIndex := OrdinaryTransport.ordinaryIndexEquiv change sourceIndex
  have indexSound :
      change.targetToSource targetIndex.1 = sourceIndex.1 := by
    exact change.targetToSource.apply_symm_apply sourceIndex.1
  have exponentSound := transport.exponent_sound targetIndex.1
  simp only [componentAt, indexSound] at exponentSound
  have roleLabel :
      OrdinaryTransport.ordinaryLabelingEquiv change sourceLabeling targetIndex =
        sourceLabeling sourceIndex := by
    rw [OrdinaryTransport.ordinaryLabelingEquiv_apply]
    exact congrArg sourceLabeling (Subtype.ext indexSound)
  rw [roleLabel]
  exact congrArg
    (fun exponent =>
      𝒞.premodular.quantumDimension (sourceLabeling sourceIndex) *
        𝒞.premodular.toFusionCategoryData.automorphismScalarPower
          η (sourceLabeling sourceIndex) exponent)
    exponentSound.symm

/--
Once the exact source-bound local movie proves every transported term,
ordinary-label reindexing upgrades it to the complete role-aware finite sum.
-/
theorem roleAwareLinearDiagram_eval_transport
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (sourceGeometry :
      SimultaneousDottedCutGeometry.Geometry source)
    (targetGeometry :
      SimultaneousDottedCutGeometry.Geometry target)
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    (transport :
      SameComponentCycleExponentTransport
        source target change sourceCycle targetCycle)
    (term_sound :
      (sourceLabeling :
        RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
          (S := S) source) →
        CategoricalTangle.Diagram.eval C
            (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
                𝒞 η source sourceGeometry sourceLabeling) =
          CategoricalTangle.Diagram.eval C
            (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
                𝒞 η target targetGeometry
                (OrdinaryTransport.ordinaryLabelingEquiv
                  change sourceLabeling))) :
    LinearDiagram.eval
        (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLinearDiagram
            𝒞 η source sourceGeometry sourceCycle) =
      LinearDiagram.eval
        (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLinearDiagram
            𝒞 η target targetGeometry targetCycle) := by
  unfold
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLinearDiagram
  exact eval_weightedSum_equiv
    (OrdinaryTransport.ordinaryLabelingEquiv change)
    (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareGlobalWeight
      𝒞 η source sourceCycle)
    (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareGlobalWeight
      𝒞 η target targetCycle)
    (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
      𝒞 η source sourceGeometry)
    (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
      𝒞 η target targetGeometry)
    (roleAwareGlobalWeight_transport 𝒞 η change transport)
    term_sound

/-- The same complete transport after applying the category's closed scalar. -/
theorem roleAwareRawNumerator_transport
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (sourceGeometry :
      SimultaneousDottedCutGeometry.Geometry source)
    (targetGeometry :
      SimultaneousDottedCutGeometry.Geometry target)
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    (transport :
      SameComponentCycleExponentTransport
        source target change sourceCycle targetCycle)
    (term_sound :
      (sourceLabeling :
        RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
          (S := S) source) →
        CategoricalTangle.Diagram.eval C
            (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
              𝒞 η source sourceGeometry sourceLabeling) =
          CategoricalTangle.Diagram.eval C
            (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
              𝒞 η target targetGeometry
              (OrdinaryTransport.ordinaryLabelingEquiv
                change sourceLabeling))) :
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareRawNumerator
        𝒞 η source sourceGeometry sourceCycle =
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareRawNumerator
        𝒞 η target targetGeometry targetCycle := by
  unfold
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareRawNumerator
  exact congrArg 𝒞.toFusionCategoryData.closedScalar
    (roleAwareLinearDiagram_eval_transport
      𝒞 η sourceGeometry targetGeometry change transport term_sound)

/-- Equal counts and source-bound term transport give equal normalized values. -/
theorem roleAwareCycleEval_transport
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (sourceGeometry :
      SimultaneousDottedCutGeometry.Geometry source)
    (targetGeometry :
      SimultaneousDottedCutGeometry.Geometry target)
    (countsSound : source.topology.counts = target.topology.counts)
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    (transport :
      SameComponentCycleExponentTransport
        source target change sourceCycle targetCycle)
    (term_sound :
      (sourceLabeling :
        RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
          (S := S) source) →
        CategoricalTangle.Diagram.eval C
            (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
              𝒞 η source sourceGeometry sourceLabeling) =
          CategoricalTangle.Diagram.eval C
            (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
              𝒞 η target targetGeometry
              (OrdinaryTransport.ordinaryLabelingEquiv
                change sourceLabeling))) :
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
        𝒞 η source sourceGeometry sourceCycle =
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
        𝒞 η target targetGeometry targetCycle := by
  unfold
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
  apply
    TwistedYetter.Kirby.HomologicallyTwistedInvariant.EvaluatedTableTwoStep.normalized_eq_of_counts_and_raw
  · exact countsSound
  · exact roleAwareRawNumerator_transport
      𝒞 η sourceGeometry targetGeometry change transport term_sound

/--
Equal complete role-aware finite sums give equal normalized evaluations.

Unlike `roleAwareCycleEval_transport`, this theorem does not require
fixed-label term equality.  It is the correct interface for a 2/2 Kirby
slide, whose proof may reindex and resolve the stationary Kirby colour
through intermediate fusion channels before the two complete sums agree.
-/
theorem roleAwareCycleEval_eq_of_linearDiagram_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (sourceGeometry :
      SimultaneousDottedCutGeometry.Geometry source)
    (targetGeometry :
      SimultaneousDottedCutGeometry.Geometry target)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (targetCycle : target.DegreeTwoCycle)
    (sum_sound :
      LinearDiagram.eval
          (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLinearDiagram
            𝒞 η source sourceGeometry sourceCycle) =
        LinearDiagram.eval
          (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLinearDiagram
            𝒞 η target targetGeometry targetCycle)) :
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
        𝒞 η source sourceGeometry sourceCycle =
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
        𝒞 η target targetGeometry targetCycle := by
  unfold
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareEvaluationState
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareRawNumerator
  apply
    TwistedYetter.Kirby.HomologicallyTwistedInvariant.EvaluatedTableTwoStep.normalized_eq_of_counts_and_raw
  · exact countsSound
  · exact congrArg 𝒞.toFusionCategoryData.closedScalar sum_sound

end TwistedYetter.Kirby.RoleAwareSameComponentTransport
