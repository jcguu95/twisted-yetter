import TwistedYetter.Kirby.CanonicalMoveGeometry

/-!
# Cycle-safe geometry for canonical Kirby moves

The conditional evaluator chooses a representative of each second-homology
class by classical choice.  Such choices do not commute strictly with Kirby
moves.  This module therefore states all move geometry for an explicit source
dual two-cycle and an explicitly transported target dual two-cycle.

The structures below contain no equality of evaluator values.  They record:

* the target cycle and its transported homology class;
* exact component and integer-exponent transport;
* exact free-diagram endpoint factorizations; and
* restricted framed-isotopy proof terms.

Lean derives the finite-sum and normalization calculations.  Turning these
explicit-cycle calculations into a homology-level invariant requires the
dual-boundary graphical realization, including the Tham `k = 3` vacuum
projector on primal dotted one-handles.
-/

namespace TwistedYetter.Kirby.CanonicalCycleMoveGeometry

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
open TwistedYetter.Kirby.CanonicalMoveGeometry
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.ComponentRibbonIsotopy
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.EGNOModularKirbyMoves.LiteratureBackedModularGraphicalEnvironment
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
An explicit target cycle representing the transported class of each source
cycle.  No choice of representative is required to be natural.
-/
structure CycleTransport
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (targetClass : H2 → H2) where
  targetCycle :
    source.DegreeTwoCycle → target.DegreeTwoCycle
  class_sound :
    (sourceCycle : source.DegreeTwoCycle) →
      target.topology.h2ModelEquiv
          (target.topology.handleChain.complex.homologyπ 2
            (targetCycle sourceCycle)) =
        targetClass
          (source.topology.h2ModelEquiv
            (source.topology.handleChain.complex.homologyπ 2 sourceCycle))

namespace CycleTransport

/--
Transport an explicit cycle by the actual forward chain map retained by a
marked handle-chain equivalence.

This construction is the reason no move compiler is allowed to choose a
target cycle independently of the chain-level topology input.
-/
noncomputable def ofMarkedH2Transport
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (transport :
      MarkedH2Transport source.topology target.topology) :
    CycleTransport source target transport.targetClass where
  targetCycle sourceCycle :=
    (HomologicalComplex.cyclesMap
      transport.chainEquivalence.homotopyEquiv.hom 2) sourceCycle
  class_sound sourceCycle := by
    change
      target.topology.h2ModelEquiv
          ((HomologicalComplex.cyclesMap
              transport.chainEquivalence.homotopyEquiv.hom 2 ≫
            target.topology.handleChain.complex.homologyπ 2)
            sourceCycle) =
        transport.targetClass
          (source.topology.h2ModelEquiv
            (source.topology.handleChain.complex.homologyπ 2 sourceCycle))
    simp [MarkedH2Transport.targetClass,
      MarkedH2Transport.homologyEquiv,
      MarkedH2Transport.homologyAddEquiv,
      HandleChainEquivalence.secondHomologyAddEquiv,
      HandleChainEquivalence.secondHomologyLinearEquiv]
    have naturality :=
      congrArg
        (fun morphism =>
          (ConcreteCategory.hom morphism) sourceCycle)
        (HomologicalComplex.homologyπ_naturality
          (φ := transport.chainEquivalence.homotopyEquiv.hom)
          (i := 2))
    simpa only [ConcreteCategory.comp_apply] using naturality.symm

/--
Transport a target cycle backwards by the inverse chain map of the same
marked handle-chain equivalence.
-/
noncomputable def ofMarkedH2TransportInverse
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (transport :
      MarkedH2Transport source.topology target.topology) :
    CycleTransport target source transport.homologyEquiv.symm where
  targetCycle targetCycle :=
    (HomologicalComplex.cyclesMap
      transport.chainEquivalence.homotopyEquiv.inv 2) targetCycle
  class_sound targetCycle := by
    change
      source.topology.h2ModelEquiv
          ((HomologicalComplex.cyclesMap
              transport.chainEquivalence.homotopyEquiv.inv 2 ≫
            source.topology.handleChain.complex.homologyπ 2)
            targetCycle) =
        transport.homologyEquiv.symm
          (target.topology.h2ModelEquiv
            (target.topology.handleChain.complex.homologyπ 2 targetCycle))
    apply transport.homologyEquiv.injective
    simp only [Equiv.apply_symm_apply]
    simp [MarkedH2Transport.homologyEquiv,
      MarkedH2Transport.homologyAddEquiv,
      HandleChainEquivalence.secondHomologyAddEquiv,
      HandleChainEquivalence.secondHomologyLinearEquiv]
    have naturality :=
      congrArg
        (fun morphism =>
          (ConcreteCategory.hom morphism) targetCycle)
        (HomologicalComplex.homologyπ_naturality
          (φ := transport.chainEquivalence.homotopyEquiv.inv)
          (i := 2))
    have cycleClass :
        source.topology.handleChain.complex.homologyπ 2
            ((HomologicalComplex.cyclesMap
                transport.chainEquivalence.homotopyEquiv.inv 2)
              targetCycle) =
          (HomologicalComplex.homologyMap
              transport.chainEquivalence.homotopyEquiv.inv 2)
            (target.topology.handleChain.complex.homologyπ 2 targetCycle) := by
      simpa only [ConcreteCategory.comp_apply] using naturality.symm
    rw [cycleClass]
    let homologyIso :=
      transport.chainEquivalence.homotopyEquiv.toHomologyIso 2
    have inverseLaw :=
      congrArg
        (fun morphism =>
          (ConcreteCategory.hom morphism)
            (target.topology.handleChain.complex.homologyπ 2 targetCycle))
        homologyIso.inv_hom_id
    simpa only [homologyIso, HomotopyEquiv.toHomologyIso,
      ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using inverseLaw

end CycleTransport

/-- Exact exponent transport for one pair of explicit cycles. -/
structure SameComponentCycleExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    (sourceCycle : source.DegreeTwoCycle)
    (targetCycle : target.DegreeTwoCycle) where
  exponent_sound :
    (targetIndex : ComponentIndex target.topology.formal) →
      target.cycleComponentExponent targetCycle
          (componentAt target.topology.formal targetIndex) =
        source.cycleComponentExponent sourceCycle
          (componentAt source.topology.formal
            (change.targetToSource targetIndex))

namespace SameComponentCycleExponentTransport

/-- Exact-cycle component weights are preserved under reindexing. -/
theorem cycleGlobalWeight_transport
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    (transport :
      SameComponentCycleExponentTransport
        source target change sourceCycle targetCycle)
    (sourceLabeling : source.GlobalLabeling (S := S)) :
    source.cycleGlobalWeight 𝒞.premodular automorphism sourceCycle sourceLabeling =
      target.cycleGlobalWeight 𝒞.premodular automorphism targetCycle
        (change.labelingEquiv S sourceLabeling) := by
  classical
  unfold CanonicalPresentation.cycleGlobalWeight
  symm
  apply Fintype.prod_equiv change.targetToSource
  intro targetIndex
  simp only [CanonicalPresentation.cycleComponentWeight]
  have exponentSound := transport.exponent_sound targetIndex
  simp only [componentAt] at exponentSound
  rw [exponentSound]
  simp only [SameComponentIndexChange.labelingEquiv,
    Equiv.coe_fn_mk, Function.comp_apply]

end SameComponentCycleExponentTransport

/-- Complete cycle-safe geometry of a framed isotopy. -/
structure FramedIsotopyCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (targetClass : H2 → H2) where
  cycleTransport : CycleTransport source target targetClass
  componentChange :
    SameComponentIndexChange
      source.topology.formal target.topology.formal
  exponentTransport :
    (sourceCycle : source.DegreeTwoCycle) →
      SameComponentCycleExponentTransport source target componentChange
        sourceCycle (cycleTransport.targetCycle sourceCycle)
  termIsotopy :
    GeneratedIsotopy
      source.componentTermDiagram target.componentTermDiagram

/--
Endpoint-bound local movie data for a framed isotopy.

Unlike `FramedIsotopyCycleGeometry`, this structure cannot choose its own
cycle transport.  The target cycle is forced by the marked handle-chain map.
The remaining fields are exactly the local geometric facts that must be read
from the source and target diagrams.
-/
structure FramedIsotopyEndpointMovie
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (transport : MarkedH2Transport source.topology target.topology) where
  componentChange :
    SameComponentIndexChange
      source.topology.formal target.topology.formal
  exponentTransport :
    (sourceCycle : source.DegreeTwoCycle) →
      SameComponentCycleExponentTransport source target componentChange
        sourceCycle
        ((CycleTransport.ofMarkedH2Transport source target transport).targetCycle
          sourceCycle)
  termIsotopy :
    GeneratedIsotopy
      source.componentTermDiagram target.componentTermDiagram

namespace FramedIsotopyEndpointMovie

/--
Promote an endpoint-bound movie to complete cycle geometry.  The cycle map is
derived from the marked handle-chain equivalence rather than supplied by the
movie.
-/
noncomputable def toCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {transport : MarkedH2Transport source.topology target.topology}
    (movie : FramedIsotopyEndpointMovie source target transport) :
    FramedIsotopyCycleGeometry source target transport.targetClass where
  cycleTransport :=
    CycleTransport.ofMarkedH2Transport source target transport
  componentChange := movie.componentChange
  exponentTransport := movie.exponentTransport
  termIsotopy := movie.termIsotopy

end FramedIsotopyEndpointMovie

namespace FramedIsotopyCycleGeometry

/-- A cycle-safe framed isotopy preserves the complete linear sum. -/
theorem cycleLinearDiagram_eval_transport
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry :
      FramedIsotopyCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle) :
    LinearDiagram.eval
        (source.cycleLinearDiagram 𝒞.premodular automorphism sourceCycle) =
      LinearDiagram.eval
        (target.cycleLinearDiagram 𝒞.premodular automorphism
          (geometry.cycleTransport.targetCycle sourceCycle)) := by
  classical
  rw [source.cycleLinearDiagram_eval 𝒞.premodular automorphism sourceCycle]
  rw [target.cycleLinearDiagram_eval 𝒞.premodular automorphism
    (geometry.cycleTransport.targetCycle sourceCycle)]
  rw [← geometry.componentChange.sum_reindex
    (fun targetLabeling =>
      target.cycleGlobalWeight 𝒞.premodular automorphism
          (geometry.cycleTransport.targetCycle sourceCycle) targetLabeling •
        Diagram.eval C (target.termDiagram 𝒞.premodular targetLabeling))]
  apply Finset.sum_congr rfl
  intro sourceLabeling _
  rw [SameComponentCycleExponentTransport.cycleGlobalWeight_transport
    𝒞 automorphism geometry.componentChange
    (geometry.exponentTransport sourceCycle) sourceLabeling]
  have termEval :
      Diagram.eval C (source.termDiagram 𝒞.premodular sourceLabeling) =
        Diagram.eval C
          (target.termDiagram 𝒞.premodular
            (geometry.componentChange.labelingEquiv S sourceLabeling)) := by
    have labels :
        target.labelOf 𝒞.premodular
            (geometry.componentChange.labelingEquiv S sourceLabeling) =
          source.labelOf 𝒞.premodular sourceLabeling := by
      funext componentId
      exact
        CanonicalMoveGeometry.SameComponentIndexChange.labelOf_transport
          𝒞 source target geometry.componentChange
          sourceLabeling componentId
    unfold CanonicalPresentation.termDiagram
    rw [labels]
    exact geometry.termIsotopy.eval_eq
      𝒞 (source.labelOf 𝒞.premodular sourceLabeling)
  exact congrArg
    (fun value =>
      target.cycleGlobalWeight 𝒞.premodular automorphism
          (geometry.cycleTransport.targetCycle sourceCycle)
          (geometry.componentChange.labelingEquiv S sourceLabeling) • value)
    termEval

end FramedIsotopyCycleGeometry

/-- Exact exponent transport when the target has a finite local summand. -/
structure AddedComponentCycleExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    {addedCount : Nat}
    (change :
      AddedComponentIndexChange
        source.topology.formal target.topology.formal addedCount)
    (sourceCycle : source.DegreeTwoCycle)
    (targetCycle : target.DegreeTwoCycle) where
  common_exponent_sound :
    (sourceIndex : ComponentIndex source.topology.formal) →
      target.cycleComponentExponent targetCycle
          (componentAt target.topology.formal
            (change.targetDecomposition.symm
              (Sum.inl sourceIndex))) =
        source.cycleComponentExponent sourceCycle
          (componentAt source.topology.formal sourceIndex)
  added_exponent : Fin addedCount → ℤ
  added_exponent_sound :
    (addedIndex : Fin addedCount) →
      target.cycleComponentExponent targetCycle
          (componentAt target.topology.formal
            (change.targetDecomposition.symm
              (Sum.inr addedIndex))) =
        added_exponent addedIndex

namespace AddedComponentCycleExponentTransport

/-- The exact coefficient of the newly inserted local components. -/
noncomputable def localWeight
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    {change :
      AddedComponentIndexChange
        source.topology.formal target.topology.formal addedCount}
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    (transport :
      AddedComponentCycleExponentTransport source target change
        sourceCycle targetCycle)
    (addedLabeling : Fin addedCount → S) : K :=
  ∏ addedIndex,
    𝒞.premodular.quantumDimension (addedLabeling addedIndex) *
      𝒞.premodular.toFusionCategoryData.automorphismScalarPower
        automorphism (addedLabeling addedIndex)
        (transport.added_exponent addedIndex)

/-- The target weight splits into common and local exact-cycle weights. -/
theorem cycleGlobalWeight_split
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    {change :
      AddedComponentIndexChange
        source.topology.formal target.topology.formal addedCount}
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    (transport :
      AddedComponentCycleExponentTransport source target change
        sourceCycle targetCycle)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin addedCount → S) :
    target.cycleGlobalWeight 𝒞.premodular automorphism targetCycle
        ((change.labelingEquiv S).symm
          (sourceLabeling, addedLabeling)) =
      source.cycleGlobalWeight 𝒞.premodular automorphism sourceCycle sourceLabeling *
        transport.localWeight 𝒞 automorphism addedLabeling := by
  classical
  unfold CanonicalPresentation.cycleGlobalWeight
  rw [change.component_product_split]
  congr 1
  · apply Finset.prod_congr rfl
    intro sourceIndex _
    simp only [CanonicalPresentation.cycleComponentWeight]
    have exponentSound := transport.common_exponent_sound sourceIndex
    simp only [componentAt] at exponentSound
    rw [exponentSound]
    simp [AddedComponentIndexChange.labelingEquiv]
  · unfold localWeight
    apply Finset.prod_congr rfl
    intro addedIndex _
    simp only [CanonicalPresentation.cycleComponentWeight]
    have exponentSound := transport.added_exponent_sound addedIndex
    simp only [componentAt] at exponentSound
    rw [exponentSound]
    simp [AddedComponentIndexChange.labelingEquiv]

end AddedComponentCycleExponentTransport

/-- Category-neutral cancellation geometry for explicit cycles. -/
structure AddedClosedCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (addedCount : Nat)
    (targetClass : H2 → H2) where
  cycleTransport : CycleTransport source target targetClass
  componentChange :
    AddedComponentIndexChange
      source.topology.formal target.topology.formal addedCount
  exponentTransport :
    (sourceCycle : source.DegreeTwoCycle) →
      AddedComponentCycleExponentTransport source target componentChange
        sourceCycle (cycleTransport.targetCycle sourceCycle)
  localDiagram : ComponentDiagram .unit .unit
  diagram_isotopy :
    GeneratedIsotopy target.componentTermDiagram
      (ComponentDiagram.closedTensor
        localDiagram source.componentTermDiagram)

/--
Endpoint data for inserting a finite closed local diagram.

The target cycle is fixed by `transport`; this structure records only the
component split, exponent calculation, and generated framed-diagram isotopy.
-/
structure AddedClosedEndpointMovie
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (addedCount : Nat)
    (targetClass : H2 → H2)
    (cycleTransport : CycleTransport source target targetClass) where
  componentChange :
    AddedComponentIndexChange
      source.topology.formal target.topology.formal addedCount
  exponentTransport :
    (sourceCycle : source.DegreeTwoCycle) →
      AddedComponentCycleExponentTransport source target componentChange
        sourceCycle
        (cycleTransport.targetCycle sourceCycle)
  localDiagram : ComponentDiagram .unit .unit
  diagram_isotopy :
    GeneratedIsotopy target.componentTermDiagram
      (ComponentDiagram.closedTensor
        localDiagram source.componentTermDiagram)

namespace AddedClosedEndpointMovie

/-- Add the forced chain-level cycle transport to an endpoint movie. -/
noncomputable def toCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    {targetClass : H2 → H2}
    {cycleTransport : CycleTransport source target targetClass}
    (movie :
      AddedClosedEndpointMovie source target addedCount
        targetClass cycleTransport) :
    AddedClosedCycleGeometry source target addedCount targetClass where
  cycleTransport := cycleTransport
  componentChange := movie.componentChange
  exponentTransport := movie.exponentTransport
  localDiagram := movie.localDiagram
  diagram_isotopy := movie.diagram_isotopy

end AddedClosedEndpointMovie

namespace AddedClosedCycleGeometry

/-- The retained source term uses exactly the original source labels. -/
theorem source_term_eval_transport
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    {targetClass : H2 → H2}
    (geometry :
      AddedClosedCycleGeometry source target addedCount targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin addedCount → S) :
    Diagram.eval C
        (source.componentTermDiagram.interpret 𝒞.premodular
          (target.labelOf 𝒞.premodular
            ((geometry.componentChange.labelingEquiv S).symm
              (sourceLabeling, addedLabeling)))) =
      Diagram.eval C
        (source.componentTermDiagram.interpret 𝒞.premodular
          (source.labelOf 𝒞.premodular sourceLabeling)) := by
  apply ComponentDiagram.eval_interpret_eq_of_eq_on_componentIds
  intro componentId membership
  obtain ⟨sourceIndex, componentIdEq⟩ :=
    TwistedYetter.Kirby.ComponentRibbonDiagram.CanonicalPresentation.componentTermDiagram_component_support
      source componentId membership
  subst componentId
  rw [AddedComponentIndexChange.labelOf_common]
  exact
    (source.labelOf_component
      𝒞.premodular sourceLabeling sourceIndex).symm

/-- The target closed term scalar splits into local and retained factors. -/
theorem term_closedScalar_split
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    {targetClass : H2 → H2}
    (geometry :
      AddedClosedCycleGeometry source target addedCount targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin addedCount → S) :
    𝒞.premodular.toFusionCategoryData.closedScalar
        (Diagram.eval C
          (target.termDiagram 𝒞.premodular
            ((geometry.componentChange.labelingEquiv S).symm
              (sourceLabeling, addedLabeling)))) =
      𝒞.premodular.toFusionCategoryData.closedScalar
          (Diagram.eval C
            (geometry.localDiagram.interpret 𝒞.premodular
              (target.labelOf 𝒞.premodular
                ((geometry.componentChange.labelingEquiv S).symm
                  (sourceLabeling, addedLabeling))))) *
        𝒞.premodular.toFusionCategoryData.closedScalar
          (Diagram.eval C
            (source.termDiagram 𝒞.premodular sourceLabeling)) := by
  let targetLabelOf :=
    target.labelOf 𝒞.premodular
      ((geometry.componentChange.labelingEquiv S).symm
        (sourceLabeling, addedLabeling))
  have sourceEval :=
    geometry.source_term_eval_transport
      𝒞 sourceLabeling addedLabeling
  change
    𝒞.premodular.toFusionCategoryData.closedScalar
        (Diagram.eval C
          (target.componentTermDiagram.interpret
            𝒞.premodular targetLabelOf)) =
      _
  have factorizationEval :=
    geometry.diagram_isotopy.eval_eq 𝒞 targetLabelOf
  rw [factorizationEval]
  change
    𝒞.premodular.toFusionCategoryData.closedScalar
        (Diagram.eval C
          (closedTensorDiagram
            (geometry.localDiagram.interpret
              𝒞.premodular targetLabelOf)
            (source.componentTermDiagram.interpret
              𝒞.premodular targetLabelOf))) =
      _
  rw [closedTensorScalar_multiplicative]
  dsimp only [targetLabelOf]
  apply congrArg₂ (· * ·)
  · rfl
  · simpa only [CanonicalPresentation.termDiagram] using
      congrArg 𝒞.premodular.toFusionCategoryData.closedScalar sourceEval

end AddedClosedCycleGeometry

/-- Cycle-safe insertion geometry for a cancelling 1--2 pair. -/
structure OneTwoBirthCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (targetClass : H2 → H2) where
  added : AddedClosedCycleGeometry source target 2 targetClass
  newDottedId : String
  newTwoHandleId : String
  distinct_ids : newDottedId ≠ newTwoHandleId
  added_dotted_component_id :
    (componentAt target.topology.formal
      (added.componentChange.targetDecomposition.symm
        (Sum.inr firstOfTwo))).componentId =
      newDottedId
  added_two_handle_component_id :
    (componentAt target.topology.formal
      (added.componentChange.targetDecomposition.symm
        (Sum.inr secondOfTwo))).componentId =
      newTwoHandleId
  local_diagram_sound :
    added.localDiagram =
      ComponentDiagram.oneTwoHopfPair newDottedId newTwoHandleId
  added_exponent_zero :
    (sourceCycle : source.DegreeTwoCycle) →
    (addedIndex : Fin 2) →
      (added.exponentTransport sourceCycle).added_exponent addedIndex = 0

/-- Endpoint-bound input for creating a cancelling 1--2 pair. -/
structure OneTwoBirthEndpointMovie
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (targetClass : H2 → H2)
    (cycleTransport : CycleTransport source target targetClass) where
  added :
    AddedClosedEndpointMovie source target 2 targetClass cycleTransport
  newDottedId : String
  newTwoHandleId : String
  distinct_ids : newDottedId ≠ newTwoHandleId
  added_dotted_component_id :
    (componentAt target.topology.formal
      (added.componentChange.targetDecomposition.symm
        (Sum.inr firstOfTwo))).componentId =
      newDottedId
  added_two_handle_component_id :
    (componentAt target.topology.formal
      (added.componentChange.targetDecomposition.symm
        (Sum.inr secondOfTwo))).componentId =
      newTwoHandleId
  local_diagram_sound :
    added.localDiagram =
      ComponentDiagram.oneTwoHopfPair newDottedId newTwoHandleId
  added_exponent_zero :
    (sourceCycle : source.DegreeTwoCycle) →
    (addedIndex : Fin 2) →
      (added.exponentTransport sourceCycle).added_exponent addedIndex = 0

namespace OneTwoBirthEndpointMovie

/-- Promote the endpoint movie using the forced chain-level cycle map. -/
noncomputable def toCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    {cycleTransport : CycleTransport source target targetClass}
    (movie :
      OneTwoBirthEndpointMovie source target targetClass cycleTransport) :
    OneTwoBirthCycleGeometry source target targetClass where
  added := movie.added.toCycleGeometry
  newDottedId := movie.newDottedId
  newTwoHandleId := movie.newTwoHandleId
  distinct_ids := movie.distinct_ids
  added_dotted_component_id := movie.added_dotted_component_id
  added_two_handle_component_id := movie.added_two_handle_component_id
  local_diagram_sound := movie.local_diagram_sound
  added_exponent_zero := movie.added_exponent_zero

end OneTwoBirthEndpointMovie

namespace OneTwoBirthCycleGeometry

theorem dotted_label_sound
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthCycleGeometry source target targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin 2 → S) :
    target.labelOf 𝒞.premodular
        ((geometry.added.componentChange.labelingEquiv S).symm
          (sourceLabeling, addedLabeling))
        geometry.newDottedId =
      addedLabeling firstOfTwo := by
  rw [← geometry.added_dotted_component_id]
  simp only [componentAt]
  rw [target.labelOf_component]
  simp [AddedComponentIndexChange.labelingEquiv]

theorem two_handle_label_sound
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthCycleGeometry source target targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin 2 → S) :
    target.labelOf 𝒞.premodular
        ((geometry.added.componentChange.labelingEquiv S).symm
          (sourceLabeling, addedLabeling))
        geometry.newTwoHandleId =
      addedLabeling secondOfTwo := by
  rw [← geometry.added_two_handle_component_id]
  simp only [componentAt]
  rw [target.labelOf_component]
  simp [AddedComponentIndexChange.labelingEquiv]

theorem localWeight_eq_quantumDimensions
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle)
    (addedLabeling : Fin 2 → S) :
    (geometry.added.exponentTransport sourceCycle).localWeight
        𝒞.premodular automorphism addedLabeling =
      𝒞.premodular.quantumDimension (addedLabeling firstOfTwo) *
        𝒞.premodular.quantumDimension
          (addedLabeling secondOfTwo) := by
  classical
  unfold AddedComponentCycleExponentTransport.localWeight
  rw [Fin.prod_univ_two]
  have firstZero := geometry.added_exponent_zero sourceCycle (0 : Fin 2)
  have secondZero := geometry.added_exponent_zero sourceCycle (1 : Fin 2)
  rw [firstZero, secondZero]
  simp only [firstOfTwo, secondOfTwo,
    FusionCategoryData.automorphismScalarPower_zero, mul_one]
  congr 2 <;> apply Fin.ext <;> rfl

theorem localPairSum_eq_globalDimension
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle)
    (sourceLabeling : source.GlobalLabeling (S := S)) :
    (∑ addedLabeling : Fin 2 → S,
      (geometry.added.exponentTransport sourceCycle).localWeight
          𝒞.premodular automorphism addedLabeling *
        𝒞.premodular.toFusionCategoryData.closedScalar
          (Diagram.eval C
            (geometry.added.localDiagram.interpret
              𝒞.premodular
              (target.labelOf 𝒞.premodular
                ((geometry.added.componentChange.labelingEquiv S).symm
                  (sourceLabeling, addedLabeling)))))) =
      globalDimension 𝒞.premodular := by
  classical
  simp_rw [geometry.localWeight_eq_quantumDimensions
    𝒞.premodular automorphism sourceCycle]
  rw [geometry.local_diagram_sound]
  exact baerenzBarrett_oneTwoHopfPairSum
    𝒞 geometry.newDottedId geometry.newTwoHandleId
    geometry.distinct_ids
    (fun addedLabeling =>
      target.labelOf 𝒞.premodular
        ((geometry.added.componentChange.labelingEquiv S).symm
          (sourceLabeling, addedLabeling)))
    (fun addedLabeling =>
      geometry.dotted_label_sound
        𝒞.premodular sourceLabeling addedLabeling)
    (fun addedLabeling =>
      geometry.two_handle_label_sound
        𝒞.premodular sourceLabeling addedLabeling)

/-- The explicit-cycle numerator gains exactly one global dimension. -/
theorem cycleRawNumerator_factor
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle) :
    target.cycleRawNumerator 𝒞.premodular automorphism
        (geometry.added.cycleTransport.targetCycle sourceCycle) =
      globalDimension 𝒞.premodular *
        source.cycleRawNumerator 𝒞.premodular automorphism sourceCycle := by
  classical
  rw [target.cycleRawNumerator_eq_sum 𝒞.premodular automorphism]
  rw [source.cycleRawNumerator_eq_sum 𝒞.premodular automorphism]
  rw [geometry.added.componentChange.sum_split]
  rw [Fintype.sum_prod_type]
  calc
    _ =
      ∑ sourceLabeling,
        globalDimension 𝒞.premodular *
          (source.cycleGlobalWeight 𝒞.premodular automorphism
              sourceCycle sourceLabeling *
            𝒞.premodular.toFusionCategoryData.closedScalar
              (Diagram.eval C
                (source.termDiagram 𝒞.premodular sourceLabeling))) := by
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        calc
          _ =
            ∑ addedLabeling : Fin 2 → S,
              ((geometry.added.exponentTransport sourceCycle).localWeight
                  𝒞.premodular automorphism addedLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (geometry.added.localDiagram.interpret
                      𝒞.premodular
                      (target.labelOf 𝒞.premodular
                        ((geometry.added.componentChange.labelingEquiv S).symm
                          (sourceLabeling, addedLabeling)))))) *
              (source.cycleGlobalWeight 𝒞.premodular automorphism
                  sourceCycle sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞.premodular sourceLabeling))) := by
              apply Finset.sum_congr rfl
              intro addedLabeling _
              rw [(geometry.added.exponentTransport sourceCycle)
                |>.cycleGlobalWeight_split
                  𝒞.premodular automorphism sourceLabeling addedLabeling]
              rw [geometry.added.term_closedScalar_split
                𝒞.premodular sourceLabeling addedLabeling]
              ring
          _ =
            globalDimension 𝒞.premodular *
              (source.cycleGlobalWeight 𝒞.premodular automorphism
                  sourceCycle sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞.premodular sourceLabeling))) := by
              rw [← Finset.sum_mul,
                geometry.localPairSum_eq_globalDimension
                  𝒞 automorphism sourceCycle sourceLabeling]
    _ = _ := by
      rw [Finset.mul_sum]

end OneTwoBirthCycleGeometry

/-- Cycle-safe insertion geometry for a cancelling 2--3 pair. -/
structure TwoThreeBirthCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (targetClass : H2 → H2) where
  added : AddedClosedCycleGeometry source target 1 targetClass
  newTwoHandleId : String
  added_component_id :
    (componentAt target.topology.formal
      (added.componentChange.targetDecomposition.symm
        (Sum.inr onlyOne))).componentId =
      newTwoHandleId
  local_diagram_sound :
    added.localDiagram =
      ComponentDiagram.zeroFramedUnknot newTwoHandleId
  added_exponent_zero :
    (sourceCycle : source.DegreeTwoCycle) →
      (added.exponentTransport sourceCycle).added_exponent onlyOne = 0

/-- Endpoint-bound input for creating a cancelling 2--3 pair. -/
structure TwoThreeBirthEndpointMovie
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (targetClass : H2 → H2)
    (cycleTransport : CycleTransport source target targetClass) where
  added :
    AddedClosedEndpointMovie source target 1 targetClass cycleTransport
  newTwoHandleId : String
  added_component_id :
    (componentAt target.topology.formal
      (added.componentChange.targetDecomposition.symm
        (Sum.inr onlyOne))).componentId =
      newTwoHandleId
  local_diagram_sound :
    added.localDiagram =
      ComponentDiagram.zeroFramedUnknot newTwoHandleId
  added_exponent_zero :
    (sourceCycle : source.DegreeTwoCycle) →
      (added.exponentTransport sourceCycle).added_exponent onlyOne = 0

namespace TwoThreeBirthEndpointMovie

/-- Promote the endpoint movie using the forced chain-level cycle map. -/
noncomputable def toCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    {cycleTransport : CycleTransport source target targetClass}
    (movie :
      TwoThreeBirthEndpointMovie source target targetClass cycleTransport) :
    TwoThreeBirthCycleGeometry source target targetClass where
  added := movie.added.toCycleGeometry
  newTwoHandleId := movie.newTwoHandleId
  added_component_id := movie.added_component_id
  local_diagram_sound := movie.local_diagram_sound
  added_exponent_zero := movie.added_exponent_zero

end TwoThreeBirthEndpointMovie

namespace TwoThreeBirthCycleGeometry

theorem added_label_sound
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : TwoThreeBirthCycleGeometry source target targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin 1 → S) :
    target.labelOf 𝒞.premodular
        ((geometry.added.componentChange.labelingEquiv S).symm
          (sourceLabeling, addedLabeling))
        geometry.newTwoHandleId =
      addedLabeling onlyOne := by
  rw [← geometry.added_component_id]
  simp only [componentAt]
  rw [target.labelOf_component]
  simp [AddedComponentIndexChange.labelingEquiv]

theorem localWeight_eq_quantumDimension
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : TwoThreeBirthCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle)
    (addedLabeling : Fin 1 → S) :
    (geometry.added.exponentTransport sourceCycle).localWeight
        𝒞 automorphism addedLabeling =
      𝒞.premodular.quantumDimension (addedLabeling onlyOne) := by
  classical
  unfold AddedComponentCycleExponentTransport.localWeight
  rw [Fintype.prod_unique]
  have exponentZero := geometry.added_exponent_zero sourceCycle
  simpa only [Subsingleton.elim (default : Fin 1) onlyOne,
    exponentZero,
    FusionCategoryData.automorphismScalarPower_zero, mul_one]

theorem localDiagram_closedScalar_eq_quantumDimension
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : TwoThreeBirthCycleGeometry source target targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin 1 → S) :
    𝒞.premodular.toFusionCategoryData.closedScalar
        (Diagram.eval C
          (geometry.added.localDiagram.interpret 𝒞.premodular
            (target.labelOf 𝒞.premodular
              ((geometry.added.componentChange.labelingEquiv S).symm
                (sourceLabeling, addedLabeling))))) =
      𝒞.premodular.quantumDimension
        (addedLabeling onlyOne) := by
  rw [geometry.local_diagram_sound]
  rw [ComponentDiagram.zeroFramedUnknot_closedScalar]
  rw [geometry.added_label_sound 𝒞 sourceLabeling addedLabeling]

/-- The explicit-cycle numerator gains exactly one global dimension. -/
theorem cycleRawNumerator_factor
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : TwoThreeBirthCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle) :
    target.cycleRawNumerator 𝒞.premodular automorphism
        (geometry.added.cycleTransport.targetCycle sourceCycle) =
      globalDimension 𝒞.premodular *
        source.cycleRawNumerator 𝒞.premodular automorphism sourceCycle := by
  classical
  rw [target.cycleRawNumerator_eq_sum 𝒞.premodular automorphism]
  rw [source.cycleRawNumerator_eq_sum 𝒞.premodular automorphism]
  rw [geometry.added.componentChange.sum_split]
  rw [Fintype.sum_prod_type]
  have addedSum :
      (∑ addedLabeling : Fin 1 → S,
        𝒞.premodular.quantumDimension (addedLabeling onlyOne) *
          𝒞.premodular.quantumDimension (addedLabeling onlyOne)) =
        globalDimension 𝒞.premodular := by
    simpa only [globalDimension,
      Subsingleton.elim (default : Fin 1) onlyOne] using
      Equiv.sum_comp (Equiv.funUnique (Fin 1) S)
        (fun simple =>
          𝒞.premodular.quantumDimension simple *
            𝒞.premodular.quantumDimension simple)
  calc
    _ =
      ∑ sourceLabeling,
        globalDimension 𝒞.premodular *
          (source.cycleGlobalWeight 𝒞.premodular automorphism
              sourceCycle sourceLabeling *
            𝒞.premodular.toFusionCategoryData.closedScalar
              (Diagram.eval C
                (source.termDiagram 𝒞.premodular sourceLabeling))) := by
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        calc
          _ =
            ∑ addedLabeling : Fin 1 → S,
              (𝒞.premodular.quantumDimension (addedLabeling onlyOne) *
                𝒞.premodular.quantumDimension (addedLabeling onlyOne)) *
              (source.cycleGlobalWeight 𝒞.premodular automorphism
                  sourceCycle sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞.premodular sourceLabeling))) := by
              apply Finset.sum_congr rfl
              intro addedLabeling _
              rw [(geometry.added.exponentTransport sourceCycle)
                |>.cycleGlobalWeight_split
                  𝒞 automorphism sourceLabeling addedLabeling]
              rw [geometry.localWeight_eq_quantumDimension
                𝒞 automorphism sourceCycle addedLabeling]
              rw [geometry.added.term_closedScalar_split
                𝒞 sourceLabeling addedLabeling]
              rw [geometry.localDiagram_closedScalar_eq_quantumDimension
                𝒞 sourceLabeling addedLabeling]
              ring
          _ =
            globalDimension 𝒞.premodular *
              (source.cycleGlobalWeight 𝒞.premodular automorphism
                  sourceCycle sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞.premodular sourceLabeling))) := by
              rw [← Finset.sum_mul, addedSum]
    _ = _ := by
      rw [Finset.mul_sum]

end TwoThreeBirthCycleGeometry

/--
Cycle geometry for deleting a cancelling 1--2 pair.

The reverse birth is expressed using an inverse-class cycle transport.  No
strict equality of raw cycle representatives is required.
-/
structure OneTwoDeathCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
  (transport : MarkedH2Transport source.topology target.topology) where
  reverseBirth :
    OneTwoBirthCycleGeometry target source transport.homologyEquiv.symm

/--
Endpoint-bound deletion movie for a cancelling 1--2 pair.

Both directions use the two chain maps of the same marked equivalence.
-/
structure OneTwoDeathEndpointMovie
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (transport : MarkedH2Transport source.topology target.topology) where
  reverseBirth :
    OneTwoBirthEndpointMovie target source transport.homologyEquiv.symm
      (CycleTransport.ofMarkedH2TransportInverse source target transport)

namespace OneTwoDeathEndpointMovie

/-- Promote the two endpoint-bound directions to complete death geometry. -/
noncomputable def toCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {transport : MarkedH2Transport source.topology target.topology}
    (movie : OneTwoDeathEndpointMovie source target transport) :
    OneTwoDeathCycleGeometry source target transport where
  reverseBirth := movie.reverseBirth.toCycleGeometry

end OneTwoDeathEndpointMovie

/--
Cycle geometry for deleting a cancelling 2--3 pair, with the same strict
cycle-retraction requirement.
-/
structure TwoThreeDeathCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
  (transport : MarkedH2Transport source.topology target.topology) where
  reverseBirth :
    TwoThreeBirthCycleGeometry target source transport.homologyEquiv.symm

/-- Endpoint-bound deletion movie for a cancelling 2--3 pair. -/
structure TwoThreeDeathEndpointMovie
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (transport : MarkedH2Transport source.topology target.topology) where
  reverseBirth :
    TwoThreeBirthEndpointMovie target source transport.homologyEquiv.symm
      (CycleTransport.ofMarkedH2TransportInverse source target transport)

namespace TwoThreeDeathEndpointMovie

/-- Promote the two endpoint-bound directions to complete death geometry. -/
noncomputable def toCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {transport : MarkedH2Transport source.topology target.topology}
    (movie : TwoThreeDeathEndpointMovie source target transport) :
    TwoThreeDeathCycleGeometry source target transport where
  reverseBirth := movie.reverseBirth.toCycleGeometry

end TwoThreeDeathEndpointMovie

end TwistedYetter.Kirby.CanonicalCycleMoveGeometry
