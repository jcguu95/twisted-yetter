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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
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

end CycleTransport

/-- Exact exponent transport for one pair of explicit cycles. -/
structure SameComponentCycleExponentTransport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation manifold H2}
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {sourceCycle : source.DegreeTwoCycle}
    {targetCycle : target.DegreeTwoCycle}
    (transport :
      SameComponentCycleExponentTransport
        source target change sourceCycle targetCycle)
    (sourceLabeling : source.GlobalLabeling (S := S)) :
    source.cycleGlobalWeight 𝒞 automorphism sourceCycle sourceLabeling =
      target.cycleGlobalWeight 𝒞 automorphism targetCycle
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
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

namespace FramedIsotopyCycleGeometry

/-- A cycle-safe framed isotopy preserves the complete linear sum. -/
theorem cycleLinearDiagram_eval_transport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation manifold H2}
    {targetClass : H2 → H2}
    (geometry :
      FramedIsotopyCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle) :
    LinearDiagram.eval
        (source.cycleLinearDiagram 𝒞 automorphism sourceCycle) =
      LinearDiagram.eval
        (target.cycleLinearDiagram 𝒞 automorphism
          (geometry.cycleTransport.targetCycle sourceCycle)) := by
  classical
  rw [source.cycleLinearDiagram_eval 𝒞 automorphism sourceCycle]
  rw [target.cycleLinearDiagram_eval 𝒞 automorphism
    (geometry.cycleTransport.targetCycle sourceCycle)]
  rw [← geometry.componentChange.sum_reindex
    (fun targetLabeling =>
      target.cycleGlobalWeight 𝒞 automorphism
          (geometry.cycleTransport.targetCycle sourceCycle) targetLabeling •
        Diagram.eval C (target.termDiagram 𝒞 targetLabeling))]
  apply Finset.sum_congr rfl
  intro sourceLabeling _
  rw [SameComponentCycleExponentTransport.cycleGlobalWeight_transport
    𝒞 automorphism geometry.componentChange
    (geometry.exponentTransport sourceCycle) sourceLabeling]
  have termEval :
      Diagram.eval C (source.termDiagram 𝒞 sourceLabeling) =
        Diagram.eval C
          (target.termDiagram 𝒞
            (geometry.componentChange.labelingEquiv S sourceLabeling)) := by
    have labels :
        target.labelOf 𝒞
            (geometry.componentChange.labelingEquiv S sourceLabeling) =
          source.labelOf 𝒞 sourceLabeling := by
      funext componentId
      exact
        CanonicalMoveGeometry.SameComponentIndexChange.labelOf_transport
          𝒞 source target geometry.componentChange
          sourceLabeling componentId
    unfold CanonicalPresentation.termDiagram
    rw [labels]
    exact geometry.termIsotopy.eval_eq
      𝒞 (source.labelOf 𝒞 sourceLabeling)
  exact congrArg
    (fun value =>
      target.cycleGlobalWeight 𝒞 automorphism
          (geometry.cycleTransport.targetCycle sourceCycle)
          (geometry.componentChange.labelingEquiv S sourceLabeling) • value)
    termEval

end FramedIsotopyCycleGeometry

/-- Exact exponent transport when the target has a finite local summand. -/
structure AddedComponentCycleExponentTransport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation manifold H2}
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation manifold H2}
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
    target.cycleGlobalWeight 𝒞 automorphism targetCycle
        ((change.labelingEquiv S).symm
          (sourceLabeling, addedLabeling)) =
      source.cycleGlobalWeight 𝒞 automorphism sourceCycle sourceLabeling *
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
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
  diagram_factorization :
    target.componentTermDiagram =
      ComponentDiagram.closedTensor
        localDiagram source.componentTermDiagram
  source_component_support :
    (componentId : String) →
    componentId ∈ source.componentTermDiagram.componentIds →
      ∃ sourceIndex : ComponentIndex source.topology.formal,
        componentId =
          (componentAt source.topology.formal sourceIndex).componentId

namespace AddedClosedCycleGeometry

/-- The retained source term uses exactly the original source labels. -/
theorem source_term_eval_transport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation manifold H2}
    {addedCount : Nat}
    {targetClass : H2 → H2}
    (geometry :
      AddedClosedCycleGeometry source target addedCount targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin addedCount → S) :
    Diagram.eval C
        (source.componentTermDiagram.interpret 𝒞.premodular
          (target.labelOf 𝒞
            ((geometry.componentChange.labelingEquiv S).symm
              (sourceLabeling, addedLabeling)))) =
      Diagram.eval C
        (source.componentTermDiagram.interpret 𝒞.premodular
          (source.labelOf 𝒞 sourceLabeling)) := by
  apply ComponentDiagram.eval_interpret_eq_of_eq_on_componentIds
  intro componentId membership
  obtain ⟨sourceIndex, componentIdEq⟩ :=
    geometry.source_component_support componentId membership
  subst componentId
  rw [AddedComponentIndexChange.labelOf_common]
  exact (source.labelOf_component 𝒞 sourceLabeling sourceIndex).symm

/-- The target closed term scalar splits into local and retained factors. -/
theorem term_closedScalar_split
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation manifold H2}
    {addedCount : Nat}
    {targetClass : H2 → H2}
    (geometry :
      AddedClosedCycleGeometry source target addedCount targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin addedCount → S) :
    𝒞.premodular.toFusionCategoryData.closedScalar
        (Diagram.eval C
          (target.termDiagram 𝒞
            ((geometry.componentChange.labelingEquiv S).symm
              (sourceLabeling, addedLabeling)))) =
      𝒞.premodular.toFusionCategoryData.closedScalar
          (Diagram.eval C
            (geometry.localDiagram.interpret 𝒞.premodular
              (target.labelOf 𝒞
                ((geometry.componentChange.labelingEquiv S).symm
                  (sourceLabeling, addedLabeling))))) *
        𝒞.premodular.toFusionCategoryData.closedScalar
          (Diagram.eval C
            (source.termDiagram 𝒞 sourceLabeling)) := by
  let targetLabelOf :=
    target.labelOf 𝒞
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
  rw [geometry.diagram_factorization]
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
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

namespace OneTwoBirthCycleGeometry

theorem dotted_label_sound
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation manifold H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthCycleGeometry source target targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin 2 → S) :
    target.labelOf 𝒞
        ((geometry.added.componentChange.labelingEquiv S).symm
          (sourceLabeling, addedLabeling))
        geometry.newDottedId =
      addedLabeling firstOfTwo := by
  rw [← geometry.added_dotted_component_id]
  simp only [componentAt]
  rw [target.labelOf_component]
  simp [AddedComponentIndexChange.labelingEquiv]

theorem two_handle_label_sound
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation manifold H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthCycleGeometry source target targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin 2 → S) :
    target.labelOf 𝒞
        ((geometry.added.componentChange.labelingEquiv S).symm
          (sourceLabeling, addedLabeling))
        geometry.newTwoHandleId =
      addedLabeling secondOfTwo := by
  rw [← geometry.added_two_handle_component_id]
  simp only [componentAt]
  rw [target.labelOf_component]
  simp [AddedComponentIndexChange.labelingEquiv]

theorem localWeight_eq_quantumDimensions
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation manifold H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle)
    (addedLabeling : Fin 2 → S) :
    (geometry.added.exponentTransport sourceCycle).localWeight
        𝒞 automorphism addedLabeling =
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation manifold H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle)
    (sourceLabeling : source.GlobalLabeling (S := S)) :
    (∑ addedLabeling : Fin 2 → S,
      (geometry.added.exponentTransport sourceCycle).localWeight
          𝒞 automorphism addedLabeling *
        𝒞.premodular.toFusionCategoryData.closedScalar
          (Diagram.eval C
            (geometry.added.localDiagram.interpret
              𝒞.premodular
              (target.labelOf 𝒞
                ((geometry.added.componentChange.labelingEquiv S).symm
                  (sourceLabeling, addedLabeling)))))) =
      globalDimension 𝒞.premodular := by
  classical
  simp_rw [geometry.localWeight_eq_quantumDimensions
    𝒞 automorphism sourceCycle]
  rw [geometry.local_diagram_sound]
  exact baerenzBarrett_oneTwoHopfPairSum
    𝒞 geometry.newDottedId geometry.newTwoHandleId
    geometry.distinct_ids
    (fun addedLabeling =>
      target.labelOf 𝒞
        ((geometry.added.componentChange.labelingEquiv S).symm
          (sourceLabeling, addedLabeling)))
    (fun addedLabeling =>
      geometry.dotted_label_sound 𝒞 sourceLabeling addedLabeling)
    (fun addedLabeling =>
      geometry.two_handle_label_sound 𝒞 sourceLabeling addedLabeling)

/-- The explicit-cycle numerator gains exactly one global dimension. -/
theorem cycleRawNumerator_factor
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation manifold H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle) :
    target.cycleRawNumerator 𝒞 automorphism
        (geometry.added.cycleTransport.targetCycle sourceCycle) =
      globalDimension 𝒞.premodular *
        source.cycleRawNumerator 𝒞 automorphism sourceCycle := by
  classical
  rw [target.cycleRawNumerator_eq_sum 𝒞 automorphism]
  rw [source.cycleRawNumerator_eq_sum 𝒞 automorphism]
  rw [geometry.added.componentChange.sum_split]
  rw [Fintype.sum_prod_type]
  calc
    _ =
      ∑ sourceLabeling,
        globalDimension 𝒞.premodular *
          (source.cycleGlobalWeight 𝒞 automorphism
              sourceCycle sourceLabeling *
            𝒞.premodular.toFusionCategoryData.closedScalar
              (Diagram.eval C
                (source.termDiagram 𝒞 sourceLabeling))) := by
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        calc
          _ =
            ∑ addedLabeling : Fin 2 → S,
              ((geometry.added.exponentTransport sourceCycle).localWeight
                  𝒞 automorphism addedLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (geometry.added.localDiagram.interpret
                      𝒞.premodular
                      (target.labelOf 𝒞
                        ((geometry.added.componentChange.labelingEquiv S).symm
                          (sourceLabeling, addedLabeling)))))) *
              (source.cycleGlobalWeight 𝒞 automorphism
                  sourceCycle sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞 sourceLabeling))) := by
              apply Finset.sum_congr rfl
              intro addedLabeling _
              rw [(geometry.added.exponentTransport sourceCycle)
                |>.cycleGlobalWeight_split
                  𝒞 automorphism sourceLabeling addedLabeling]
              rw [geometry.added.term_closedScalar_split
                𝒞 sourceLabeling addedLabeling]
              ring
          _ =
            globalDimension 𝒞.premodular *
              (source.cycleGlobalWeight 𝒞 automorphism
                  sourceCycle sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞 sourceLabeling))) := by
              rw [← Finset.sum_mul,
                geometry.localPairSum_eq_globalDimension
                  𝒞 automorphism sourceCycle sourceLabeling]
    _ = _ := by
      rw [Finset.mul_sum]

end OneTwoBirthCycleGeometry

/-- Cycle-safe insertion geometry for a cancelling 2--3 pair. -/
structure TwoThreeBirthCycleGeometry
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
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

namespace TwoThreeBirthCycleGeometry

theorem added_label_sound
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation manifold H2}
    {targetClass : H2 → H2}
    (geometry : TwoThreeBirthCycleGeometry source target targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin 1 → S) :
    target.labelOf 𝒞
        ((geometry.added.componentChange.labelingEquiv S).symm
          (sourceLabeling, addedLabeling))
        geometry.newTwoHandleId =
      addedLabeling onlyOne := by
  rw [← geometry.added_component_id]
  simp only [componentAt]
  rw [target.labelOf_component]
  simp [AddedComponentIndexChange.labelingEquiv]

theorem localWeight_eq_quantumDimension
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation manifold H2}
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation manifold H2}
    {targetClass : H2 → H2}
    (geometry : TwoThreeBirthCycleGeometry source target targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin 1 → S) :
    𝒞.premodular.toFusionCategoryData.closedScalar
        (Diagram.eval C
          (geometry.added.localDiagram.interpret 𝒞.premodular
            (target.labelOf 𝒞
              ((geometry.added.componentChange.labelingEquiv S).symm
                (sourceLabeling, addedLabeling))))) =
      𝒞.premodular.quantumDimension
        (addedLabeling onlyOne) := by
  rw [geometry.local_diagram_sound]
  rw [ComponentDiagram.zeroFramedUnknot_closedScalar]
  rw [geometry.added_label_sound 𝒞 sourceLabeling addedLabeling]

/-- The explicit-cycle numerator gains exactly one global dimension. -/
theorem cycleRawNumerator_factor
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation manifold H2}
    {targetClass : H2 → H2}
    (geometry : TwoThreeBirthCycleGeometry source target targetClass)
    (sourceCycle : source.DegreeTwoCycle) :
    target.cycleRawNumerator 𝒞 automorphism
        (geometry.added.cycleTransport.targetCycle sourceCycle) =
      globalDimension 𝒞.premodular *
        source.cycleRawNumerator 𝒞 automorphism sourceCycle := by
  classical
  rw [target.cycleRawNumerator_eq_sum 𝒞 automorphism]
  rw [source.cycleRawNumerator_eq_sum 𝒞 automorphism]
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
          (source.cycleGlobalWeight 𝒞 automorphism
              sourceCycle sourceLabeling *
            𝒞.premodular.toFusionCategoryData.closedScalar
              (Diagram.eval C
                (source.termDiagram 𝒞 sourceLabeling))) := by
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        calc
          _ =
            ∑ addedLabeling : Fin 1 → S,
              (𝒞.premodular.quantumDimension (addedLabeling onlyOne) *
                𝒞.premodular.quantumDimension (addedLabeling onlyOne)) *
              (source.cycleGlobalWeight 𝒞 automorphism
                  sourceCycle sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞 sourceLabeling))) := by
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
              (source.cycleGlobalWeight 𝒞 automorphism
                  sourceCycle sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞 sourceLabeling))) := by
              rw [← Finset.sum_mul, addedSum]
    _ = _ := by
      rw [Finset.mul_sum]

end TwoThreeBirthCycleGeometry

/--
Cycle geometry for deleting a cancelling 1--2 pair.

The reverse birth is not enough by itself: the forward deletion must be a
strict left inverse on the cycles produced by that reverse birth.  This is
the exact no-hidden-coefficient law needed for arbitrary-H2 cancellation.
-/
structure OneTwoDeathCycleGeometry
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
    (transport : MarkedH2Transport source.topology target.topology) where
  reverseBirth :
    OneTwoBirthCycleGeometry target source transport.homologyEquiv.symm
  forward_reverse_cycle :
    (targetCycleValue : target.DegreeTwoCycle) →
      (CycleTransport.ofMarkedH2Transport source target transport).targetCycle
          (reverseBirth.added.cycleTransport.targetCycle targetCycleValue) =
        targetCycleValue

/--
Cycle geometry for deleting a cancelling 2--3 pair, with the same strict
cycle-retraction requirement.
-/
structure TwoThreeDeathCycleGeometry
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
    (transport : MarkedH2Transport source.topology target.topology) where
  reverseBirth :
    TwoThreeBirthCycleGeometry target source transport.homologyEquiv.symm
  forward_reverse_cycle :
    (targetCycleValue : target.DegreeTwoCycle) →
      (CycleTransport.ofMarkedH2Transport source target transport).targetCycle
          (reverseBirth.added.cycleTransport.targetCycle targetCycleValue) =
        targetCycleValue

end TwistedYetter.Kirby.CanonicalCycleMoveGeometry
