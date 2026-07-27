import Mathlib.Data.Fintype.BigOperators
import TwistedYetter.Kirby.CanonicalComponentSupport
import TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
import TwistedYetter.Kirby.ComponentRibbonIsotopy
import TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

/-!
# Category-neutral geometry for canonical Kirby moves

This module binds the free component diagrams and the finite global-label
denominators used by the canonical evaluator.

The structures below contain only:

* finite component-index equivalences;
* integer exponent transport;
* exact equalities between free component diagrams; and
* generated free framed-isotopy proof terms.

They contain no category object, category morphism, scalar evaluation, or
equality of scalar evaluations.  Their interpretation in a modular category
is proved later.
-/

namespace TwistedYetter.Kirby.CanonicalMoveGeometry

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.ComponentRibbonIsotopy
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.EGNOModularKirbyMoves.LiteratureBackedModularGraphicalEnvironment
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
The exact source and target trace windows selected by one serialized local
rewrite.

Both sides are computed from the canonical closed traces.  In particular,
the caller cannot supply a second, unrelated replay whose event list merely
has the right length or component names.
-/
structure SourceBoundTraceWindow
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (window :
      PresentationWindowEdit
        source.topology.formal target.topology.formal) where
  sourceSplit :
    CanonicalKirbyTrace.Trace.ThreeWaySplit
      (raw := source.topology.formal.raw)
      (initial := []) (final := [])
      window.commonEventPrefix
      window.sourceEventWindow
      window.commonEventSuffix
  targetSplit :
    CanonicalKirbyTrace.Trace.ThreeWaySplit
      (raw := target.topology.formal.raw)
      (initial := []) (final := [])
      window.commonEventPrefix
      window.targetEventWindow
      window.commonEventSuffix
  source_whole_diagram_sound :
    ComponentRibbonDiagram.Trace.componentDiagram sourceSplit.wholeTrace =
      source.componentTermDiagram
  target_whole_diagram_sound :
    ComponentRibbonDiagram.Trace.componentDiagram targetSplit.wholeTrace =
      target.componentTermDiagram
  source_declared_slices_sound :
    source.topology.formal.raw.declaredSlices =
      Presentation.RawPresentation.declareSlicesFrom 0
        sourceSplit.wholeTrace.toExecutionTrace.states
  target_declared_slices_sound :
    target.topology.formal.raw.declaredSlices =
      Presentation.RawPresentation.declareSlicesFrom 0
        targetSplit.wholeTrace.toExecutionTrace.states

namespace SourceBoundTraceWindow

/-- Split both admitted canonical traces at the exact recipe-owned windows. -/
def ofPresentationWindow
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (window :
      PresentationWindowEdit
        source.topology.formal target.topology.formal) :
    SourceBoundTraceWindow source target window := by
  let sourceTrace :
      CanonicalKirbyTrace.Trace source.topology.formal.raw
        (window.commonEventPrefix ++ window.sourceEventWindow ++
          window.commonEventSuffix) [] [] :=
    window.source_events_sound ▸ source.canonicalTrace.trace
  let targetTrace :
      CanonicalKirbyTrace.Trace target.topology.formal.raw
        (window.commonEventPrefix ++ window.targetEventWindow ++
          window.commonEventSuffix) [] [] :=
    window.target_events_sound ▸ target.canonicalTrace.trace
  let sourceSplit :=
    CanonicalKirbyTrace.Trace.splitThree
      window.commonEventPrefix window.sourceEventWindow
      window.commonEventSuffix sourceTrace
  let targetSplit :=
    CanonicalKirbyTrace.Trace.splitThree
      window.commonEventPrefix window.targetEventWindow
      window.commonEventSuffix targetTrace
  refine
    { sourceSplit := sourceSplit
      targetSplit := targetSplit
      source_whole_diagram_sound := ?_
      target_whole_diagram_sound := ?_
      source_declared_slices_sound := ?_
      target_declared_slices_sound := ?_ }
  · change
      ComponentRibbonDiagram.Trace.componentDiagram sourceTrace =
        source.componentTermDiagram
    simpa only [sourceTrace, CanonicalPresentation.componentTermDiagram] using
      ComponentRibbonDiagram.Trace.componentDiagram_transport_events
        window.source_events_sound source.canonicalTrace.trace
  · change
      ComponentRibbonDiagram.Trace.componentDiagram targetTrace =
        target.componentTermDiagram
    simpa only [targetTrace, CanonicalPresentation.componentTermDiagram] using
      ComponentRibbonDiagram.Trace.componentDiagram_transport_events
        window.target_events_sound target.canonicalTrace.trace
  · change
      source.topology.formal.raw.declaredSlices =
        Presentation.RawPresentation.declareSlicesFrom 0
          sourceTrace.toExecutionTrace.states
    rw [CanonicalKirbyTrace.Trace.toExecutionTrace_states_transport_events
      window.source_events_sound source.canonicalTrace.trace]
    exact source.canonicalTrace.declared_slices_sound
  · change
      target.topology.formal.raw.declaredSlices =
        Presentation.RawPresentation.declareSlicesFrom 0
          targetTrace.toExecutionTrace.states
    rw [CanonicalKirbyTrace.Trace.toExecutionTrace_states_transport_events
      window.target_events_sound target.canonicalTrace.trace]
    exact target.canonicalTrace.declared_slices_sound

end SourceBoundTraceWindow

namespace SameComponentIndexChange

/--
Transporting a global labeling along an exact component correspondence
preserves the label selected by every component ID.

The proof also covers IDs absent from both registries: both canonical
evaluators then select the tensor-unit label.
-/
theorem labelOf_transport
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (source target : CanonicalPresentation H2)
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (componentId : String) :
    target.labelOf 𝒞.premodular
        (change.labelingEquiv S sourceLabeling) componentId =
      source.labelOf 𝒞.premodular sourceLabeling componentId := by
  unfold CanonicalPresentation.labelOf
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
      simp only [targetLookup, sourceLookup, SameComponentIndexChange.labelingEquiv,
        Equiv.coe_fn_mk, Function.comp_apply]
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

end SameComponentIndexChange

/--
Exact integer-coordinate transport for a move with unchanged components.

This is category-neutral.  It says how the chosen degree-two cycle
coordinates move; it does not assert anything about a category, a diagram
evaluation, or a final invariant.
-/
structure SameComponentExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    (targetClass : H2 → H2) where
  exponent_sound :
    (alpha : H2) →
    (targetIndex :
      ComponentIndex target.topology.formal) →
      target.cycleComponentExponent
          (target.chosenCycle
            (target.topology.h2ModelEquiv.symm (targetClass alpha)))
          (componentAt target.topology.formal targetIndex) =
        source.cycleComponentExponent
          (source.chosenCycle
            (source.topology.h2ModelEquiv.symm alpha))
          (componentAt source.topology.formal
            (change.targetToSource targetIndex))

namespace SameComponentExponentTransport

/--
The complete component coefficient is preserved by an exact common-component
and exponent transport.

This lemma is independent of which graphical move is later placed between
the two endpoint diagrams.
-/
theorem cycleGlobalWeight_transport
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism :
      TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    {targetClass : H2 → H2}
    (transport :
      SameComponentExponentTransport
        source target change targetClass)
    (alpha : H2)
    (sourceLabeling : source.GlobalLabeling (S := S)) :
    source.cycleGlobalWeight 𝒞.premodular automorphism
        (source.chosenCycle
          (source.topology.h2ModelEquiv.symm alpha)) sourceLabeling =
      target.cycleGlobalWeight 𝒞.premodular automorphism
        (target.chosenCycle
          (target.topology.h2ModelEquiv.symm (targetClass alpha)))
        (change.labelingEquiv S sourceLabeling) := by
  classical
  unfold CanonicalPresentation.cycleGlobalWeight
  symm
  apply Fintype.prod_equiv change.targetToSource
  intro targetIndex
  simp only [CanonicalPresentation.cycleComponentWeight]
  have exponentSound :=
    transport.exponent_sound alpha targetIndex
  simp only [componentAt] at exponentSound
  rw [exponentSound]
  simp only [SameComponentIndexChange.labelingEquiv,
    Equiv.coe_fn_mk, Function.comp_apply]

end SameComponentExponentTransport

/--
Complete category-neutral framed-isotopy geometry between two canonical
presentations.

The diagram proof is checked in the free ribbon grammar.  Component labels
and cycle exponents are transported separately, preventing a graphical proof
from silently changing the finite Kirby-colour denominator.
-/
structure FramedIsotopyGeometry
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (targetClass : H2 → H2) where
  componentChange :
    SameComponentIndexChange
      source.topology.formal target.topology.formal
  exponentTransport :
    SameComponentExponentTransport
      source target componentChange targetClass
  termIsotopy :
    GeneratedIsotopy
      source.componentTermDiagram target.componentTermDiagram

namespace FramedIsotopyGeometry

/-- The component-product coefficient is preserved term by term. -/
theorem cycleGlobalWeight_transport
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism :
      TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry :
      FramedIsotopyGeometry source target targetClass)
    (alpha : H2)
    (sourceLabeling : source.GlobalLabeling (S := S)) :
    source.cycleGlobalWeight 𝒞.premodular automorphism
        (source.chosenCycle
          (source.topology.h2ModelEquiv.symm alpha)) sourceLabeling =
      target.cycleGlobalWeight 𝒞.premodular automorphism
        (target.chosenCycle
          (target.topology.h2ModelEquiv.symm (targetClass alpha)))
        (geometry.componentChange.labelingEquiv S sourceLabeling) := by
  exact
    SameComponentExponentTransport.cycleGlobalWeight_transport
      𝒞 automorphism geometry.componentChange
      geometry.exponentTransport alpha sourceLabeling

/-- Each globally labeled closed term has the same categorical evaluation. -/
theorem termDiagram_eval_transport
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry :
      FramedIsotopyGeometry source target targetClass)
    (sourceLabeling : source.GlobalLabeling (S := S)) :
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
        𝒞 source target geometry.componentChange sourceLabeling componentId
  unfold CanonicalPresentation.termDiagram
  rw [labels]
  exact geometry.termIsotopy.eval_eq
    𝒞 (source.labelOf 𝒞.premodular sourceLabeling)

/--
The complete formal Kirby-colour sum is preserved by a certified framed
isotopy.
-/
theorem linearDiagram_eval_transport
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism :
      TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry :
      FramedIsotopyGeometry source target targetClass)
    (alpha : H2) :
    LinearDiagram.eval
        (source.linearDiagram 𝒞 automorphism
          (source.topology.h2ModelEquiv.symm alpha)) =
      LinearDiagram.eval
        (target.linearDiagram 𝒞 automorphism
          (target.topology.h2ModelEquiv.symm (targetClass alpha))) := by
  classical
  rw [source.linearDiagram_eval 𝒞 automorphism
    (source.topology.h2ModelEquiv.symm alpha)]
  rw [target.linearDiagram_eval 𝒞 automorphism
    (target.topology.h2ModelEquiv.symm (targetClass alpha))]
  rw [← geometry.componentChange.sum_reindex
    (fun targetLabeling =>
      target.cycleGlobalWeight 𝒞.premodular automorphism
          (target.chosenCycle
            (target.topology.h2ModelEquiv.symm (targetClass alpha)))
          targetLabeling •
        Diagram.eval C (target.termDiagram 𝒞.premodular targetLabeling))]
  apply Finset.sum_congr rfl
  intro sourceLabeling _
  rw [geometry.cycleGlobalWeight_transport
    𝒞 automorphism alpha sourceLabeling]
  exact congrArg
    (fun value =>
      target.cycleGlobalWeight 𝒞.premodular automorphism
          (target.chosenCycle
            (target.topology.h2ModelEquiv.symm (targetClass alpha)))
          (geometry.componentChange.labelingEquiv S sourceLabeling) • value)
    (geometry.termDiagram_eval_transport 𝒞 sourceLabeling)

end FramedIsotopyGeometry

namespace AddedComponentIndexChange

/-- A reconstructed target labeling agrees with the source on common IDs. -/
theorem labelOf_common
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (source target : CanonicalPresentation H2)
    {addedCount : Nat}
    (change :
      AddedComponentIndexChange
        source.topology.formal target.topology.formal addedCount)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin addedCount → S)
    (sourceIndex : ComponentIndex source.topology.formal) :
    target.labelOf 𝒞.premodular
        ((change.labelingEquiv S).symm
          (sourceLabeling, addedLabeling))
        (componentAt source.topology.formal sourceIndex).componentId =
      sourceLabeling sourceIndex := by
  let targetIndex :=
    change.targetDecomposition.symm (Sum.inl sourceIndex)
  calc
    target.labelOf 𝒞.premodular
          ((change.labelingEquiv S).symm
            (sourceLabeling, addedLabeling))
          (componentAt source.topology.formal sourceIndex).componentId =
        target.labelOf 𝒞.premodular
          ((change.labelingEquiv S).symm
            (sourceLabeling, addedLabeling))
          (componentAt target.topology.formal targetIndex).componentId := by
            rw [change.common_component_id_sound sourceIndex]
    _ =
        ((change.labelingEquiv S).symm
          (sourceLabeling, addedLabeling)) targetIndex :=
      target.labelOf_component 𝒞.premodular _ targetIndex
    _ = sourceLabeling sourceIndex := by
      simp [targetIndex, AddedComponentIndexChange.labelingEquiv]

end AddedComponentIndexChange

/-- Integer exponent transport for insertion of local components. -/
structure AddedComponentExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    {addedCount : Nat}
    (change :
      AddedComponentIndexChange
        source.topology.formal target.topology.formal addedCount)
    (targetClass : H2 → H2) where
  common_exponent_sound :
    (alpha : H2) →
    (sourceIndex : ComponentIndex source.topology.formal) →
      target.cycleComponentExponent
          (target.chosenCycle
            (target.topology.h2ModelEquiv.symm (targetClass alpha)))
          (componentAt target.topology.formal
            (change.targetDecomposition.symm
              (Sum.inl sourceIndex))) =
        source.cycleComponentExponent
          (source.chosenCycle
            (source.topology.h2ModelEquiv.symm alpha))
          (componentAt source.topology.formal sourceIndex)
  added_exponent :
    (alpha : H2) →
    Fin addedCount → ℤ
  added_exponent_sound :
    (alpha : H2) →
    (addedIndex : Fin addedCount) →
      target.cycleComponentExponent
          (target.chosenCycle
            (target.topology.h2ModelEquiv.symm (targetClass alpha)))
          (componentAt target.topology.formal
            (change.targetDecomposition.symm
              (Sum.inr addedIndex))) =
        added_exponent alpha addedIndex

namespace AddedComponentExponentTransport

/-- The exact coefficient contributed by the newly inserted components. -/
noncomputable def localWeight
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism :
      TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    {change :
      AddedComponentIndexChange
        source.topology.formal target.topology.formal addedCount}
    {targetClass : H2 → H2}
    (transport :
      AddedComponentExponentTransport
        source target change targetClass)
    (alpha : H2)
    (addedLabeling : Fin addedCount → S) : K :=
  ∏ addedIndex,
    𝒞.premodular.quantumDimension (addedLabeling addedIndex) *
      𝒞.premodular.toFusionCategoryData.automorphismScalarPower
        automorphism (addedLabeling addedIndex)
        (transport.added_exponent alpha addedIndex)

/--
The target component product factors into the exact common source weight and
the exact local added-component weight.
-/
theorem cycleGlobalWeight_split
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism :
      TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    {change :
      AddedComponentIndexChange
        source.topology.formal target.topology.formal addedCount}
    {targetClass : H2 → H2}
    (transport :
      AddedComponentExponentTransport
        source target change targetClass)
    (alpha : H2)
    (sourceLabeling : source.GlobalLabeling (S := S))
    (addedLabeling : Fin addedCount → S) :
    target.cycleGlobalWeight 𝒞.premodular automorphism
        (target.chosenCycle
          (target.topology.h2ModelEquiv.symm (targetClass alpha)))
        ((change.labelingEquiv S).symm
          (sourceLabeling, addedLabeling)) =
      source.cycleGlobalWeight 𝒞.premodular automorphism
          (source.chosenCycle
            (source.topology.h2ModelEquiv.symm alpha)) sourceLabeling *
        transport.localWeight 𝒞 automorphism alpha addedLabeling := by
  classical
  unfold CanonicalPresentation.cycleGlobalWeight
  rw [change.component_product_split]
  congr 1
  · apply Finset.prod_congr rfl
    intro sourceIndex _
    simp only [CanonicalPresentation.cycleComponentWeight]
    have exponentSound :=
      transport.common_exponent_sound alpha sourceIndex
    simp only [componentAt] at exponentSound
    rw [exponentSound]
    simp [AddedComponentIndexChange.labelingEquiv]
  · unfold localWeight
    apply Finset.prod_congr rfl
    intro addedIndex _
    simp only [CanonicalPresentation.cycleComponentWeight]
    change
      𝒞.premodular.quantumDimension
          (((change.labelingEquiv S).symm
            (sourceLabeling, addedLabeling))
            (change.targetDecomposition.symm
              (Sum.inr addedIndex))) *
        𝒞.premodular.toFusionCategoryData.automorphismScalarPower
          automorphism
          (((change.labelingEquiv S).symm
            (sourceLabeling, addedLabeling))
            (change.targetDecomposition.symm
              (Sum.inr addedIndex)))
          (target.cycleComponentExponent
            (target.chosenCycle
              (target.topology.h2ModelEquiv.symm (targetClass alpha)))
            (componentAt target.topology.formal
              (change.targetDecomposition.symm
                (Sum.inr addedIndex)))) =
        _
    have addedExponent :=
      transport.added_exponent_sound alpha addedIndex
    rw [addedExponent]
    simp [AddedComponentIndexChange.labelingEquiv]

end AddedComponentExponentTransport

/--
Exact category-neutral geometry of a cancellation birth.

The target component registry is split into the old components and a finite
local summand.  The target closed free diagram is literally the disjoint
union of a local free diagram and the complete source free diagram.  No
category, categorical morphism, evaluator, or scalar equality occurs in this
structure.
-/
structure AddedClosedDiagramGeometry
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (addedCount : Nat)
    (targetClass : H2 → H2) where
  componentChange :
    AddedComponentIndexChange
      source.topology.formal target.topology.formal addedCount
  exponentTransport :
    AddedComponentExponentTransport
      source target componentChange targetClass
  localDiagram : ComponentDiagram .unit .unit
  diagram_isotopy :
    GeneratedIsotopy target.componentTermDiagram
      (ComponentDiagram.closedTensor
        localDiagram source.componentTermDiagram)

namespace AddedClosedDiagramGeometry

/--
On the retained source diagram, the reconstructed target labeling is exactly
the original source labeling.
-/
theorem source_term_eval_transport
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    {targetClass : H2 → H2}
    (geometry :
      AddedClosedDiagramGeometry
        source target addedCount targetClass)
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

/--
After scalarization, the target term is the product of the local closed
diagram and the retained source term.  Multiplicativity is proved from the
fusion-category scalarization; it is not an assumption of the geometry.
-/
theorem term_closedScalar_split
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {addedCount : Nat}
    {targetClass : H2 → H2}
    (geometry :
      AddedClosedDiagramGeometry
        source target addedCount targetClass)
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
      congrArg 𝒞.premodular.toFusionCategoryData.closedScalar
        sourceEval

end AddedClosedDiagramGeometry

/--
Category-neutral endpoint geometry for insertion of one cancelling 1--2
pair.  The two new components form the exact positive Hopf pair, and both
new degree-two exponents are zero.
-/
structure OneTwoBirthGeometry
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (targetClass : H2 → H2) where
  added :
    AddedClosedDiagramGeometry source target 2 targetClass
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
    (alpha : H2) →
    (addedIndex : Fin 2) →
      added.exponentTransport.added_exponent alpha addedIndex = 0

namespace OneTwoBirthGeometry

/-- The new dotted component receives the first local simple label. -/
theorem dotted_label_sound
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthGeometry source target targetClass)
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

/-- The new meridian two-handle receives the second local simple label. -/
theorem two_handle_label_sound
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthGeometry source target targetClass)
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

/-- The local coefficient is the product of the two quantum dimensions. -/
theorem localWeight_eq_quantumDimensions
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism :
      TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthGeometry source target targetClass)
    (alpha : H2)
    (addedLabeling : Fin 2 → S) :
    geometry.added.exponentTransport.localWeight
        𝒞.premodular automorphism alpha addedLabeling =
      𝒞.premodular.quantumDimension
          (addedLabeling firstOfTwo) *
        𝒞.premodular.quantumDimension
          (addedLabeling secondOfTwo) := by
  classical
  unfold AddedComponentExponentTransport.localWeight
  rw [Fin.prod_univ_two]
  have firstZero :=
    geometry.added_exponent_zero alpha (0 : Fin 2)
  have secondZero :=
    geometry.added_exponent_zero alpha (1 : Fin 2)
  rw [firstZero, secondZero]
  simp only [firstOfTwo, secondOfTwo,
    FusionCategoryData.automorphismScalarPower_zero, mul_one]
  congr 2 <;> apply Fin.ext <;> rfl

/--
The complete local two-component Kirby-colour sum is the global dimension.

This is where the exact Bärenz--Barrett cutting/killing theorem is consumed.
No surrounding presentation data or final normalization enters that axiom.
-/
theorem localPairSum_eq_globalDimension
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (automorphism :
      TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthGeometry source target targetClass)
    (alpha : H2)
    (sourceLabeling : source.GlobalLabeling (S := S)) :
    (∑ addedLabeling : Fin 2 → S,
      geometry.added.exponentTransport.localWeight
          𝒞.premodular automorphism alpha addedLabeling *
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
    𝒞.premodular automorphism alpha]
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

/--
The complete numerator acquires exactly one global dimension when the
cancelling 1--2 Hopf pair is inserted.
-/
theorem rawNumerator_factor
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (automorphism :
      TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : OneTwoBirthGeometry source target targetClass)
    (alpha : H2) :
    target.rawNumerator 𝒞.premodular automorphism
        (target.topology.h2ModelEquiv.symm (targetClass alpha)) =
      globalDimension 𝒞.premodular *
        source.rawNumerator 𝒞.premodular automorphism
          (source.topology.h2ModelEquiv.symm alpha) := by
  classical
  rw [target.rawNumerator_eq_sum 𝒞.premodular automorphism
    (target.topology.h2ModelEquiv.symm (targetClass alpha))]
  rw [source.rawNumerator_eq_sum 𝒞.premodular automorphism
    (source.topology.h2ModelEquiv.symm alpha)]
  rw [geometry.added.componentChange.sum_split]
  rw [Fintype.sum_prod_type]
  change
    (∑ sourceLabeling, ∑ addedLabeling,
      target.cycleGlobalWeight 𝒞.premodular automorphism
          (target.chosenCycle
            (target.topology.h2ModelEquiv.symm (targetClass alpha)))
          ((geometry.added.componentChange.labelingEquiv S).symm
            (sourceLabeling, addedLabeling)) *
        𝒞.premodular.toFusionCategoryData.closedScalar
          (Diagram.eval C
            (target.termDiagram 𝒞.premodular
              ((geometry.added.componentChange.labelingEquiv S).symm
                (sourceLabeling, addedLabeling))))) =
      globalDimension 𝒞.premodular *
        ∑ sourceLabeling,
          source.cycleGlobalWeight 𝒞.premodular automorphism
              (source.chosenCycle
                (source.topology.h2ModelEquiv.symm alpha)) sourceLabeling *
            𝒞.premodular.toFusionCategoryData.closedScalar
              (Diagram.eval C
                (source.termDiagram 𝒞.premodular sourceLabeling))
  calc
    _ =
      ∑ sourceLabeling,
        globalDimension 𝒞.premodular *
          (source.cycleGlobalWeight 𝒞.premodular automorphism
              (source.chosenCycle
                (source.topology.h2ModelEquiv.symm alpha)) sourceLabeling *
            𝒞.premodular.toFusionCategoryData.closedScalar
              (Diagram.eval C
                (source.termDiagram 𝒞.premodular sourceLabeling))) := by
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        calc
          (∑ addedLabeling,
              target.cycleGlobalWeight 𝒞.premodular automorphism
                  (target.chosenCycle
                    (target.topology.h2ModelEquiv.symm
                      (targetClass alpha)))
                  ((geometry.added.componentChange.labelingEquiv S).symm
                    (sourceLabeling, addedLabeling)) *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (target.termDiagram 𝒞.premodular
                      ((geometry.added.componentChange.labelingEquiv S).symm
                        (sourceLabeling, addedLabeling))))) =
            ∑ addedLabeling : Fin 2 → S,
              (geometry.added.exponentTransport.localWeight
                  𝒞.premodular automorphism alpha addedLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (geometry.added.localDiagram.interpret
                      𝒞.premodular
                      (target.labelOf 𝒞.premodular
                        ((geometry.added.componentChange.labelingEquiv S).symm
                          (sourceLabeling, addedLabeling)))))) *
              (source.cycleGlobalWeight 𝒞.premodular automorphism
                  (source.chosenCycle
                    (source.topology.h2ModelEquiv.symm alpha))
                  sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞.premodular sourceLabeling))) := by
              apply Finset.sum_congr rfl
              intro addedLabeling _
              rw [geometry.added.exponentTransport.cycleGlobalWeight_split
                𝒞.premodular automorphism alpha sourceLabeling addedLabeling]
              rw [geometry.added.term_closedScalar_split
                𝒞.premodular sourceLabeling addedLabeling]
              ring
          _ =
            globalDimension 𝒞.premodular *
              (source.cycleGlobalWeight 𝒞.premodular automorphism
                  (source.chosenCycle
                    (source.topology.h2ModelEquiv.symm alpha))
                  sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞.premodular sourceLabeling))) := by
              rw [← Finset.sum_mul,
                geometry.localPairSum_eq_globalDimension
                  𝒞 automorphism alpha sourceLabeling]
    _ = _ := by
      rw [Finset.mul_sum]

end OneTwoBirthGeometry

/--
Category-neutral endpoint geometry for insertion of one cancelling 2--3
pair.  The new two-handle is represented by one isolated zero-framed unknot,
and its transported degree-two exponent is zero.
-/
structure TwoThreeBirthGeometry
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (targetClass : H2 → H2) where
  added :
    AddedClosedDiagramGeometry source target 1 targetClass
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
    (alpha : H2) →
      added.exponentTransport.added_exponent alpha onlyOne = 0

namespace TwoThreeBirthGeometry

/-- The new local component receives exactly the sole added simple label. -/
theorem added_label_sound
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : TwoThreeBirthGeometry source target targetClass)
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

/-- The coefficient of the new 2-handle is its quantum dimension. -/
theorem localWeight_eq_quantumDimension
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism :
      TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : TwoThreeBirthGeometry source target targetClass)
    (alpha : H2)
    (addedLabeling : Fin 1 → S) :
    geometry.added.exponentTransport.localWeight
        𝒞 automorphism alpha addedLabeling =
      𝒞.premodular.quantumDimension (addedLabeling onlyOne) := by
  classical
  unfold AddedComponentExponentTransport.localWeight
  rw [Fintype.prod_unique]
  have exponentZero := geometry.added_exponent_zero alpha
  simpa only [Subsingleton.elim (default : Fin 1) onlyOne,
    exponentZero,
    FusionCategoryData.automorphismScalarPower_zero, mul_one]

/-- The local isolated unknot has the same quantum dimension. -/
theorem localDiagram_closedScalar_eq_quantumDimension
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : TwoThreeBirthGeometry source target targetClass)
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

/--
The complete finite Kirby-colour numerator acquires exactly one global
dimension when an isolated cancelling 2--3 pair is inserted.

All label reindexing, exponent transport, disjoint-union multiplicativity,
and finite-sum algebra are performed in Lean.
-/
theorem rawNumerator_factor
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism :
      TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {targetClass : H2 → H2}
    (geometry : TwoThreeBirthGeometry source target targetClass)
    (alpha : H2) :
    target.rawNumerator 𝒞 automorphism
        (target.topology.h2ModelEquiv.symm (targetClass alpha)) =
      globalDimension 𝒞.premodular *
        source.rawNumerator 𝒞 automorphism
          (source.topology.h2ModelEquiv.symm alpha) := by
  classical
  rw [target.rawNumerator_eq_sum 𝒞 automorphism
    (target.topology.h2ModelEquiv.symm (targetClass alpha))]
  rw [source.rawNumerator_eq_sum 𝒞 automorphism
    (source.topology.h2ModelEquiv.symm alpha)]
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
  change
    (∑ sourceLabeling, ∑ addedLabeling,
      target.cycleGlobalWeight 𝒞.premodular automorphism
          (target.chosenCycle
            (target.topology.h2ModelEquiv.symm (targetClass alpha)))
          ((geometry.added.componentChange.labelingEquiv S).symm
            (sourceLabeling, addedLabeling)) *
        𝒞.premodular.toFusionCategoryData.closedScalar
          (Diagram.eval C
            (target.termDiagram 𝒞.premodular
              ((geometry.added.componentChange.labelingEquiv S).symm
                (sourceLabeling, addedLabeling))))) =
      globalDimension 𝒞.premodular *
        ∑ sourceLabeling,
          source.cycleGlobalWeight 𝒞.premodular automorphism
              (source.chosenCycle
                (source.topology.h2ModelEquiv.symm alpha)) sourceLabeling *
            𝒞.premodular.toFusionCategoryData.closedScalar
              (Diagram.eval C
                (source.termDiagram 𝒞.premodular sourceLabeling))
  calc
    _ =
      ∑ sourceLabeling,
        globalDimension 𝒞.premodular *
          (source.cycleGlobalWeight 𝒞.premodular automorphism
              (source.chosenCycle
                (source.topology.h2ModelEquiv.symm alpha)) sourceLabeling *
            𝒞.premodular.toFusionCategoryData.closedScalar
              (Diagram.eval C
                (source.termDiagram 𝒞.premodular sourceLabeling))) := by
        apply Finset.sum_congr rfl
        intro sourceLabeling _
        calc
          (∑ addedLabeling,
              target.cycleGlobalWeight 𝒞.premodular automorphism
                  (target.chosenCycle
                    (target.topology.h2ModelEquiv.symm
                      (targetClass alpha)))
                  ((geometry.added.componentChange.labelingEquiv S).symm
                    (sourceLabeling, addedLabeling)) *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (target.termDiagram 𝒞.premodular
                      ((geometry.added.componentChange.labelingEquiv S).symm
                        (sourceLabeling, addedLabeling))))) =
            ∑ addedLabeling : Fin 1 → S,
              (𝒞.premodular.quantumDimension (addedLabeling onlyOne) *
                𝒞.premodular.quantumDimension (addedLabeling onlyOne)) *
              (source.cycleGlobalWeight 𝒞.premodular automorphism
                  (source.chosenCycle
                    (source.topology.h2ModelEquiv.symm alpha))
                  sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞.premodular sourceLabeling))) := by
              apply Finset.sum_congr rfl
              intro addedLabeling _
              rw [geometry.added.exponentTransport.cycleGlobalWeight_split
                𝒞 automorphism alpha sourceLabeling addedLabeling]
              rw [geometry.localWeight_eq_quantumDimension
                𝒞 automorphism alpha addedLabeling]
              rw [geometry.added.term_closedScalar_split
                𝒞 sourceLabeling addedLabeling]
              rw [geometry.localDiagram_closedScalar_eq_quantumDimension
                𝒞 sourceLabeling addedLabeling]
              ring
          _ =
            globalDimension 𝒞.premodular *
              (source.cycleGlobalWeight 𝒞.premodular automorphism
                  (source.chosenCycle
                    (source.topology.h2ModelEquiv.symm alpha))
                  sourceLabeling *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (Diagram.eval C
                    (source.termDiagram 𝒞.premodular sourceLabeling))) := by
              rw [← Finset.sum_mul, addedSum]
    _ = _ := by
      rw [Finset.mul_sum]

end TwoThreeBirthGeometry

end TwistedYetter.Kirby.CanonicalMoveGeometry
