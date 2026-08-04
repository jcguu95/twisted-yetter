import TwistedYetter.StableNoGo.EntranceAxioms
import TwistedYetter.StableNoGo.RawMultiplicativity
import TwistedYetter.Kirby.Final.TwistedYetter

/-!
# Evaluator factorization over a transparent split presentation

This file derives category calculations from `SplitSpecialKirbyPresentation`.
The two topology axioms only supply the split presentation and its marking
naturality; no evaluator equality is imported from topology.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open scoped BigOperators
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final.Proofs
open TwistedYetter.Kirby.Final

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- A transparent embedding of one combinatorial link trace into another. -/
structure TraceEmbedding
    (source target : CombinatorialLinkTrace) where
  component : source.ComponentId -> target.ComponentId
  strand : source.StrandId -> target.StrandId
  component_data :
    ∀ item, target.components (component item) = source.components item
  strand_component :
    ∀ item,
      (target.strands (strand item)).component =
        component (source.strands item).component
  strand_orientation :
    ∀ item,
      (target.strands (strand item)).orientation =
        (source.strands item).orientation

def TraceEmbedding.puncture
    {source target : CombinatorialLinkTrace}
    (embedding : TraceEmbedding source target)
    (puncture : DottedPuncture source) :
    DottedPuncture target where
  dottedComponent := embedding.component puncture.dottedComponent
  twoHandleComponent := embedding.component puncture.twoHandleComponent
  inputStrand := embedding.strand puncture.inputStrand
  outputStrand := embedding.strand puncture.outputStrand
  direction := puncture.direction
  cutPosition := puncture.cutPosition
  dotted_role := by
    simpa [embedding.component_data] using puncture.dotted_role
  two_handle_role := by
    simpa [embedding.component_data] using puncture.two_handle_role
  input_on_two_handle := by
    rw [embedding.strand_component, puncture.input_on_two_handle]
  output_on_two_handle := by
    rw [embedding.strand_component, puncture.output_on_two_handle]
  orientation_preserved := by
    rw [embedding.strand_orientation, embedding.strand_orientation]
    exact puncture.orientation_preserved

def TraceEmbedding.event
    {source target : CombinatorialLinkTrace}
    (embedding : TraceEmbedding source target) :
    CutOpenEvent source -> CutOpenEvent target
  | .birth left right => .birth (embedding.strand left) (embedding.strand right)
  | .death left right => .death (embedding.strand left) (embedding.strand right)
  | .crossing overInput underInput overOutput underOutput sign =>
      .crossing (embedding.strand overInput) (embedding.strand underInput)
        (embedding.strand overOutput) (embedding.strand underOutput) sign
  | .framingTwist input output sign =>
      .framingTwist (embedding.strand input) (embedding.strand output) sign
  | .planarIsotopy continuations =>
      .planarIsotopy
        (continuations.map fun pair =>
          (embedding.strand pair.1, embedding.strand pair.2))
  | .projectorHole dotted punctures =>
      .projectorHole (embedding.component dotted)
        (punctures.map embedding.puncture)

theorem TraceEmbedding.event_pairing
    {source target : CombinatorialLinkTrace}
    (embedding : TraceEmbedding source target)
    (event : CutOpenEvent source)
    (pairing : event.StrandContinuationsAreWellFormed) :
    (embedding.event event).StrandContinuationsAreWellFormed := by
  cases event with
  | birth left right =>
      exact
        ⟨by rw [embedding.strand_component,
            embedding.strand_component, pairing.1],
          by rw [embedding.strand_orientation,
            embedding.strand_orientation]
             exact pairing.2⟩
  | death left right =>
      exact
        ⟨by rw [embedding.strand_component,
            embedding.strand_component, pairing.1],
          by rw [embedding.strand_orientation,
            embedding.strand_orientation]
             exact pairing.2⟩
  | crossing overInput underInput overOutput underOutput sign =>
      exact
        ⟨by rw [embedding.strand_component,
            embedding.strand_component, pairing.1],
          by rw [embedding.strand_orientation,
            embedding.strand_orientation]
             exact pairing.2.1,
          by rw [embedding.strand_component,
            embedding.strand_component, pairing.2.2.1],
          by rw [embedding.strand_orientation,
            embedding.strand_orientation]
             exact pairing.2.2.2⟩
  | framingTwist input output sign =>
      exact
        ⟨by rw [embedding.strand_component,
            embedding.strand_component, pairing.1],
          by rw [embedding.strand_orientation,
            embedding.strand_orientation]
             exact pairing.2⟩
  | planarIsotopy continuations =>
      intro pair membership
      simp only [List.mem_map] at membership
      obtain ⟨sourcePair, sourceMembership, pairEq⟩ := membership
      subst pair
      have sourcePairing := pairing sourcePair sourceMembership
      exact
        ⟨by rw [embedding.strand_component,
            embedding.strand_component, sourcePairing.1],
          by rw [embedding.strand_orientation,
            embedding.strand_orientation]
             exact sourcePairing.2⟩
  | projectorHole dotted punctures =>
      intro targetPuncture membership
      simp only [List.mem_map] at membership
      obtain ⟨sourcePuncture, sourceMembership, targetEq⟩ := membership
      subst targetPuncture
      have sourcePairing := pairing sourcePuncture sourceMembership
      exact
        ⟨by change
              (target.strands
                  (embedding.strand sourcePuncture.inputStrand)).component =
                (target.strands
                  (embedding.strand sourcePuncture.outputStrand)).component
            rw [embedding.strand_component,
            embedding.strand_component, sourcePairing.1],
          by change
              (target.strands
                  (embedding.strand sourcePuncture.inputStrand)).orientation =
                (target.strands
                  (embedding.strand sourcePuncture.outputStrand)).orientation
             rw [embedding.strand_orientation,
            embedding.strand_orientation]
             exact sourcePairing.2⟩

theorem TraceEmbedding.event_beforeWord
    {source target : CombinatorialLinkTrace}
    (embedding : TraceEmbedding source target)
    (event : CutOpenEvent source) :
    (embedding.event event).beforeWord =
      event.beforeWord.map embedding.strand := by
  cases event with
  | birth | death | crossing | framingTwist | planarIsotopy =>
      simp [TraceEmbedding.event, CutOpenEvent.beforeWord, List.map_map]
  | projectorHole dotted punctures =>
      simp [TraceEmbedding.event, CutOpenEvent.beforeWord,
        TraceEmbedding.puncture, List.map_map]

theorem TraceEmbedding.event_afterWord
    {source target : CombinatorialLinkTrace}
    (embedding : TraceEmbedding source target)
    (event : CutOpenEvent source) :
    (embedding.event event).afterWord =
      event.afterWord.map embedding.strand := by
  cases event with
  | birth | death | crossing | framingTwist | planarIsotopy =>
      simp [TraceEmbedding.event, CutOpenEvent.afterWord, List.map_map]
  | projectorHole dotted punctures =>
      simp [TraceEmbedding.event, CutOpenEvent.afterWord,
        TraceEmbedding.puncture, List.map_map]

theorem TraceEmbedding.mappedExteriorWord
    {source target : SpecialKirbyDiagram}
    (embedding : TraceEmbedding source.trace target.trace)
    (𝒞 : BundledPremodularCategory K)
    (sourceLabeling : TwoHandleLabeling 𝒞 source)
    (targetLabeling : TwoHandleLabeling 𝒞 target)
    (orientedEq :
      ∀ strand,
        orientedExteriorStrand 𝒞 target targetLabeling
            (embedding.strand strand) =
          orientedExteriorStrand 𝒞 source sourceLabeling strand)
    (word : List source.trace.StrandId) :
    exteriorWord 𝒞 target targetLabeling (word.map embedding.strand) =
      exteriorWord 𝒞 source sourceLabeling word := by
  induction word with
  | nil => rfl
  | cons strand rest ih =>
      exact congrArg₂ List.cons (orientedEq strand) ih

/-- Elementary graphical interpretation is natural under an exact trace embedding. -/
theorem TraceEmbedding.compileEventMorphism_heq
    {source target : SpecialKirbyDiagram}
    (embedding : TraceEmbedding source.trace target.trace)
    (𝒞 : BundledPremodularCategory K)
    (sourcePresentation : DottedCutPresentation source)
    (targetPresentation : DottedCutPresentation target)
    (sourceLabeling : TwoHandleLabeling 𝒞 source)
    (targetLabeling : TwoHandleLabeling 𝒞 target)
    (orientedEq :
      ∀ strand,
        orientedExteriorStrand 𝒞 target targetLabeling
            (embedding.strand strand) =
          orientedExteriorStrand 𝒞 source sourceLabeling strand)
    (event : CutOpenEvent source.trace)
    (pairing : event.StrandContinuationsAreWellFormed) :
    HEq
      (compileCutOpenEventMorphism 𝒞 target targetLabeling
        (embedding.event event) (embedding.event_pairing event pairing))
      (compileCutOpenEventMorphism 𝒞 source sourceLabeling event pairing) := by
  have beforeEq :
      exteriorWord 𝒞 target targetLabeling
          (embedding.event event).beforeWord =
        exteriorWord 𝒞 source sourceLabeling event.beforeWord :=
    (congrArg (exteriorWord 𝒞 target targetLabeling)
      (embedding.event_beforeWord event)).trans
        (embedding.mappedExteriorWord 𝒞 sourceLabeling targetLabeling
          orientedEq event.beforeWord)
  have afterEq :
      exteriorWord 𝒞 target targetLabeling
          (embedding.event event).afterWord =
        exteriorWord 𝒞 source sourceLabeling event.afterWord :=
    (congrArg (exteriorWord 𝒞 target targetLabeling)
      (embedding.event_afterWord event)).trans
        (embedding.mappedExteriorWord 𝒞 sourceLabeling targetLabeling
          orientedEq event.afterWord)
  cases event with
  | birth left right =>
      have rightLabelEq := congrArg OrientedSimple.label (orientedEq right)
      have leftOrientationEq := embedding.strand_orientation left
      simp only [compileCutOpenEventMorphism, TraceEmbedding.event]
      unfold pairedBirthMorphism
      by_cases leftPositive : (source.trace.strands left).orientation = .positive
      · have targetPositive :
            (target.trace.strands (embedding.strand left)).orientation =
              .positive := leftOrientationEq.trans leftPositive
        simp only [leftPositive, targetPositive, ↓reduceDIte]
        exact
          (CategoryTheory.comp_eqToHom_heq _ _).trans
            ((canonicalPositiveNegativeBirth_heq 𝒞 rightLabelEq).trans
              (CategoryTheory.comp_eqToHom_heq _ _).symm)
      · have targetNotPositive :
            ¬(target.trace.strands (embedding.strand left)).orientation =
              .positive := by
          intro targetPositive
          exact leftPositive (leftOrientationEq.symm.trans targetPositive)
        simp only [leftPositive, targetNotPositive, ↓reduceDIte]
        exact
          (CategoryTheory.comp_eqToHom_heq _ _).trans
            ((canonicalNegativePositiveBirth_heq 𝒞 rightLabelEq).trans
              (CategoryTheory.comp_eqToHom_heq _ _).symm)
  | death left right =>
      have rightLabelEq := congrArg OrientedSimple.label (orientedEq right)
      have leftOrientationEq := embedding.strand_orientation left
      simp only [compileCutOpenEventMorphism, TraceEmbedding.event]
      unfold pairedDeathMorphism
      by_cases leftPositive : (source.trace.strands left).orientation = .positive
      · have targetPositive :
            (target.trace.strands (embedding.strand left)).orientation =
              .positive := leftOrientationEq.trans leftPositive
        simp only [leftPositive, targetPositive, ↓reduceDIte]
        exact
          (CategoryTheory.eqToHom_comp_heq _ _).trans
            ((canonicalPositiveNegativeDeath_heq 𝒞 rightLabelEq).trans
              (CategoryTheory.eqToHom_comp_heq _ _).symm)
      · have targetNotPositive :
            ¬(target.trace.strands (embedding.strand left)).orientation =
              .positive := by
          intro targetPositive
          exact leftPositive (leftOrientationEq.symm.trans targetPositive)
        simp only [leftPositive, targetNotPositive, ↓reduceDIte]
        exact
          (CategoryTheory.eqToHom_comp_heq _ _).trans
            ((canonicalNegativePositiveDeath_heq 𝒞 rightLabelEq).trans
              (CategoryTheory.eqToHom_comp_heq _ _).symm)
  | crossing overInput underInput overOutput underOutput sign =>
      exact
        (compileCrossingMorphism_heq_canonical 𝒞 target targetPresentation
          targetLabeling (embedding.strand overInput)
          (embedding.strand underInput) (embedding.strand overOutput)
          (embedding.strand underOutput) sign
          (embedding.event_pairing _ pairing)).trans
          ((canonicalCrossingMorphism_heq 𝒞
            (orientedEq overInput) (orientedEq underInput)
            (orientedEq overOutput) (orientedEq underOutput) sign
            _ _ _ _).trans
            (compileCrossingMorphism_heq_canonical 𝒞 source
              sourcePresentation sourceLabeling overInput underInput
              overOutput underOutput sign pairing).symm)
  | framingTwist input output sign =>
      exact
        (compileFramingTwistMorphism_heq_canonical 𝒞 target
          targetPresentation targetLabeling (embedding.strand input)
          (embedding.strand output) sign
          (embedding.event_pairing _ pairing)).trans
          ((canonicalFramingTwistMorphism_heq 𝒞
            (orientedEq input) (orientedEq output) sign _ _).trans
            (compileFramingTwistMorphism_heq_canonical 𝒞 source
              sourcePresentation sourceLabeling input output sign pairing).symm)
  | planarIsotopy continuations =>
      let targetContinuations :
          List (target.trace.StrandId × target.trace.StrandId) :=
        continuations.map fun pair =>
          (embedding.strand pair.1, embedding.strand pair.2)
      have targetPairing :
          (CutOpenEvent.planarIsotopy targetContinuations).StrandContinuationsAreWellFormed :=
        by simpa [targetContinuations, TraceEmbedding.event] using
          embedding.event_pairing _ pairing
      exact
        (compilePlanarIsotopyMorphism_heq_canonical 𝒞 target
          targetPresentation targetLabeling
          targetContinuations
          targetPairing).trans
          ((canonicalPlanarIsotopyMorphism_heq 𝒞 beforeEq afterEq _ _).trans
            (compilePlanarIsotopyMorphism_heq_canonical 𝒞 source
              sourcePresentation sourceLabeling continuations pairing).symm)
  | projectorHole dotted punctures =>
      exact
        (compileProjectorHoleMorphism_heq_canonical 𝒞 target
          targetPresentation targetLabeling (embedding.component dotted)
          (punctures.map embedding.puncture)
          (embedding.event_pairing _ pairing)).trans
          ((canonicalProjectorHoleMorphism_heq 𝒞 beforeEq afterEq _ _).trans
            (compileProjectorHoleMorphism_heq_canonical 𝒞 source
              sourcePresentation sourceLabeling dotted punctures pairing).symm)

theorem TraceEmbedding.contexts_of_before_nonempty
    {source target : SpecialKirbyDiagram}
    (embedding : TraceEmbedding source.trace target.trace)
    (sourcePresentation : DottedCutPresentation source)
    (targetPresentation : DottedCutPresentation target)
    (sourceEvent : Fin sourcePresentation.cut.exterior.eventCount)
    (targetEvent : Fin targetPresentation.cut.exterior.eventCount)
    (eventEq :
      targetPresentation.cut.exterior.events targetEvent =
        embedding.event (sourcePresentation.cut.exterior.events sourceEvent))
    (activeEq :
      targetPresentation.cut.exterior.activeOrder targetEvent.castSucc =
        (sourcePresentation.cut.exterior.activeOrder sourceEvent.castSucc).map
          embedding.strand)
    (beforeNonempty :
      (sourcePresentation.cut.exterior.events sourceEvent).beforeWord ≠ []) :
    eventLeftContext target targetPresentation targetEvent =
        (eventLeftContext source sourcePresentation sourceEvent).map
          embedding.strand ∧
      eventRightContext target targetPresentation targetEvent =
        (eventRightContext source sourcePresentation sourceEvent).map
          embedding.strand := by
  have mappedSourceTransition := congrArg (List.map embedding.strand)
    (eventTransitionEquations source sourcePresentation sourceEvent).1
  have secondDecomposition :
      targetPresentation.cut.exterior.activeOrder targetEvent.castSucc =
        (eventLeftContext source sourcePresentation sourceEvent).map
            embedding.strand ++
          (targetPresentation.cut.exterior.events targetEvent).beforeWord ++
          (eventRightContext source sourcePresentation sourceEvent).map
            embedding.strand := by
    rw [activeEq, eventEq, embedding.event_beforeWord]
    simpa [List.map_append] using mappedSourceTransition
  have middleNonempty :
      (targetPresentation.cut.exterior.events targetEvent).beforeWord ≠ [] := by
    rw [eventEq, embedding.event_beforeWord]
    simpa using beforeNonempty
  exact list_context_unique_of_nodup
    (targetPresentation.cut.exterior.activeWordsNoDuplicates
      targetEvent.castSucc)
    middleNonempty
    (eventTransitionEquations target targetPresentation targetEvent).1
    secondDecomposition

theorem TraceEmbedding.contexts_of_after_nonempty
    {source target : SpecialKirbyDiagram}
    (embedding : TraceEmbedding source.trace target.trace)
    (sourcePresentation : DottedCutPresentation source)
    (targetPresentation : DottedCutPresentation target)
    (sourceEvent : Fin sourcePresentation.cut.exterior.eventCount)
    (targetEvent : Fin targetPresentation.cut.exterior.eventCount)
    (eventEq :
      targetPresentation.cut.exterior.events targetEvent =
        embedding.event (sourcePresentation.cut.exterior.events sourceEvent))
    (activeEq :
      targetPresentation.cut.exterior.activeOrder targetEvent.succ =
        (sourcePresentation.cut.exterior.activeOrder sourceEvent.succ).map
          embedding.strand)
    (afterNonempty :
      (sourcePresentation.cut.exterior.events sourceEvent).afterWord ≠ []) :
    eventLeftContext target targetPresentation targetEvent =
        (eventLeftContext source sourcePresentation sourceEvent).map
          embedding.strand ∧
      eventRightContext target targetPresentation targetEvent =
        (eventRightContext source sourcePresentation sourceEvent).map
          embedding.strand := by
  have mappedSourceTransition := congrArg (List.map embedding.strand)
    (eventTransitionEquations source sourcePresentation sourceEvent).2
  have secondDecomposition :
      targetPresentation.cut.exterior.activeOrder targetEvent.succ =
        (eventLeftContext source sourcePresentation sourceEvent).map
            embedding.strand ++
          (targetPresentation.cut.exterior.events targetEvent).afterWord ++
          (eventRightContext source sourcePresentation sourceEvent).map
            embedding.strand := by
    rw [activeEq, eventEq, embedding.event_afterWord]
    simpa [List.map_append] using mappedSourceTransition
  have middleNonempty :
      (targetPresentation.cut.exterior.events targetEvent).afterWord ≠ [] := by
    rw [eventEq, embedding.event_afterWord]
    simpa using afterNonempty
  exact list_context_unique_of_nodup
    (targetPresentation.cut.exterior.activeWordsNoDuplicates targetEvent.succ)
    middleNonempty
    (eventTransitionEquations target targetPresentation targetEvent).2
    secondDecomposition

theorem TraceEmbedding.compileContextualMorphism_heq_of_contexts
    {source target : SpecialKirbyDiagram}
    (embedding : TraceEmbedding source.trace target.trace)
    (𝒞 : BundledPremodularCategory K)
    (sourcePresentation : DottedCutPresentation source)
    (targetPresentation : DottedCutPresentation target)
    (sourceLabeling : TwoHandleLabeling 𝒞 source)
    (targetLabeling : TwoHandleLabeling 𝒞 target)
    (orientedEq :
      ∀ strand,
        orientedExteriorStrand 𝒞 target targetLabeling
            (embedding.strand strand) =
          orientedExteriorStrand 𝒞 source sourceLabeling strand)
    (sourceEvent : Fin sourcePresentation.cut.exterior.eventCount)
    (targetEvent : Fin targetPresentation.cut.exterior.eventCount)
    (eventEq :
      targetPresentation.cut.exterior.events targetEvent =
        embedding.event (sourcePresentation.cut.exterior.events sourceEvent))
    (contexts :
      eventLeftContext target targetPresentation targetEvent =
          (eventLeftContext source sourcePresentation sourceEvent).map
            embedding.strand ∧
        eventRightContext target targetPresentation targetEvent =
          (eventRightContext source sourcePresentation sourceEvent).map
            embedding.strand) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target
        targetPresentation targetLabeling targetEvent)
      (compileContextualCutOpenEventMorphism 𝒞 source
        sourcePresentation sourceLabeling sourceEvent) := by
  let sourceStoredEvent := sourcePresentation.cut.exterior.events sourceEvent
  have leftEq :
      exteriorWord 𝒞 target targetLabeling
          (eventLeftContext target targetPresentation targetEvent) =
        exteriorWord 𝒞 source sourceLabeling
          (eventLeftContext source sourcePresentation sourceEvent) := by
    rw [contexts.1]
    exact embedding.mappedExteriorWord 𝒞 sourceLabeling targetLabeling
      orientedEq _
  have rightEq :
      exteriorWord 𝒞 target targetLabeling
          (eventRightContext target targetPresentation targetEvent) =
        exteriorWord 𝒞 source sourceLabeling
          (eventRightContext source sourcePresentation sourceEvent) := by
    rw [contexts.2]
    exact embedding.mappedExteriorWord 𝒞 sourceLabeling targetLabeling
      orientedEq _
  have beforeEq :
      exteriorWord 𝒞 target targetLabeling
          (targetPresentation.cut.exterior.events targetEvent).beforeWord =
        exteriorWord 𝒞 source sourceLabeling sourceStoredEvent.beforeWord := by
    rw [eventEq, embedding.event_beforeWord]
    exact embedding.mappedExteriorWord 𝒞 sourceLabeling targetLabeling
      orientedEq _
  have afterEq :
      exteriorWord 𝒞 target targetLabeling
          (targetPresentation.cut.exterior.events targetEvent).afterWord =
        exteriorWord 𝒞 source sourceLabeling sourceStoredEvent.afterWord := by
    rw [eventEq, embedding.event_afterWord]
    exact embedding.mappedExteriorWord 𝒞 sourceLabeling targetLabeling
      orientedEq _
  have targetLocalToMapped :=
    compileCutOpenEventMorphism_heq_of_event_eq 𝒞 target targetLabeling
      eventEq
      (targetPresentation.cut.exterior.strandContinuationsAreWellFormed
        targetEvent)
  have mappedToSource := embedding.compileEventMorphism_heq 𝒞
    sourcePresentation targetPresentation sourceLabeling targetLabeling
    orientedEq sourceStoredEvent
    (sourcePresentation.cut.exterior.strandContinuationsAreWellFormed
      sourceEvent)
  have localEq := targetLocalToMapped.trans mappedToSource
  exact
    (compileContextualCutOpenEventMorphism_heq_core 𝒞 target
      targetPresentation targetLabeling targetEvent).trans
      ((contextualizeRibbonMorphism_heq 𝒞
        leftEq beforeEq afterEq rightEq localEq).trans
        (compileContextualCutOpenEventMorphism_heq_core 𝒞 source
          sourcePresentation sourceLabeling sourceEvent).symm)

theorem TraceEmbedding.compileContextualMorphism_heq
    {source target : SpecialKirbyDiagram}
    (embedding : TraceEmbedding source.trace target.trace)
    (𝒞 : BundledPremodularCategory K)
    (sourcePresentation : DottedCutPresentation source)
    (targetPresentation : DottedCutPresentation target)
    (sourceLabeling : TwoHandleLabeling 𝒞 source)
    (targetLabeling : TwoHandleLabeling 𝒞 target)
    (orientedEq :
      ∀ strand,
        orientedExteriorStrand 𝒞 target targetLabeling
            (embedding.strand strand) =
          orientedExteriorStrand 𝒞 source sourceLabeling strand)
    (sourceEvent : Fin sourcePresentation.cut.exterior.eventCount)
    (targetEvent : Fin targetPresentation.cut.exterior.eventCount)
    (eventEq :
      targetPresentation.cut.exterior.events targetEvent =
        embedding.event (sourcePresentation.cut.exterior.events sourceEvent))
    (activeBeforeEq :
      targetPresentation.cut.exterior.activeOrder targetEvent.castSucc =
        (sourcePresentation.cut.exterior.activeOrder sourceEvent.castSucc).map
          embedding.strand)
    (activeAfterEq :
      targetPresentation.cut.exterior.activeOrder targetEvent.succ =
        (sourcePresentation.cut.exterior.activeOrder sourceEvent.succ).map
          embedding.strand) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target
        targetPresentation targetLabeling targetEvent)
      (compileContextualCutOpenEventMorphism 𝒞 source
        sourcePresentation sourceLabeling sourceEvent) := by
  generalize sourceEventEq :
    sourcePresentation.cut.exterior.events sourceEvent = event
  have boundEventEq := eventEq
  rw [sourceEventEq] at boundEventEq
  have identityObjectEq :
      ribbonWordObject 𝒞
          (exteriorWord 𝒞 target targetLabeling
            (targetPresentation.cut.exterior.activeOrder
              targetEvent.castSucc)) =
        ribbonWordObject 𝒞
          (exteriorWord 𝒞 source sourceLabeling
            (sourcePresentation.cut.exterior.activeOrder
              sourceEvent.castSucc)) := by
    apply congrArg (ribbonWordObject 𝒞)
    rw [activeBeforeEq]
    exact embedding.mappedExteriorWord 𝒞 sourceLabeling targetLabeling
      orientedEq _
  cases event with
  | birth left right =>
      exact embedding.compileContextualMorphism_heq_of_contexts 𝒞
        sourcePresentation targetPresentation sourceLabeling targetLabeling
        orientedEq sourceEvent targetEvent eventEq
        (embedding.contexts_of_after_nonempty sourcePresentation
          targetPresentation sourceEvent targetEvent eventEq activeAfterEq
          (by rw [sourceEventEq]
              simp [CutOpenEvent.afterWord]))
  | death left right =>
      exact embedding.compileContextualMorphism_heq_of_contexts 𝒞
        sourcePresentation targetPresentation sourceLabeling targetLabeling
        orientedEq sourceEvent targetEvent eventEq
        (embedding.contexts_of_before_nonempty sourcePresentation
          targetPresentation sourceEvent targetEvent eventEq activeBeforeEq
          (by rw [sourceEventEq]
              simp [CutOpenEvent.beforeWord]))
  | crossing overInput underInput overOutput underOutput sign =>
      exact embedding.compileContextualMorphism_heq_of_contexts 𝒞
        sourcePresentation targetPresentation sourceLabeling targetLabeling
        orientedEq sourceEvent targetEvent eventEq
        (embedding.contexts_of_before_nonempty sourcePresentation
          targetPresentation sourceEvent targetEvent eventEq activeBeforeEq
          (by rw [sourceEventEq]
              simp [CutOpenEvent.beforeWord]))
  | framingTwist input output sign =>
      exact embedding.compileContextualMorphism_heq_of_contexts 𝒞
        sourcePresentation targetPresentation sourceLabeling targetLabeling
        orientedEq sourceEvent targetEvent eventEq
        (embedding.contexts_of_before_nonempty sourcePresentation
          targetPresentation sourceEvent targetEvent eventEq activeBeforeEq
          (by rw [sourceEventEq]
              simp [CutOpenEvent.beforeWord]))
  | planarIsotopy continuations =>
      by_cases continuationsEmpty : continuations = []
      · subst continuations
        have targetEventEq :
            targetPresentation.cut.exterior.events targetEvent =
              .planarIsotopy [] := by
          simpa [TraceEmbedding.event] using boundEventEq
        exact
          (compileContextual_planarNil_heq_identity 𝒞 target
            targetPresentation targetLabeling targetEvent targetEventEq).trans
            ((identity_heq_of_object_eq identityObjectEq).trans
              (compileContextual_planarNil_heq_identity 𝒞 source
                sourcePresentation sourceLabeling sourceEvent
                sourceEventEq).symm)
      · have beforeNonempty :
            (CutOpenEvent.planarIsotopy continuations).beforeWord ≠ [] := by
          simpa [CutOpenEvent.beforeWord] using continuationsEmpty
        exact embedding.compileContextualMorphism_heq_of_contexts 𝒞
          sourcePresentation targetPresentation sourceLabeling targetLabeling
          orientedEq sourceEvent targetEvent eventEq
          (embedding.contexts_of_before_nonempty sourcePresentation
            targetPresentation sourceEvent targetEvent eventEq activeBeforeEq
            (by rw [sourceEventEq]
                exact beforeNonempty))
  | projectorHole dotted punctures =>
      by_cases puncturesEmpty : punctures = []
      · subst punctures
        have targetEventEq :
            targetPresentation.cut.exterior.events targetEvent =
              .projectorHole (embedding.component dotted) [] := by
          simpa [TraceEmbedding.event] using boundEventEq
        exact
          (compileContextual_projectorNil_heq_identity 𝒞 target
            targetPresentation targetLabeling targetEvent
            (embedding.component dotted) targetEventEq).trans
            ((identity_heq_of_object_eq identityObjectEq).trans
              (compileContextual_projectorNil_heq_identity 𝒞 source
                sourcePresentation sourceLabeling sourceEvent dotted
                sourceEventEq).symm)
      · have beforeNonempty :
            (CutOpenEvent.projectorHole dotted punctures).beforeWord ≠ [] := by
          simpa [CutOpenEvent.beforeWord] using puncturesEmpty
        exact embedding.compileContextualMorphism_heq_of_contexts 𝒞
          sourcePresentation targetPresentation sourceLabeling targetLabeling
          orientedEq sourceEvent targetEvent eventEq
          (embedding.contexts_of_before_nonempty sourcePresentation
            targetPresentation sourceEvent targetEvent eventEq activeBeforeEq
            (by rw [sourceEventEq]
                exact beforeNonempty))

/-- A target labeling is uniquely a pair of left and right labelings. -/
def splitTwoHandleLabelingEquiv
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K) :
    TwoHandleLabeling 𝒞 split.target.diagram ≃
      TwoHandleLabeling 𝒞 left.diagram ×
        TwoHandleLabeling 𝒞 right.diagram :=
  (Equiv.arrowCongr split.twoHandleEquiv (Equiv.refl 𝒞.simples.Simple)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp]
theorem splitTwoHandleLabelingEquiv_left
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (handle : Fin left.diagram.handles.hTwo) :
    (splitTwoHandleLabelingEquiv split 𝒞 labeling).1 handle =
      labeling (split.twoHandleEquiv.symm (Sum.inl handle)) := by
  rfl

@[simp]
theorem splitTwoHandleLabelingEquiv_right
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (handle : Fin right.diagram.handles.hTwo) :
    (splitTwoHandleLabelingEquiv split 𝒞 labeling).2 handle =
      labeling (split.twoHandleEquiv.symm (Sum.inr handle)) := by
  rfl

/-- The left strand keeps its index in the split target trace. -/
def splitLeftStrand
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right) :
    left.diagram.trace.StrandId -> split.target.diagram.trace.StrandId :=
  fun strand =>
    ⟨strand.1, by
      have lengths := congrArg List.length split.strands_split
      simp [serializedStrands] at lengths
      omega⟩

/-- The right strand is shifted past all left strands in the split target trace. -/
def splitRightStrand
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right) :
    right.diagram.trace.StrandId -> split.target.diagram.trace.StrandId :=
  fun strand =>
    ⟨left.diagram.trace.strandCount + strand.1, by
      have lengths := congrArg List.length split.strands_split
      simp [serializedStrands] at lengths
      omega⟩

@[simp]
theorem splitLeftStrand_value
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (strand : left.diagram.trace.StrandId) :
    (splitLeftStrand split strand).1 = strand.1 := by
  rfl

@[simp]
theorem splitRightStrand_value
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (strand : right.diagram.trace.StrandId) :
    (splitRightStrand split strand).1 =
      left.diagram.trace.strandCount + strand.1 := by
  rfl

/-- A left strand has exactly the same serialized component and orientation in the target. -/
theorem splitLeftStrand_serialization
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (strand : left.diagram.trace.StrandId) :
    serializeStrand
        (split.target.diagram.trace.strands (splitLeftStrand split strand)) =
      serializeStrand (left.diagram.trace.strands strand) := by
  have targetBound :
      strand.1 < split.target.diagram.trace.strandCount := by
    have lengths := congrArg List.length split.strands_split
    simp [serializedStrands] at lengths
    omega
  have atIndex := congrArg (fun strands => strands[strand.1]?) split.strands_split
  simp [serializedStrands, splitLeftStrand, strand.2, targetBound] at atIndex
  rw [List.getElem?_append_left (by simp [strand.2])] at atIndex
  simp at atIndex
  exact atIndex

/-- A right strand has the shifted component and unchanged orientation in the target. -/
theorem splitRightStrand_serialization
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (strand : right.diagram.trace.StrandId) :
    serializeStrand
        (split.target.diagram.trace.strands (splitRightStrand split strand)) =
      shiftSerializedStrand left.diagram.trace.componentCount
        (serializeStrand (right.diagram.trace.strands strand)) := by
  have targetBound :
      left.diagram.trace.strandCount + strand.1 <
        split.target.diagram.trace.strandCount := by
    have lengths := congrArg List.length split.strands_split
    simp [serializedStrands] at lengths
    omega
  have atIndex := congrArg
    (fun strands => strands[left.diagram.trace.strandCount + strand.1]?)
    split.strands_split
  simp [serializedStrands, splitRightStrand, strand.2,
    targetBound] at atIndex
  simpa [splitRightStrand] using atIndex

theorem splitLeftStrand_component_value
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (strand : left.diagram.trace.StrandId) :
    (split.target.diagram.trace.strands
        (splitLeftStrand split strand)).component.1 =
      (left.diagram.trace.strands strand).component.1 := by
  have serialized := splitLeftStrand_serialization split strand
  simpa [serializeStrand] using congrArg SerializedStrand.component serialized

theorem splitLeftStrand_orientation
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (strand : left.diagram.trace.StrandId) :
    (split.target.diagram.trace.strands
        (splitLeftStrand split strand)).orientation =
      (left.diagram.trace.strands strand).orientation := by
  have serialized := splitLeftStrand_serialization split strand
  simpa [serializeStrand] using congrArg SerializedStrand.orientation serialized

theorem splitRightStrand_component_value
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (strand : right.diagram.trace.StrandId) :
    (split.target.diagram.trace.strands
        (splitRightStrand split strand)).component.1 =
      left.diagram.trace.componentCount +
        (right.diagram.trace.strands strand).component.1 := by
  have serialized := splitRightStrand_serialization split strand
  simpa [serializeStrand, shiftSerializedStrand] using
    congrArg SerializedStrand.component serialized

theorem splitRightStrand_orientation
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (strand : right.diagram.trace.StrandId) :
    (split.target.diagram.trace.strands
        (splitRightStrand split strand)).orientation =
      (right.diagram.trace.strands strand).orientation := by
  have serialized := splitRightStrand_serialization split strand
  simpa [serializeStrand, shiftSerializedStrand] using
    congrArg SerializedStrand.orientation serialized

/-- The left component keeps its index in the split target diagram. -/
def splitLeftComponent
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right) :
    left.diagram.trace.ComponentId -> split.target.diagram.trace.ComponentId :=
  fun component =>
    ⟨component.1, by
      have lengths := congrArg List.length split.components_split
      simp [serializedComponents] at lengths
      omega⟩

/-- The right component is shifted past all left components. -/
def splitRightComponent
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right) :
    right.diagram.trace.ComponentId -> split.target.diagram.trace.ComponentId :=
  fun component =>
    ⟨left.diagram.trace.componentCount + component.1, by
      have lengths := congrArg List.length split.components_split
      simp [serializedComponents] at lengths
      omega⟩

theorem splitLeftComponent_data
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (component : left.diagram.trace.ComponentId) :
    split.target.diagram.trace.components (splitLeftComponent split component) =
      left.diagram.trace.components component := by
  have targetBound :
      component.1 < split.target.diagram.trace.componentCount := by
    have lengths := congrArg List.length split.components_split
    simp [serializedComponents] at lengths
    omega
  have atIndex := congrArg
    (fun components => components[component.1]?) split.components_split
  simp [serializedComponents, splitLeftComponent, component.2,
    targetBound] at atIndex
  rw [List.getElem?_append_left (by simp [component.2])] at atIndex
  simp at atIndex
  exact atIndex

theorem splitRightComponent_data
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (component : right.diagram.trace.ComponentId) :
    split.target.diagram.trace.components (splitRightComponent split component) =
      right.diagram.trace.components component := by
  have targetBound :
      left.diagram.trace.componentCount + component.1 <
        split.target.diagram.trace.componentCount := by
    have lengths := congrArg List.length split.components_split
    simp [serializedComponents] at lengths
    omega
  have atIndex := congrArg
    (fun components =>
      components[left.diagram.trace.componentCount + component.1]?)
    split.components_split
  simp [serializedComponents, splitRightComponent, component.2,
    targetBound] at atIndex
  simpa [splitRightComponent] using atIndex

theorem splitLeftStrand_component
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (strand : left.diagram.trace.StrandId) :
    (split.target.diagram.trace.strands
        (splitLeftStrand split strand)).component =
      splitLeftComponent split
        (left.diagram.trace.strands strand).component := by
  apply Fin.ext
  exact splitLeftStrand_component_value split strand

theorem splitRightStrand_component
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (strand : right.diagram.trace.StrandId) :
    (split.target.diagram.trace.strands
        (splitRightStrand split strand)).component =
      splitRightComponent split
        (right.diagram.trace.strands strand).component := by
  apply Fin.ext
  exact splitRightStrand_component_value split strand

def splitLeftTraceEmbedding
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right) :
    TraceEmbedding left.diagram.trace split.target.diagram.trace where
  component := splitLeftComponent split
  strand := splitLeftStrand split
  component_data := splitLeftComponent_data split
  strand_component := splitLeftStrand_component split
  strand_orientation := splitLeftStrand_orientation split

def splitRightTraceEmbedding
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right) :
    TraceEmbedding right.diagram.trace split.target.diagram.trace where
  component := splitRightComponent split
  strand := splitRightStrand split
  component_data := splitRightComponent_data split
  strand_component := splitRightStrand_component split
  strand_orientation := splitRightStrand_orientation split

/-- The target label on an embedded left strand is the original left label. -/
theorem splitLeft_exteriorStrandLabel
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (strand : left.diagram.trace.StrandId) :
    exteriorStrandLabel 𝒞 split.target.diagram labeling
        (splitLeftStrand split strand) =
      exteriorStrandLabel 𝒞 left.diagram
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).1 strand := by
  let sourceComponent := (left.diagram.trace.strands strand).component
  let targetComponent := splitLeftComponent split sourceComponent
  have strandComponent :
      (split.target.diagram.trace.strands
          (splitLeftStrand split strand)).component = targetComponent :=
    splitLeftStrand_component split strand
  have componentData :
      split.target.diagram.trace.components targetComponent =
        left.diagram.trace.components sourceComponent :=
    splitLeftComponent_data split sourceComponent
  unfold exteriorStrandLabel
  rw [strandComponent]
  by_cases sourceRole :
      (left.diagram.trace.components sourceComponent).role ≠ .dotted
  · have targetRole :
        (split.target.diagram.trace.components targetComponent).role ≠
          .dotted := by
      simpa [componentData] using sourceRole
    rw [dif_pos sourceRole, dif_pos targetRole]
    rw [splitTwoHandleLabelingEquiv_left]
    apply congrArg labeling
    apply split.target.diagram.handles.twoHandleIndex.injective
    apply Subtype.ext
    apply Fin.ext
    simpa [targetComponent, splitLeftComponent] using
      ((split.leftTwoHandleComponent
        (left.diagram.handles.twoHandleIndex.symm
          ⟨sourceComponent, sourceRole⟩)).trans
        (congrArg (fun component => component.1.1)
          (left.diagram.handles.twoHandleIndex.apply_symm_apply
            ⟨sourceComponent, sourceRole⟩))).symm
  · have targetRole :
        ¬(split.target.diagram.trace.components targetComponent).role ≠
          .dotted := by
      simpa [componentData] using sourceRole
    rw [dif_neg sourceRole, dif_neg targetRole]

/-- The target label on an embedded right strand is the original right label. -/
theorem splitRight_exteriorStrandLabel
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (strand : right.diagram.trace.StrandId) :
    exteriorStrandLabel 𝒞 split.target.diagram labeling
        (splitRightStrand split strand) =
      exteriorStrandLabel 𝒞 right.diagram
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).2 strand := by
  let sourceComponent := (right.diagram.trace.strands strand).component
  let targetComponent := splitRightComponent split sourceComponent
  have strandComponent :
      (split.target.diagram.trace.strands
          (splitRightStrand split strand)).component = targetComponent :=
    splitRightStrand_component split strand
  have componentData :
      split.target.diagram.trace.components targetComponent =
        right.diagram.trace.components sourceComponent :=
    splitRightComponent_data split sourceComponent
  unfold exteriorStrandLabel
  rw [strandComponent]
  by_cases sourceRole :
      (right.diagram.trace.components sourceComponent).role ≠ .dotted
  · have targetRole :
        (split.target.diagram.trace.components targetComponent).role ≠
          .dotted := by
      simpa [componentData] using sourceRole
    rw [dif_pos sourceRole, dif_pos targetRole]
    rw [splitTwoHandleLabelingEquiv_right]
    apply congrArg labeling
    apply split.target.diagram.handles.twoHandleIndex.injective
    apply Subtype.ext
    apply Fin.ext
    simpa [targetComponent, splitRightComponent] using
      ((split.rightTwoHandleComponent
        (right.diagram.handles.twoHandleIndex.symm
          ⟨sourceComponent, sourceRole⟩)).trans
        (congrArg (left.diagram.trace.componentCount + ·)
          (congrArg (fun component => component.1.1)
            (right.diagram.handles.twoHandleIndex.apply_symm_apply
              ⟨sourceComponent, sourceRole⟩)))).symm
  · have targetRole :
        ¬(split.target.diagram.trace.components targetComponent).role ≠
          .dotted := by
      simpa [componentData] using sourceRole
    rw [dif_neg sourceRole, dif_neg targetRole]

theorem splitLeft_orientedExteriorStrand
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (strand : left.diagram.trace.StrandId) :
    orientedExteriorStrand 𝒞 split.target.diagram labeling
        (splitLeftStrand split strand) =
      orientedExteriorStrand 𝒞 left.diagram
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).1 strand := by
  exact congrArg₂
    (fun label direction =>
      ({ label := label, direction := direction } : OrientedSimple 𝒞))
    (splitLeft_exteriorStrandLabel split 𝒞 labeling strand)
    (congrArg ribbonDirectionOfStrandOrientation
      (splitLeftStrand_orientation split strand))

theorem splitRight_orientedExteriorStrand
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (strand : right.diagram.trace.StrandId) :
    orientedExteriorStrand 𝒞 split.target.diagram labeling
        (splitRightStrand split strand) =
      orientedExteriorStrand 𝒞 right.diagram
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).2 strand := by
  exact congrArg₂
    (fun label direction =>
      ({ label := label, direction := direction } : OrientedSimple 𝒞))
    (splitRight_exteriorStrandLabel split 𝒞 labeling strand)
    (congrArg ribbonDirectionOfStrandOrientation
      (splitRightStrand_orientation split strand))

theorem splitLeft_exteriorWord
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (word : List left.diagram.trace.StrandId) :
    exteriorWord 𝒞 split.target.diagram labeling
        (word.map (splitLeftStrand split)) =
      exteriorWord 𝒞 left.diagram
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).1 word := by
  induction word with
  | nil => rfl
  | cons strand rest ih =>
      exact congrArg₂ List.cons
        (splitLeft_orientedExteriorStrand split 𝒞 labeling strand) ih

theorem splitRight_exteriorWord
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (word : List right.diagram.trace.StrandId) :
    exteriorWord 𝒞 split.target.diagram labeling
        (word.map (splitRightStrand split)) =
      exteriorWord 𝒞 right.diagram
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).2 word := by
  induction word with
  | nil => rfl
  | cons strand rest ih =>
      exact congrArg₂ List.cons
        (splitRight_orientedExteriorStrand split 𝒞 labeling strand) ih

theorem split_eventCount
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right) :
    split.target.cut.cut.exterior.eventCount =
      left.cut.cut.exterior.eventCount + right.cut.cut.exterior.eventCount := by
  have lengths := congrArg List.length split.events_split
  simpa [serializedExteriorEvents] using lengths

/-- Serialization records exactly the active word at every trace state. -/
theorem serializedActiveOrders_lookup
    {diagram : SpecialKirbyDiagram}
    (presentation : DottedCutPresentation diagram)
    (state : Fin (presentation.cut.exterior.eventCount + 1)) :
    (serializedActiveOrders presentation)[state.1]? =
      some (List.map Fin.val
        (presentation.cut.exterior.activeOrder state)) := by
  rcases state with ⟨_ | state, stateBound⟩
  · simp [serializedActiveOrders]
  · have eventBound : state < presentation.cut.exterior.eventCount := by omega
    simp [serializedActiveOrders, eventBound]

/-- A state in the left trace keeps its state index in the target trace. -/
def splitLeftState
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right) :
    Fin (left.cut.cut.exterior.eventCount + 1) ->
      Fin (split.target.cut.cut.exterior.eventCount + 1) :=
  fun state =>
    ⟨state.1, by rw [split_eventCount split]; omega⟩

/-- Every left active word is literally the corresponding prefix state of the target. -/
theorem splitLeft_activeOrder
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (state : Fin (left.cut.cut.exterior.eventCount + 1)) :
    split.target.cut.cut.exterior.activeOrder (splitLeftState split state) =
      (left.cut.cut.exterior.activeOrder state).map
        (splitLeftStrand split) := by
  apply List.map_injective_iff.mpr Fin.val_injective
  have atIndex := congrArg
    (fun states => states[state.1]?) split.activeOrders_split
  simp only at atIndex
  have targetLookup :
      (serializedActiveOrders split.target.cut)[state.1]? =
        some (List.map Fin.val
          (split.target.cut.cut.exterior.activeOrder
            (splitLeftState split state))) := by
    simpa [splitLeftState] using
      (serializedActiveOrders_lookup split.target.cut
        (splitLeftState split state))
  rw [targetLookup] at atIndex
  rw [List.getElem?_append_left (by
    simp [serializedActiveOrders, state.2])] at atIndex
  rw [serializedActiveOrders_lookup left.cut state] at atIndex
  have atIndex := Option.some.inj atIndex
  have embeddedValues :
      List.map (@Fin.val left.diagram.trace.strandCount)
          (left.cut.cut.exterior.activeOrder state) =
        List.map (@Fin.val split.target.diagram.trace.strandCount)
          ((left.cut.cut.exterior.activeOrder state).map
            (splitLeftStrand split)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro strand _membership
    exact (splitLeftStrand_value split strand).symm
  exact atIndex.trans embeddedValues

theorem splitLeft_exteriorWord_atState
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (state : Fin (left.cut.cut.exterior.eventCount + 1)) :
    exteriorWord 𝒞 split.target.diagram labeling
        (split.target.cut.cut.exterior.activeOrder
          (splitLeftState split state)) =
      exteriorWord 𝒞 left.diagram
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).1
        (left.cut.cut.exterior.activeOrder state) := by
  rw [splitLeft_activeOrder split state]
  exact splitLeft_exteriorWord split 𝒞 labeling _

/-- A state in the right trace is shifted past all left events. -/
def splitRightState
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right) :
    Fin (right.cut.cut.exterior.eventCount + 1) ->
      Fin (split.target.cut.cut.exterior.eventCount + 1) :=
  fun state =>
    ⟨left.cut.cut.exterior.eventCount + state.1, by
      rw [split_eventCount split]
      omega⟩

/-- Every right active word is the corresponding shifted suffix state of the target. -/
theorem splitRight_activeOrder
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (state : Fin (right.cut.cut.exterior.eventCount + 1)) :
    split.target.cut.cut.exterior.activeOrder (splitRightState split state) =
      (right.cut.cut.exterior.activeOrder state).map
        (splitRightStrand split) := by
  by_cases stateZero : state.1 = 0
  · have stateEq : state = 0 := Fin.ext stateZero
    subst state
    have targetStateEq :
        splitRightState split 0 =
          splitLeftState split
            (Fin.last left.cut.cut.exterior.eventCount) := by
      apply Fin.ext
      simp [splitRightState, splitLeftState]
    rw [targetStateEq, splitLeft_activeOrder]
    rw [left.cut.cut.exterior.finalBoundaryEmpty,
      right.cut.cut.exterior.initialBoundaryEmpty]
    rfl
  · obtain ⟨index, stateValue⟩ := Nat.exists_eq_succ_of_ne_zero stateZero
    have atIndex := congrArg
      (fun states =>
        states[left.cut.cut.exterior.eventCount + index + 1]?)
      split.activeOrders_split
    simp only at atIndex
    have stateBound : index + 1 < right.cut.cut.exterior.eventCount + 1 := by
      omega
    have stateEq : state = ⟨index + 1, stateBound⟩ := by
      apply Fin.ext
      exact stateValue
    subst state
    apply List.map_injective_iff.mpr Fin.val_injective
    have targetLookup :
        (serializedActiveOrders split.target.cut)[
            left.cut.cut.exterior.eventCount + index + 1]? =
          some (List.map Fin.val
            (split.target.cut.cut.exterior.activeOrder
              (splitRightState split ⟨index + 1, stateBound⟩))) := by
      simpa [splitRightState] using
        (serializedActiveOrders_lookup split.target.cut
          (splitRightState split ⟨index + 1, stateBound⟩))
    rw [targetLookup] at atIndex
    rw [List.getElem?_append_right (by
      simp [serializedActiveOrders])] at atIndex
    simp [serializedActiveOrders, splitRightState,
      shiftSerializedActiveOrder, List.map_map, stateBound] at atIndex
    rcases atIndex with ⟨_lookupBound, atIndex⟩
    have embeddedValues :
        List.map
            ((left.diagram.trace.strandCount + ·) ∘
              (@Fin.val right.diagram.trace.strandCount))
            (right.cut.cut.exterior.activeOrder
              ⟨index + 1, stateBound⟩) =
          List.map (@Fin.val split.target.diagram.trace.strandCount)
            ((right.cut.cut.exterior.activeOrder
              ⟨index + 1, stateBound⟩).map
                (splitRightStrand split)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro strand _membership
      exact (splitRightStrand_value split strand).symm
    exact atIndex.trans embeddedValues

theorem splitRight_exteriorWord_atState
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (state : Fin (right.cut.cut.exterior.eventCount + 1)) :
    exteriorWord 𝒞 split.target.diagram labeling
        (split.target.cut.cut.exterior.activeOrder
          (splitRightState split state)) =
      exteriorWord 𝒞 right.diagram
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).2
        (right.cut.cut.exterior.activeOrder state) := by
  rw [splitRight_activeOrder split state]
  exact splitRight_exteriorWord split 𝒞 labeling _

def splitLeftEvent
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right) :
    Fin left.cut.cut.exterior.eventCount ->
      Fin split.target.cut.cut.exterior.eventCount :=
  fun event =>
    ⟨event.1, by rw [split_eventCount split]; omega⟩

def splitRightEvent
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right) :
    Fin right.cut.cut.exterior.eventCount ->
      Fin split.target.cut.cut.exterior.eventCount :=
  fun event =>
    ⟨left.cut.cut.exterior.eventCount + event.1, by
      rw [split_eventCount split]
      omega⟩

theorem splitLeftEvent_serialization
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (event : Fin left.cut.cut.exterior.eventCount) :
    serializeCutOpenEvent
        (split.target.cut.cut.exterior.events
          (splitLeftEvent split event)) =
      serializeCutOpenEvent (left.cut.cut.exterior.events event) := by
  have targetBound :
      event.1 < split.target.cut.cut.exterior.eventCount := by
    rw [split_eventCount split]
    omega
  have atIndex := congrArg (fun events => events[event.1]?) split.events_split
  simp [serializedExteriorEvents, splitLeftEvent, event.2,
    targetBound] at atIndex
  rw [List.getElem?_append_left (by simp [event.2])] at atIndex
  simp at atIndex
  exact atIndex

theorem splitRightEvent_serialization
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (event : Fin right.cut.cut.exterior.eventCount) :
    serializeCutOpenEvent
        (split.target.cut.cut.exterior.events
          (splitRightEvent split event)) =
      shiftSerializedCutOpenEvent
          left.diagram.trace.componentCount
          left.diagram.trace.strandCount
          (serializeCutOpenEvent (right.cut.cut.exterior.events event)) := by
  have targetBound :
      left.cut.cut.exterior.eventCount + event.1 <
        split.target.cut.cut.exterior.eventCount := by
    rw [split_eventCount split]
    omega
  have atIndex := congrArg
      (fun events => events[left.cut.cut.exterior.eventCount + event.1]?)
    split.events_split
  simp [serializedExteriorEvents, splitRightEvent, event.2,
    targetBound] at atIndex
  simpa [splitRightEvent] using atIndex

theorem splitLeftTraceEmbedding_event_serialization
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (event : CutOpenEvent left.diagram.trace) :
    serializeCutOpenEvent ((splitLeftTraceEmbedding split).event event) =
      serializeCutOpenEvent event := by
  cases event <;>
    simp [TraceEmbedding.event, TraceEmbedding.puncture,
      splitLeftTraceEmbedding, splitLeftComponent, splitLeftStrand,
      serializeCutOpenEvent, serializePuncture, List.map_map]

theorem splitRightTraceEmbedding_event_serialization
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (event : CutOpenEvent right.diagram.trace) :
    serializeCutOpenEvent ((splitRightTraceEmbedding split).event event) =
      shiftSerializedCutOpenEvent
        left.diagram.trace.componentCount
        left.diagram.trace.strandCount
        (serializeCutOpenEvent event) := by
  cases event <;>
    simp [TraceEmbedding.event, TraceEmbedding.puncture,
      splitRightTraceEmbedding, splitRightComponent, splitRightStrand,
      shiftSerializedCutOpenEvent, shiftSerializedPuncture,
      serializeCutOpenEvent, serializePuncture, List.map_map,
      Nat.add_assoc]

theorem splitLeftEvent_eq_mapped
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (event : Fin left.cut.cut.exterior.eventCount) :
    split.target.cut.cut.exterior.events (splitLeftEvent split event) =
      (splitLeftTraceEmbedding split).event
        (left.cut.cut.exterior.events event) := by
  apply TwistedYetter.Kirby.Final.Proofs.serializeCutOpenEvent_injective
  rw [splitLeftEvent_serialization]
  exact
    (splitLeftTraceEmbedding_event_serialization split _).symm

theorem splitRightEvent_eq_mapped
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (event : Fin right.cut.cut.exterior.eventCount) :
    split.target.cut.cut.exterior.events (splitRightEvent split event) =
      (splitRightTraceEmbedding split).event
        (right.cut.cut.exterior.events event) := by
  apply TwistedYetter.Kirby.Final.Proofs.serializeCutOpenEvent_injective
  rw [splitRightEvent_serialization]
  exact
    (splitRightTraceEmbedding_event_serialization split _).symm

theorem splitLeft_contextualMorphism
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (event : Fin left.cut.cut.exterior.eventCount) :
    HEq
      (compileRoleAwareContextualCutOpenEventMorphism 𝒞
        split.target.diagram split.target.cut labeling
        (splitLeftEvent split event))
      (compileRoleAwareContextualCutOpenEventMorphism 𝒞
        left.diagram left.cut
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).1 event) := by
  rw [compileRoleAwareContextualCutOpenEventMorphism_eq_elementary,
    compileRoleAwareContextualCutOpenEventMorphism_eq_elementary]
  apply (splitLeftTraceEmbedding split).compileContextualMorphism_heq 𝒞
    left.cut split.target.cut
    (splitTwoHandleLabelingEquiv split 𝒞 labeling).1 labeling
    (splitLeft_orientedExteriorStrand split 𝒞 labeling)
    event (splitLeftEvent split event)
    (splitLeftEvent_eq_mapped split event)
  · simpa [splitLeftEvent, splitLeftState] using
      splitLeft_activeOrder split event.castSucc
  · simpa [splitLeftEvent, splitLeftState] using
      splitLeft_activeOrder split event.succ

theorem splitRight_contextualMorphism
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram)
    (event : Fin right.cut.cut.exterior.eventCount) :
    HEq
      (compileRoleAwareContextualCutOpenEventMorphism 𝒞
        split.target.diagram split.target.cut labeling
        (splitRightEvent split event))
      (compileRoleAwareContextualCutOpenEventMorphism 𝒞
        right.diagram right.cut
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).2 event) := by
  rw [compileRoleAwareContextualCutOpenEventMorphism_eq_elementary,
    compileRoleAwareContextualCutOpenEventMorphism_eq_elementary]
  apply (splitRightTraceEmbedding split).compileContextualMorphism_heq 𝒞
    right.cut split.target.cut
    (splitTwoHandleLabelingEquiv split 𝒞 labeling).2 labeling
    (splitRight_orientedExteriorStrand split 𝒞 labeling)
    event (splitRightEvent split event)
    (splitRightEvent_eq_mapped split event)
  · simpa [splitRightEvent, splitRightState] using
      splitRight_activeOrder split event.castSucc
  · simpa [splitRightEvent, splitRightState] using
      splitRight_activeOrder split event.succ

noncomputable def splitTargetTrace
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram) :
    FiniteMorphismTrace 𝒞.C
      (left.cut.cut.exterior.eventCount + right.cut.cut.exterior.eventCount) :=
  TwistedYetter.Semantics.Independent.FiniteMorphismTrace.castEventCount
    (split_eventCount split).symm
    (compiledExteriorTrace 𝒞 split.target.diagram split.target.cut labeling)

theorem splitTargetTrace_takePrefix
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram) :
    FiniteMorphismTrace.takePrefix (splitTargetTrace split 𝒞 labeling) =
      compiledExteriorTrace 𝒞 left.diagram left.cut
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).1 := by
  apply TwistedYetter.Semantics.Independent.FiniteMorphismTrace.eq_of_object_edge
  · intro state
    exact congrArg (ribbonWordObject 𝒞)
      (splitLeft_exteriorWord_atState split 𝒞 labeling state)
  · intro event
    exact splitLeft_contextualMorphism split 𝒞 labeling event

theorem splitTargetTrace_dropPrefix
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram) :
    FiniteMorphismTrace.dropPrefix (splitTargetTrace split 𝒞 labeling) =
      compiledExteriorTrace 𝒞 right.diagram right.cut
        (splitTwoHandleLabelingEquiv split 𝒞 labeling).2 := by
  apply TwistedYetter.Semantics.Independent.FiniteMorphismTrace.eq_of_object_edge
  · intro state
    exact congrArg (ribbonWordObject 𝒞)
      (splitRight_exteriorWord_atState split 𝒞 labeling state)
  · intro event
    exact splitRight_contextualMorphism split 𝒞 labeling event

theorem splitTargetTrace_composeAll
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (category : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling category split.target.diagram) :
    HEq (splitTargetTrace split category labeling).composeAll
      (compileCutOpenExteriorMorphism category left.diagram left.cut
          (splitTwoHandleLabelingEquiv split category labeling).1 ≫
        compileCutOpenExteriorMorphism category right.diagram right.cut
          (splitTwoHandleLabelingEquiv split category labeling).2) := by
  have decomposition :=
    FiniteMorphismTrace.composeAll_eq_prefix_comp_dropPrefix
      (splitTargetTrace split category labeling)
  rw [← FiniteMorphismTrace.takePrefix_composeAll] at decomposition
  have leftTraceToClosed :
      HEq
        (FiniteMorphismTrace.takePrefix
          (splitTargetTrace split category labeling)).composeAll
        (compileCutOpenExteriorMorphism category left.diagram left.cut
          (splitTwoHandleLabelingEquiv split category labeling).1) :=
    (FiniteMorphismTrace.composeAll_heq_of_eq
      (splitTargetTrace_takePrefix split category labeling)).trans
        (compileCutOpenExteriorMorphism_heq_compiledTrace category
          left.diagram left.cut
          (splitTwoHandleLabelingEquiv split category labeling).1).symm
  have rightTraceToClosed :
      HEq
        (FiniteMorphismTrace.dropPrefix
          (splitTargetTrace split category labeling)).composeAll
        (compileCutOpenExteriorMorphism category right.diagram right.cut
          (splitTwoHandleLabelingEquiv split category labeling).2) :=
    (FiniteMorphismTrace.composeAll_heq_of_eq
      (splitTargetTrace_dropPrefix split category labeling)).trans
        (compileCutOpenExteriorMorphism_heq_compiledTrace category
          right.diagram right.cut
          (splitTwoHandleLabelingEquiv split category labeling).2).symm
  have leftSourceObjectEq :
      (FiniteMorphismTrace.takePrefix
          (splitTargetTrace split category labeling)).object 0 =
        MonoidalCategoryStruct.tensorUnit category.C := by
    rw [splitTargetTrace_takePrefix]
    change ribbonWordObject category
      (exteriorWord category left.diagram
        (splitTwoHandleLabelingEquiv split category labeling).1
        (left.cut.cut.exterior.activeOrder 0)) =
          MonoidalCategoryStruct.tensorUnit category.C
    rw [left.cut.cut.exterior.initialBoundaryEmpty]
    rfl
  have leftTargetObjectEq :
      (FiniteMorphismTrace.takePrefix
          (splitTargetTrace split category labeling)).object
          (Fin.last left.cut.cut.exterior.eventCount) =
        MonoidalCategoryStruct.tensorUnit category.C := by
    rw [splitTargetTrace_takePrefix]
    change ribbonWordObject category
      (exteriorWord category left.diagram
        (splitTwoHandleLabelingEquiv split category labeling).1
        (left.cut.cut.exterior.activeOrder
          (Fin.last left.cut.cut.exterior.eventCount))) =
            MonoidalCategoryStruct.tensorUnit category.C
    rw [left.cut.cut.exterior.finalBoundaryEmpty]
    rfl
  have rightTargetObjectEq :
      (FiniteMorphismTrace.dropPrefix
          (splitTargetTrace split category labeling)).object
          (Fin.last right.cut.cut.exterior.eventCount) =
        MonoidalCategoryStruct.tensorUnit category.C := by
    rw [splitTargetTrace_dropPrefix]
    change ribbonWordObject category
      (exteriorWord category right.diagram
        (splitTwoHandleLabelingEquiv split category labeling).2
        (right.cut.cut.exterior.activeOrder
          (Fin.last right.cut.cut.exterior.eventCount))) =
            MonoidalCategoryStruct.tensorUnit category.C
    rw [right.cut.cut.exterior.finalBoundaryEmpty]
    rfl
  have composed :
      HEq
        ((FiniteMorphismTrace.takePrefix
            (splitTargetTrace split category labeling)).composeAll ≫
          (FiniteMorphismTrace.dropPrefix
            (splitTargetTrace split category labeling)).composeAll)
        (compileCutOpenExteriorMorphism category left.diagram left.cut
            (splitTwoHandleLabelingEquiv split category labeling).1 ≫
          compileCutOpenExteriorMorphism category right.diagram right.cut
            (splitTwoHandleLabelingEquiv split category labeling).2) := by
    exact CategoryTheory.heq_comp
      leftSourceObjectEq leftTargetObjectEq rightTargetObjectEq
      leftTraceToClosed rightTraceToClosed
  exact (heq_of_eq decomposition).trans composed

/-- The closed graphical morphism of a split presentation is the composite of both factors. -/
theorem split_compileCutOpenExteriorMorphism
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram) :
    compileCutOpenExteriorMorphism 𝒞 split.target.diagram
        split.target.cut labeling =
      compileCutOpenExteriorMorphism 𝒞 left.diagram left.cut
          (splitTwoHandleLabelingEquiv split 𝒞 labeling).1 ≫
        compileCutOpenExteriorMorphism 𝒞 right.diagram right.cut
          (splitTwoHandleLabelingEquiv split 𝒞 labeling).2 := by
  have targetToCompiled :=
    compileCutOpenExteriorMorphism_heq_compiledTrace 𝒞
      split.target.diagram split.target.cut labeling
  have castToTarget :=
    TwistedYetter.Semantics.Independent.FiniteMorphismTrace.castEventCount_composeAll
      (split_eventCount split).symm
      (compiledExteriorTrace 𝒞 split.target.diagram split.target.cut labeling)
  have targetToSplit :
      HEq
        (compileCutOpenExteriorMorphism 𝒞 split.target.diagram
          split.target.cut labeling)
        (splitTargetTrace split 𝒞 labeling).composeAll :=
    targetToCompiled.trans castToTarget.symm
  exact eq_of_heq
    (targetToSplit.trans
      (splitTargetTrace_composeAll split 𝒞 labeling))

theorem split_canonicalRibbonGraphicalEvaluation
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞η : TwistedPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞η.category split.target.diagram)
    (targetCycle : ThamTwoCycles split.target.primalBoundary)
    (leftCycle : ThamTwoCycles left.primalBoundary)
    (rightCycle : ThamTwoCycles right.primalBoundary) :
    canonicalRibbonGraphicalEvaluation 𝒞η.category
        (canonicalRoleAwareGraphCompiler 𝒞η split.target.diagram
          split.target.cut split.target.primalBoundary labeling targetCycle) =
      canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler 𝒞η left.diagram left.cut
            left.primalBoundary
            (splitTwoHandleLabelingEquiv split 𝒞η.category labeling).1
            leftCycle) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (canonicalRoleAwareGraphCompiler 𝒞η right.diagram right.cut
            right.primalBoundary
            (splitTwoHandleLabelingEquiv split 𝒞η.category labeling).2
            rightCycle) := by
  unfold canonicalRoleAwareGraphCompiler
  rw [split_compileCutOpenExteriorMorphism]
  exact canonicalRibbonGraphicalEvaluation_comp 𝒞η.category _ _

/-- Ordinary Kirby-colour dimensions multiply across the split union. -/
theorem split_ordinaryKirbyWeight
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 split.target.diagram) :
    ordinaryKirbyWeight 𝒞 labeling =
      ordinaryKirbyWeight 𝒞
          (splitTwoHandleLabelingEquiv split 𝒞 labeling).1 *
        ordinaryKirbyWeight 𝒞
          (splitTwoHandleLabelingEquiv split 𝒞 labeling).2 := by
  unfold ordinaryKirbyWeight
  rw [Fintype.prod_equiv split.twoHandleEquiv
    (fun handle => 𝒞.simples.quantumDimension (labeling handle))
    (fun handle =>
      𝒞.simples.quantumDimension
        (labeling (split.twoHandleEquiv.symm handle))) (by simp)]
  rw [Fintype.prod_sum_type]
  rfl

/-- Homological character weights multiply across the split marking. -/
theorem split_characterWeight
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (marking : SplitMarkingNaturality split)
    (𝒞η : TwistedPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞η.category split.target.diagram) :
    characterWeight 𝒞η labeling marking.targetCycle =
      characterWeight 𝒞η
          (splitTwoHandleLabelingEquiv split 𝒞η.category labeling).1
          marking.leftCycle *
        characterWeight 𝒞η
          (splitTwoHandleLabelingEquiv split 𝒞η.category labeling).2
          marking.rightCycle := by
  unfold characterWeight
  rw [Fintype.prod_equiv split.twoHandleEquiv
    (fun handle =>
      (𝒞η.character.value (labeling handle)) ^
        (marking.targetCycle.1 handle))
    (fun handle =>
      (𝒞η.character.value
          (labeling (split.twoHandleEquiv.symm handle))) ^
        (marking.targetCycle.1
          (split.twoHandleEquiv.symm handle))) (by simp)]
  rw [Fintype.prod_sum_type]
  simp only [splitTwoHandleLabelingEquiv_left,
    splitTwoHandleLabelingEquiv_right]
  simp_rw [marking.left_coordinates, marking.right_coordinates]
  rfl

/-- The THAM normalization of a split presentation contributes one factor `D⁻¹`. -/
theorem split_thamNormalization
    (globalDimension : K)
    (globalDimension_ne_zero : globalDimension ≠ 0)
    (leftHThree rightHThree targetHThree : ℕ)
    (targetHThree_eq : targetHThree = leftHThree + rightHThree)
    (leftRaw rightRaw : K) :
    thamDefinition511Normalization globalDimension targetHThree 0 0 *
        (leftRaw * rightRaw) =
      globalDimension⁻¹ *
        (thamDefinition511Normalization globalDimension leftHThree 0 0 *
          leftRaw) *
        (thamDefinition511Normalization globalDimension rightHThree 0 0 *
          rightRaw) := by
  subst targetHThree
  unfold thamDefinition511Normalization
  rw [pow_add]
  field_simp

theorem split_rawEvaluatorSummand
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (marking : SplitMarkingNaturality split)
    (𝒞η : TwistedPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞η.category split.target.diagram) :
    rawEvaluatorSummand 𝒞η split.target.diagram split.target.cut
        split.target.primalBoundary marking.targetCycle labeling =
      rawEvaluatorSummand 𝒞η left.diagram left.cut left.primalBoundary
          marking.leftCycle
          (splitTwoHandleLabelingEquiv split 𝒞η.category labeling).1 *
        rawEvaluatorSummand 𝒞η right.diagram right.cut right.primalBoundary
          marking.rightCycle
          (splitTwoHandleLabelingEquiv split 𝒞η.category labeling).2 := by
  unfold rawEvaluatorSummand
  rw [split_ordinaryKirbyWeight, split_characterWeight]
  rw [split_canonicalRibbonGraphicalEvaluation split 𝒞η labeling
    marking.targetCycle marking.leftCycle marking.rightCycle]
  ring

theorem split_rawCycleSum
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (marking : SplitMarkingNaturality split)
    (𝒞η : TwistedPremodularCategory K) :
    rawCycleSum 𝒞η split.target.diagram split.target.cut
        split.target.primalBoundary marking.targetCycle =
      rawCycleSum 𝒞η left.diagram left.cut left.primalBoundary
          marking.leftCycle *
        rawCycleSum 𝒞η right.diagram right.cut right.primalBoundary
          marking.rightCycle := by
  exact rawCycleSum_mul_of_labelingEquiv 𝒞η
    left.diagram right.diagram split.target.diagram
    left.cut right.cut split.target.cut
    left.primalBoundary right.primalBoundary split.target.primalBoundary
    marking.leftCycle marking.rightCycle marking.targetCycle
    (splitTwoHandleLabelingEquiv split 𝒞η.category)
    (split_rawEvaluatorSummand split marking 𝒞η)

theorem split_evaluateCycle
    {X Y : ClosedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (split : SplitSpecialKirbyPresentation left right)
    (marking : SplitMarkingNaturality split)
    (𝒞η : TwistedPremodularCategory K) :
    evaluateCycle 𝒞η split.target.diagram split.target.cut
        split.target.primalBoundary marking.targetCycle =
      𝒞η.category.globalDimension⁻¹ *
        evaluateCycle 𝒞η left.diagram left.cut left.primalBoundary
          marking.leftCycle *
        evaluateCycle 𝒞η right.diagram right.cut right.primalBoundary
          marking.rightCycle := by
  unfold evaluateCycle
  rw [split_rawCycleSum split marking 𝒞η]
  exact split_thamNormalization 𝒞η.category.globalDimension
    (egno_globalDimension_ne_zero 𝒞η.category)
    left.diagram.handles.hThree right.diagram.handles.hThree
    split.target.diagram.handles.hThree split.hThree_additive
    (rawCycleSum 𝒞η left.diagram left.cut left.primalBoundary
      marking.leftCycle)
    (rawCycleSum 𝒞η right.diagram right.cut right.primalBoundary
      marking.rightCycle)

theorem evaluateRepresentative_eq_cycle
    {X : ClosedOrientedSmoothFourManifold}
    (𝒞η : TwistedPremodularCategory K)
    (representative : SpecialKirbyRepresentativeOf X)
    (cycle : ThamTwoCycles representative.primalBoundary)
    (cycleClass :
      thamCycleClass representative.primalBoundary cycle =
        representative.thamAlpha) :
    evaluateMarkedDiagram 𝒞η representative.toHomologicallyMarkedDiagram =
      evaluateCycle 𝒞η representative.diagram representative.cut
        representative.primalBoundary cycle := by
  unfold evaluateMarkedDiagram evaluateMarking
  exact frozenFrontendRepresentativeIndependence 𝒞η
    representative.diagram representative.cut representative.primalBoundary
    (Quotient.out representative.thamAlpha) cycle
    ((Quotient.out_eq representative.thamAlpha).trans cycleClass.symm)

theorem TwistedYetter_eq_evaluateRepresentative
    {X : ClosedOrientedSmoothFourManifold}
    (𝒞η : TwistedPremodularCategory K)
    (alpha : ManifoldH₂ X)
    (representative : SpecialKirbyRepresentativeOf X)
    (correct : representative.representsHomologyClass alpha) :
    TwistedYetter 𝒞η ⟨X, alpha⟩ =
      evaluateMarkedDiagram 𝒞η representative.toHomologicallyMarkedDiagram := by
  unfold TwistedYetter
  let existence := specialKirbyRepresentative_exists X alpha
  have representativeCorrectIdentity :
      representative.representsHomologyClass
        (inducedH₂ (identityOrientedDiffeomorphism X) alpha) := by
    rw [inducedH₂_identityOrientedDiffeomorphism]
    exact correct
  exact ConditionalDescent.diffeomorphism_invariant_of_descent_data
    𝒞η
    (fun marked => frozenFrontendRepresentativeIndependence 𝒞η
      marked.diagram marked.cut marked.primalBoundary)
    (frozenFrontendLocalMoveInvariance 𝒞η)
    X X (identityOrientedDiffeomorphism X) alpha
    existence.choose existence.choose_spec
    representative representativeCorrectIdentity

/-- The marked connected-sum formula required by the stable no-go argument. -/
theorem markedConnectedSumFormula
    (𝒞η : TwistedPremodularCategory K) :
    MarkedConnectedSumFormula 𝒞η 𝒞η.category.globalDimension := by
  intro X Y alpha beta
  let leftExistence := specialKirbyRepresentative_exists X alpha
  let rightExistence := specialKirbyRepresentative_exists Y beta
  let left := leftExistence.choose
  let right := rightExistence.choose
  let split := Classical.choice
    (splitSpecialKirbyPresentation_exists left right)
  let marking := Classical.choice
    (splitSpecialKirbyPresentation_marking_natural split)
  have leftRepresents :
      left.diagramH₂EquivManifoldH₂ left.alpha = alpha :=
    leftExistence.choose_spec
  have rightRepresents :
      right.diagramH₂EquivManifoldH₂ right.alpha = beta :=
    rightExistence.choose_spec
  calc
    TwistedYetter 𝒞η
        ⟨connectedSum X Y, connectedSumMarking alpha beta⟩ =
        evaluateMarkedDiagram 𝒞η
          split.target.toHomologicallyMarkedDiagram :=
      TwistedYetter_eq_evaluateRepresentative 𝒞η _ split.target
        (by
          simpa [leftRepresents, rightRepresents] using
            marking.target_represents_connectedSum)
    _ = evaluateCycle 𝒞η split.target.diagram split.target.cut
          split.target.primalBoundary marking.targetCycle :=
      evaluateRepresentative_eq_cycle 𝒞η split.target marking.targetCycle
        marking.targetCycle_class
    _ = 𝒞η.category.globalDimension⁻¹ *
          evaluateCycle 𝒞η left.diagram left.cut left.primalBoundary
            marking.leftCycle *
          evaluateCycle 𝒞η right.diagram right.cut right.primalBoundary
            marking.rightCycle :=
      split_evaluateCycle split marking 𝒞η
    _ = 𝒞η.category.globalDimension⁻¹ *
          evaluateMarkedDiagram 𝒞η left.toHomologicallyMarkedDiagram *
          evaluateMarkedDiagram 𝒞η right.toHomologicallyMarkedDiagram := by
      rw [evaluateRepresentative_eq_cycle 𝒞η left marking.leftCycle
          marking.leftCycle_class,
        evaluateRepresentative_eq_cycle 𝒞η right marking.rightCycle
          marking.rightCycle_class]
    _ = 𝒞η.category.globalDimension⁻¹ *
          TwistedYetter 𝒞η ⟨X, alpha⟩ *
          TwistedYetter 𝒞η ⟨Y, beta⟩ := by
      rw [TwistedYetter_eq_evaluateRepresentative 𝒞η alpha left
          leftExistence.choose_spec,
        TwistedYetter_eq_evaluateRepresentative 𝒞η beta right
          rightExistence.choose_spec]

end

end TwistedYetter.StableNoGo
