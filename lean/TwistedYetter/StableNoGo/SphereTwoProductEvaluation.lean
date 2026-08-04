import TwistedYetter.StableNoGo.EntranceAxioms
import TwistedYetter.StableNoGo.CategoryEvidence
import TwistedYetter.StableNoGo.RawMultiplicativity

/-!
# The standard Hopf-link presentation of `S^2 \times S^2`

This file separates one classical topology identification from its ensuing
category calculation.  The diagram below is explicit finite data: two
zero-framed ordinary components, represented by two cups, two positive
crossings, and two caps.  The only external topology input says that this
specific diagram represents `S^2 \times S^2` with its zero marking.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final
open TwistedYetter.Kirby.Final.Proofs

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

private def positiveHopfComponents : Fin 2 -> Component
  | 0 => { role := .ordinary, orientation := .positive, integerFraming := 0 }
  | 1 => { role := .ordinary, orientation := .positive, integerFraming := 0 }

private def positiveHopfStrands : Fin 8 -> Strand 2
  | 0 => { component := 0, orientation := .positive }
  | 1 => { component := 0, orientation := .negative }
  | 2 => { component := 1, orientation := .positive }
  | 3 => { component := 1, orientation := .negative }
  | 4 => { component := 0, orientation := .positive }
  | 5 => { component := 1, orientation := .positive }
  | 6 => { component := 0, orientation := .positive }
  | 7 => { component := 1, orientation := .negative }

private def positiveHopfEvents : Fin 6 -> DiagramEvent 8
  | 0 => .birth 0 1
  | 1 => .birth 2 3
  | 2 => .crossing 0 2 4 5 .positive
  | 3 => .crossing 4 3 6 7 .positive
  | 4 => .death 5 7
  | 5 => .death 6 1

private def positiveHopfActiveOrder : Fin 7 -> List (Fin 8)
  | 0 => []
  | 1 => [0, 1]
  | 2 => [0, 2, 3, 1]
  | 3 => [5, 4, 3, 1]
  | 4 => [5, 7, 6, 1]
  | 5 => [6, 1]
  | 6 => []

private def positiveHopfInputEvent : Fin 8 → Fin 6
  | 0 => 2
  | 1 => 5
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 4

private def positiveHopfOutputEvent : Fin 8 → Fin 6
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 3

private theorem positiveHopf_uniqueInputAndOutput :
    EveryStrandHasUniqueInputAndOutput positiveHopfEvents := by
  intro strand
  constructor
  · refine ⟨positiveHopfInputEvent strand, ?_, ?_⟩
    · fin_cases strand <;>
        simp [StrandOccursAsInput, DiagramEvent.beforeWord,
          positiveHopfEvents, positiveHopfInputEvent]
    · intro event membership
      fin_cases strand <;> fin_cases event <;>
        simp [StrandOccursAsInput, DiagramEvent.beforeWord, positiveHopfEvents,
          positiveHopfInputEvent] at membership ⊢
  · refine ⟨positiveHopfOutputEvent strand, ?_, ?_⟩
    · fin_cases strand <;>
        simp [StrandOccursAsOutput, DiagramEvent.afterWord,
          positiveHopfEvents, positiveHopfOutputEvent]
    · intro event membership
      fin_cases strand <;> fin_cases event <;>
        simp [StrandOccursAsOutput, DiagramEvent.afterWord, positiveHopfEvents,
          positiveHopfOutputEvent] at membership ⊢

private theorem positiveHopf_everyComponentIsConnected :
    EveryComponentIsConnected positiveHopfStrands positiveHopfEvents := by
  intro component
  fin_cases component
  · refine ⟨(0 : Fin 8), rfl, ?_⟩
    intro strand component_eq
    fin_cases strand <;> simp [positiveHopfStrands] at component_eq
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by
        refine ⟨0, Or.inl ?_⟩
        decide)
    · exact Relation.ReflTransGen.single (by
        refine ⟨2, Or.inl ?_⟩
        decide)
    · exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single (by
          refine ⟨2, Or.inl ?_⟩
          change ((0 : Fin 8), (4 : Fin 8)) ∈
            (positiveHopfEvents (2 : Fin 6)).continuationPairs
          decide))
        (by
          refine ⟨3, Or.inl ?_⟩
          decide)
  · refine ⟨(2 : Fin 8), rfl, ?_⟩
    intro strand component_eq
    fin_cases strand <;> simp [positiveHopfStrands] at component_eq
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by
        refine ⟨1, Or.inl ?_⟩
        decide)
    · exact Relation.ReflTransGen.single (by
        refine ⟨2, Or.inl ?_⟩
        decide)
    · exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single (by
          refine ⟨1, Or.inl ?_⟩
          change ((2 : Fin 8), (3 : Fin 8)) ∈
            (positiveHopfEvents (1 : Fin 6)).continuationPairs
          decide))
        (by
          refine ⟨3, Or.inl ?_⟩
          decide)

/-- The explicit positive, zero-framed Hopf-link trace. -/
def positiveZeroFramedHopfTrace : CombinatorialLinkTrace where
  componentCount := 2
  strandCount := 8
  eventCount := 6
  components := positiveHopfComponents
  strands := positiveHopfStrands
  events := positiveHopfEvents
  activeOrder := positiveHopfActiveOrder
  initialBoundaryEmpty := rfl
  finalBoundaryEmpty := rfl
  transitionValid := by
    intro i
    fin_cases i
    · exact ⟨[], [], rfl, rfl⟩
    · exact ⟨[0], [1], rfl, rfl⟩
    · exact ⟨[], [3, 1], rfl, rfl⟩
    · exact ⟨[5], [1], rfl, rfl⟩
    · exact ⟨[], [6, 1], rfl, rfl⟩
    · exact ⟨[], [], rfl, rfl⟩
  activeWordsNoDuplicates := by
    intro i
    fin_cases i <;> decide
  eventPortsAreDistinct := by
    intro i
    fin_cases i <;> decide
  eventContinuationsAreWellFormed := by
    intro i first second membership
    fin_cases i
    · simp [positiveHopfEvents, DiagramEvent.continuationPairs] at membership
      rcases membership with ⟨rfl, rfl⟩
      simp [positiveHopfStrands, positiveHopfEvents]
    · simp [positiveHopfEvents, DiagramEvent.continuationPairs] at membership
      rcases membership with ⟨rfl, rfl⟩
      simp [positiveHopfStrands, positiveHopfEvents]
    · simp [positiveHopfEvents, DiagramEvent.continuationPairs] at membership
      rcases membership with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        simp [positiveHopfStrands, positiveHopfEvents]
    · simp [positiveHopfEvents, DiagramEvent.continuationPairs] at membership
      rcases membership with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        simp [positiveHopfStrands, positiveHopfEvents]
    · simp [positiveHopfEvents, DiagramEvent.continuationPairs] at membership
      rcases membership with ⟨rfl, rfl⟩
      simp [positiveHopfStrands, positiveHopfEvents]
    · simp [positiveHopfEvents, DiagramEvent.continuationPairs] at membership
      rcases membership with ⟨rfl, rfl⟩
      simp [positiveHopfStrands, positiveHopfEvents]
  everyStrandHasUniqueInputAndOutput := positiveHopf_uniqueInputAndOutput
  everyComponentIsConnected := positiveHopf_everyComponentIsConnected
  framingEventsMatchIntegerFraming := by
    classical
    intro component
    fin_cases component
    · change 0 = ∑ i : Fin 6,
        (positiveHopfEvents i).framingContribution 0 positiveHopfStrands
      symm
      apply Finset.sum_eq_zero
      intro i _
      fin_cases i <;>
        norm_num [positiveHopfEvents, DiagramEvent.framingContribution]
    · change 0 = ∑ i : Fin 6,
        (positiveHopfEvents i).framingContribution 1 positiveHopfStrands
      symm
      apply Finset.sum_eq_zero
      intro i _
      fin_cases i <;>
        norm_num [positiveHopfEvents, DiagramEvent.framingContribution]

private theorem positiveHopf_component_not_dotted
    (component : positiveZeroFramedHopfTrace.ComponentId) :
    (positiveZeroFramedHopfTrace.components component).role ≠ .dotted := by
  change Fin 2 at component
  fin_cases component <;>
    simp [positiveZeroFramedHopfTrace, positiveHopfComponents]

private def positiveHopfHandleData :
    SpecialHandleData positiveZeroFramedHopfTrace where
  hOne := 0
  hTwo := 2
  hThree := 0
  oneHandleIndex :=
    { toFun := fun empty => Fin.elim0 empty
      invFun := fun dotted =>
        False.elim (positiveHopf_component_not_dotted dotted.1 dotted.2)
      left_inv := fun empty => Fin.elim0 empty
      right_inv := fun dotted =>
        False.elim (positiveHopf_component_not_dotted dotted.1 dotted.2) }
  twoHandleIndex :=
    { toFun := fun component => ⟨component, by
          fin_cases component <;> decide⟩
      invFun := fun component => component.1
      left_inv := by intro component; rfl
      right_inv := by intro component; cases component; rfl }
  boundaryTwo := 0
  boundaryThree := 0
  boundary_squared_zero := rfl

/-- The standard Kirby diagram for `S^2 \times S^2`. -/
def positiveZeroFramedHopfDiagram : SpecialKirbyDiagram where
  trace := positiveZeroFramedHopfTrace
  handles := positiveHopfHandleData

private def positiveHopfTwoHandleEquiv :
    Fin positiveZeroFramedHopfDiagram.handles.hTwo ≃ Fin 2 :=
  positiveHopfHandleData.twoHandleIndex.trans
    { toFun := fun component => component.1
      invFun := fun component =>
        ⟨component, positiveHopf_component_not_dotted component⟩
      left_inv := by intro component; cases component; rfl
      right_inv := by intro component; rfl }

private def positiveHopfFirstHandle :
    Fin positiveZeroFramedHopfDiagram.handles.hTwo :=
  positiveHopfHandleData.twoHandleIndex.symm
    ⟨(0 : Fin 2), by
      decide⟩

private def positiveHopfSecondHandle :
    Fin positiveZeroFramedHopfDiagram.handles.hTwo :=
  positiveHopfHandleData.twoHandleIndex.symm
    ⟨(1 : Fin 2), by
      decide⟩

@[simp]
private theorem positiveHopfTwoHandleEquiv_symm_zero :
    positiveHopfTwoHandleEquiv.symm 0 = positiveHopfFirstHandle := by
  apply positiveHopfHandleData.twoHandleIndex.injective
  apply Subtype.ext
  rfl

@[simp]
private theorem positiveHopfTwoHandleEquiv_symm_one :
    positiveHopfTwoHandleEquiv.symm 1 = positiveHopfSecondHandle := by
  apply positiveHopfHandleData.twoHandleIndex.injective
  apply Subtype.ext
  rfl

@[simp]
private theorem positiveHopf_twoHandleIndex_symm
    (component : positiveZeroFramedHopfTrace.ComponentId)
    (notDotted :
      (positiveZeroFramedHopfTrace.components component).role ≠ .dotted) :
    positiveHopfHandleData.twoHandleIndex.symm
        ⟨component, notDotted⟩ = component := by
  change Fin 2 at component
  fin_cases component <;> rfl

private def positiveHopfToCutOpenEvent
    (event : DiagramEvent positiveZeroFramedHopfTrace.strandCount) :
    CutOpenEvent positiveZeroFramedHopfTrace :=
  match event with
  | .birth left right => .birth left right
  | .death left right => .death left right
  | .crossing overInput underInput overOutput underOutput sign =>
      .crossing overInput underInput overOutput underOutput sign
  | .framingTwist input output sign => .framingTwist input output sign
  | .planarIsotopy continuations => .planarIsotopy continuations

private theorem positiveHopfToCutOpenEvent_beforeWord
    (event : DiagramEvent positiveZeroFramedHopfTrace.strandCount) :
    (positiveHopfToCutOpenEvent event).beforeWord = event.beforeWord := by
  cases event <;> rfl

private theorem positiveHopfToCutOpenEvent_afterWord
    (event : DiagramEvent positiveZeroFramedHopfTrace.strandCount) :
    (positiveHopfToCutOpenEvent event).afterWord = event.afterWord := by
  cases event <;> rfl

private def positiveHopfCutOpenExterior :
    CutOpenExteriorTrace positiveZeroFramedHopfTrace where
  eventCount := positiveZeroFramedHopfTrace.eventCount
  events := fun i => positiveHopfToCutOpenEvent
    (positiveZeroFramedHopfTrace.events i)
  activeOrder := positiveZeroFramedHopfTrace.activeOrder
  initialBoundaryEmpty := positiveZeroFramedHopfTrace.initialBoundaryEmpty
  finalBoundaryEmpty := positiveZeroFramedHopfTrace.finalBoundaryEmpty
  transitionValid := by
    intro i
    fin_cases i
    · exact ⟨[], [], rfl, rfl⟩
    · exact ⟨[(0 : Fin 8)], [(1 : Fin 8)], rfl, rfl⟩
    · exact ⟨[], [(3 : Fin 8), (1 : Fin 8)], rfl, rfl⟩
    · exact ⟨[(5 : Fin 8)], [(1 : Fin 8)], rfl, rfl⟩
    · exact ⟨[], [(6 : Fin 8), (1 : Fin 8)], rfl, rfl⟩
    · exact ⟨[], [], rfl, rfl⟩
  strandContinuationsAreWellFormed := by
    intro i
    fin_cases i <;>
      simp [positiveZeroFramedHopfTrace, positiveHopfEvents,
        positiveHopfToCutOpenEvent, CutOpenEvent.StrandContinuationsAreWellFormed,
        positiveHopfStrands]
  eventPortsAreDistinct := by
    change ∀ i : Fin 6,
      ((positiveHopfToCutOpenEvent (positiveHopfEvents i)).beforeWord ++
        (positiveHopfToCutOpenEvent (positiveHopfEvents i)).afterWord).Nodup
    simpa only [positiveHopfToCutOpenEvent_beforeWord,
      positiveHopfToCutOpenEvent_afterWord] using
        positiveZeroFramedHopfTrace.eventPortsAreDistinct
  everyStrandHasUniqueInputAndOutput := by
    change ∀ strand : Fin 8,
      (∃! i : Fin 6,
          strand ∈ (positiveHopfToCutOpenEvent (positiveHopfEvents i)).beforeWord) ∧
        (∃! i : Fin 6,
          strand ∈ (positiveHopfToCutOpenEvent (positiveHopfEvents i)).afterWord)
    simpa only [positiveHopfToCutOpenEvent_beforeWord,
      positiveHopfToCutOpenEvent_afterWord] using
        positiveHopf_uniqueInputAndOutput
  activeWordsNoDuplicates := positiveZeroFramedHopfTrace.activeWordsNoDuplicates
  activeStrandsAreTwoHandles := by
    intro _ strand _
    exact positiveHopf_component_not_dotted
      (positiveZeroFramedHopfTrace.strands strand).component

private def positiveHopfDottedCutData :
    DottedCutData positiveZeroFramedHopfTrace where
  punctureWord := by
    intro dotted dottedRole
    exact False.elim (positiveHopf_component_not_dotted dotted dottedRole)
  exterior := positiveHopfCutOpenExterior

/-- The standard Hopf diagram has no dotted components, so cutting changes nothing. -/
def positiveZeroFramedHopfCut :
    DottedCutPresentation positiveZeroFramedHopfDiagram where
  cut := positiveHopfDottedCutData
  incidence_agrees_with_handle_boundary := by
    intro one
    exact Fin.elim0 one

private def positiveHopfCutEventIndex (i : Fin 6) :
    Fin positiveZeroFramedHopfCut.cut.exterior.eventCount :=
  ⟨i, by
    change i.val < 6
    exact i.isLt⟩

private def positiveHopfStrandIndex (i : Fin 8) :
    positiveZeroFramedHopfDiagram.trace.StrandId :=
  ⟨i, by
    change i.val < 8
    exact i.isLt⟩

/-- The 2-handle label read by each of the eight explicit Hopf strands. -/
private def positiveHopfStrandHandle : Fin 8 →
    Fin positiveZeroFramedHopfDiagram.handles.hTwo
  | 0 | 1 | 4 | 6 => positiveHopfFirstHandle
  | 2 | 3 | 5 | 7 => positiveHopfSecondHandle

private theorem positiveHopf_exteriorStrandLabel
    (𝒸 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒸 positiveZeroFramedHopfDiagram)
    (strand : positiveZeroFramedHopfDiagram.trace.StrandId) :
    exteriorStrandLabel 𝒸 positiveZeroFramedHopfDiagram labeling
        strand =
      labeling (positiveHopfStrandHandle strand) := by
  change Fin 8 at strand
  fin_cases strand <;>
    simp [positiveHopfStrandHandle,
      exteriorStrandLabel, positiveZeroFramedHopfDiagram,
      positiveZeroFramedHopfTrace,
      positiveHopfStrands, positiveHopfComponents,
      positiveHopfFirstHandle, positiveHopfSecondHandle]
  all_goals
    apply congrArg labeling
    rfl

private def positiveHopfStrandOrientation : Fin 8 → StrandOrientation
  | 0 | 2 | 4 | 5 | 6 => .positive
  | 1 | 3 | 7 => .negative

private theorem positiveHopf_strand_orientation
    (strand : positiveZeroFramedHopfDiagram.trace.StrandId) :
    (positiveZeroFramedHopfDiagram.trace.strands
      strand).orientation =
        positiveHopfStrandOrientation strand := by
  change Fin 8 at strand
  fin_cases strand <;>
    rfl

private theorem positiveHopf_orientedExteriorStrand
    (𝒸 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒸 positiveZeroFramedHopfDiagram)
    (strand : positiveZeroFramedHopfDiagram.trace.StrandId) :
    orientedExteriorStrand 𝒸 positiveZeroFramedHopfDiagram labeling
        strand =
      { label := labeling (positiveHopfStrandHandle strand)
        direction :=
          ribbonDirectionOfStrandOrientation
            (positiveHopfStrandOrientation strand) } := by
  unfold orientedExteriorStrand
  rw [positiveHopf_exteriorStrandLabel,
    positiveHopf_strand_orientation]

private theorem positiveHopf_eventContexts_eq
    (i : Fin positiveZeroFramedHopfCut.cut.exterior.eventCount)
    (left right : List positiveZeroFramedHopfDiagram.trace.StrandId)
    (beforeNonempty :
      (positiveZeroFramedHopfCut.cut.exterior.events i).beforeWord ≠ [])
    (decomposition :
      positiveZeroFramedHopfCut.cut.exterior.activeOrder i.castSucc =
        left ++
          (positiveZeroFramedHopfCut.cut.exterior.events i).beforeWord ++
          right) :
    eventLeftContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut i = left ∧
      eventRightContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut i = right := by
  exact
    list_context_unique_of_nodup
      (positiveZeroFramedHopfCut.cut.exterior.activeWordsNoDuplicates i.castSucc)
      beforeNonempty
      (eventTransitionEquations
        positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut i).1
      decomposition

private theorem positiveHopf_eventContexts_eq_after
    (i : Fin positiveZeroFramedHopfCut.cut.exterior.eventCount)
    (left right : List positiveZeroFramedHopfDiagram.trace.StrandId)
    (afterNonempty :
      (positiveZeroFramedHopfCut.cut.exterior.events i).afterWord ≠ [])
    (decomposition :
      positiveZeroFramedHopfCut.cut.exterior.activeOrder i.succ =
        left ++
          (positiveZeroFramedHopfCut.cut.exterior.events i).afterWord ++
          right) :
    eventLeftContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut i = left ∧
      eventRightContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut i = right := by
  exact
    list_context_unique_of_nodup
      (positiveZeroFramedHopfCut.cut.exterior.activeWordsNoDuplicates i.succ)
      afterNonempty
      (eventTransitionEquations
        positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut i).2
      decomposition

private theorem positiveHopf_eventZeroContexts :
    eventLeftContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 0) = [] ∧
      eventRightContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 0) = [] := by
  apply positiveHopf_eventContexts_eq_after
  · change [positiveHopfStrandIndex 0, positiveHopfStrandIndex 1] ≠ []
    simp
  · change [positiveHopfStrandIndex 0, positiveHopfStrandIndex 1] =
      [] ++ [positiveHopfStrandIndex 0, positiveHopfStrandIndex 1] ++ []
    rfl

private theorem positiveHopf_eventOneContexts :
    eventLeftContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 1) = [positiveHopfStrandIndex 0] ∧
      eventRightContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 1) = [positiveHopfStrandIndex 1] := by
  apply positiveHopf_eventContexts_eq_after
  · change [positiveHopfStrandIndex 2, positiveHopfStrandIndex 3] ≠ []
    simp
  · change [positiveHopfStrandIndex 0, positiveHopfStrandIndex 2,
        positiveHopfStrandIndex 3, positiveHopfStrandIndex 1] =
      [positiveHopfStrandIndex 0] ++
        [positiveHopfStrandIndex 2, positiveHopfStrandIndex 3] ++
        [positiveHopfStrandIndex 1]
    rfl

private theorem positiveHopf_eventTwoContexts :
    eventLeftContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 2) = [] ∧
      eventRightContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 2) =
          [positiveHopfStrandIndex 3, positiveHopfStrandIndex 1] := by
  apply positiveHopf_eventContexts_eq
  · change [positiveHopfStrandIndex 0, positiveHopfStrandIndex 2] ≠ []
    simp
  · change [positiveHopfStrandIndex 0, positiveHopfStrandIndex 2,
        positiveHopfStrandIndex 3, positiveHopfStrandIndex 1] =
      [] ++ [positiveHopfStrandIndex 0, positiveHopfStrandIndex 2] ++
        [positiveHopfStrandIndex 3, positiveHopfStrandIndex 1]
    rfl

private theorem positiveHopf_eventThreeContexts :
    eventLeftContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 3) = [positiveHopfStrandIndex 5] ∧
      eventRightContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 3) = [positiveHopfStrandIndex 1] := by
  apply positiveHopf_eventContexts_eq
  · change [positiveHopfStrandIndex 4, positiveHopfStrandIndex 3] ≠ []
    simp
  · change [positiveHopfStrandIndex 5, positiveHopfStrandIndex 4,
        positiveHopfStrandIndex 3, positiveHopfStrandIndex 1] =
      [positiveHopfStrandIndex 5] ++
        [positiveHopfStrandIndex 4, positiveHopfStrandIndex 3] ++
        [positiveHopfStrandIndex 1]
    rfl

private theorem positiveHopf_eventFourContexts :
    eventLeftContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 4) = [] ∧
      eventRightContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 4) =
          [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1] := by
  apply positiveHopf_eventContexts_eq
  · change [positiveHopfStrandIndex 5, positiveHopfStrandIndex 7] ≠ []
    simp
  · change [positiveHopfStrandIndex 5, positiveHopfStrandIndex 7,
        positiveHopfStrandIndex 6, positiveHopfStrandIndex 1] =
      [] ++ [positiveHopfStrandIndex 5, positiveHopfStrandIndex 7] ++
        [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1]
    rfl

private theorem positiveHopf_eventFiveContexts :
    eventLeftContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 5) = [] ∧
      eventRightContext positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut
        (positiveHopfCutEventIndex 5) = [] := by
  apply positiveHopf_eventContexts_eq
  · change [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1] ≠ []
    simp
  · change [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1] =
      [] ++ [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1] ++ []
    rfl

/-- The first explicit Hopf event compiles to the canonical paired birth. -/
private theorem positiveHopf_eventZeroContextualEdge
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling word))
          (show
            positiveZeroFramedHopfCut.cut.exterior.activeOrder
                (positiveHopfCutEventIndex 0).castSucc = [] by
              rfl)).symm ≫
      compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 0) ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling word))
          (show
            positiveZeroFramedHopfCut.cut.exterior.activeOrder
                (positiveHopfCutEventIndex 0).succ =
              [positiveHopfStrandIndex 0, positiveHopfStrandIndex 1] by
                rfl)) =
      pairedBirthMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
        (positiveHopfStrandIndex 0) (positiveHopfStrandIndex 1)
        (by rfl) (by decide) := by
  let i := positiveHopfCutEventIndex 0
  have eventEq :
      positiveZeroFramedHopfCut.cut.exterior.events i =
        .birth (positiveHopfStrandIndex 0) (positiveHopfStrandIndex 1) := by
    rfl
  have beforeEq :
      positiveZeroFramedHopfCut.cut.exterior.activeOrder i.castSucc = [] := by
    rfl
  have afterEq :
      positiveZeroFramedHopfCut.cut.exterior.activeOrder i.succ =
        [positiveHopfStrandIndex 0, positiveHopfStrandIndex 1] := by
    rfl
  have contexts := positiveHopf_eventZeroContexts
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  simpa [i] using
    (compileContextualFromWitness_eq_birth
      𝒞 positiveZeroFramedHopfDiagram labeling
      (positiveZeroFramedHopfCut.cut.exterior.events i)
      (positiveHopfStrandIndex 0) (positiveHopfStrandIndex 1)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.castSucc)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.succ)
      (eventLeftContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      (eventRightContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).1
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).2
      (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i)
      eventEq beforeEq afterEq contexts.1 contexts.2)

private theorem positiveHopf_eventZeroDirect
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 0) =
      pairedBirthMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
        (positiveHopfStrandIndex 0) (positiveHopfStrandIndex 1)
        (by rfl) (by decide) := by
  apply eq_of_heq
  apply middle_heq_of_transport_sandwich_eq
  exact positiveHopf_eventZeroContextualEdge 𝒞 labeling

/-- The first Hopf event is the canonical cup for the first component. -/
private theorem positiveHopf_eventZeroCanonical
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    HEq
      (compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 0))
      (canonicalPositiveNegativeBirth 𝒞
        (labeling positiveHopfFirstHandle)) := by
  refine (heq_of_eq (positiveHopf_eventZeroDirect 𝒞 labeling)).trans ?_
  have labelEq :
      exteriorStrandLabel 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex (1 : Fin 8)) =
        labeling positiveHopfFirstHandle := by
    rw [positiveHopf_exteriorStrandLabel]
    rfl
  have leftPositive :
      (positiveZeroFramedHopfDiagram.trace.strands
        (positiveHopfStrandIndex (0 : Fin 8))).orientation = .positive := by
    rfl
  unfold pairedBirthMorphism
  simp only [leftPositive, ↓reduceDIte]
  exact
    (CategoryTheory.comp_eqToHom_heq _ _).trans
      (canonicalPositiveNegativeBirth_heq 𝒞 labelEq)

/-- The second Hopf event inserts the second paired birth in its fixed exterior context. -/
private theorem positiveHopf_eventOneContextualEdge
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 1) =
      contextualizeExteriorMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
        [positiveHopfStrandIndex 0] []
        [positiveHopfStrandIndex 2, positiveHopfStrandIndex 3]
        [positiveHopfStrandIndex 1]
        (pairedBirthMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex 2) (positiveHopfStrandIndex 3)
          (by rfl) (by decide)) := by
  let i := positiveHopfCutEventIndex 1
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  have eventEq :
      positiveZeroFramedHopfCut.cut.exterior.events i =
        .birth (positiveHopfStrandIndex 2) (positiveHopfStrandIndex 3) := by
    rfl
  have contexts := positiveHopf_eventOneContexts
  have contextual :=
    compileContextualFromWitness_heq_in_context
      𝒞 positiveZeroFramedHopfDiagram labeling
      (positiveZeroFramedHopfCut.cut.exterior.events i)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.castSucc)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.succ)
      (eventLeftContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      (eventRightContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      [positiveHopfStrandIndex 0] [positiveHopfStrandIndex 1]
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).1
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).2
      (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i)
      contexts.1 contexts.2 (by rfl) (by rfl)
  have localEdge :=
    compileCutOpenEventMorphism_heq_birth
      𝒞 positiveZeroFramedHopfDiagram labeling
      (positiveZeroFramedHopfCut.cut.exterior.events i)
      (positiveHopfStrandIndex 2) (positiveHopfStrandIndex 3)
      (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i)
      eventEq
  have exterior :=
    contextualizeExteriorMorphism_heq
      𝒞 positiveZeroFramedHopfDiagram labeling
      (left := [positiveHopfStrandIndex 0])
      (before :=
        (positiveZeroFramedHopfCut.cut.exterior.events i).beforeWord)
      (after :=
        (positiveZeroFramedHopfCut.cut.exterior.events i).afterWord)
      (right := [positiveHopfStrandIndex 1])
      (left' := [positiveHopfStrandIndex 0])
      (before' := [])
      (after' := [positiveHopfStrandIndex 2, positiveHopfStrandIndex 3])
      (right' := [positiveHopfStrandIndex 1])
      (map := compileCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram labeling
        (positiveZeroFramedHopfCut.cut.exterior.events i)
        (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i))
      (map' := pairedBirthMorphism
        𝒞 positiveZeroFramedHopfDiagram labeling
        (positiveHopfStrandIndex 2) (positiveHopfStrandIndex 3)
        (eventEq ▸
          positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i).1
        (eventEq ▸
          positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i).2)
      rfl (congrArg CutOpenEvent.beforeWord eventEq)
      (congrArg CutOpenEvent.afterWord eventEq) rfl localEdge
  apply eq_of_heq
  simpa only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord] using
    contextual.trans exterior

/-- The second Hopf event, stripped of strand-indexed endpoint transports. -/
private theorem positiveHopf_eventOneDirect
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    HEq
      (compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 1))
      (contextualizeRibbonMorphism 𝒞
        [{ label := labeling positiveHopfFirstHandle, direction := .forward }]
        []
        [{ label := labeling positiveHopfSecondHandle, direction := .forward },
          { label := labeling positiveHopfSecondHandle, direction := .dual }]
        [{ label := labeling positiveHopfFirstHandle, direction := .dual }]
        (canonicalPositiveNegativeBirth 𝒞
          (labeling positiveHopfSecondHandle))) := by
  have core :=
    (heq_of_eq (positiveHopf_eventOneContextualEdge 𝒞 labeling)).trans
      (contextualizeExteriorMorphism_heq_core
        𝒞 positiveZeroFramedHopfDiagram labeling
        [positiveHopfStrandIndex 0] []
        [positiveHopfStrandIndex 2, positiveHopfStrandIndex 3]
        [positiveHopfStrandIndex 1]
        (pairedBirthMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex 2) (positiveHopfStrandIndex 3)
          (by rfl) (by decide)))
  have mapEq :
      HEq
        (pairedBirthMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex 2) (positiveHopfStrandIndex 3)
          (by rfl) (by decide))
        (canonicalPositiveNegativeBirth 𝒞
          (labeling positiveHopfSecondHandle)) := by
    unfold pairedBirthMorphism
    simp [positiveZeroFramedHopfDiagram, positiveZeroFramedHopfTrace,
      positiveHopfStrands, positiveHopfComponents,
      exteriorStrandLabel, positiveHopfSecondHandle,
      positiveHopfStrandIndex]
    congr 2
  have leftEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (0 : Fin 8)] =
        [{ label := labeling positiveHopfFirstHandle, direction := .forward }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  have afterEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (2 : Fin 8),
            positiveHopfStrandIndex (3 : Fin 8)] =
        [{ label := labeling positiveHopfSecondHandle, direction := .forward },
          { label := labeling positiveHopfSecondHandle, direction := .dual }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  have rightEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (1 : Fin 8)] =
        [{ label := labeling positiveHopfFirstHandle, direction := .dual }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  exact core.trans
    (contextualizeRibbonMorphism_heq 𝒞
      leftEq
      rfl
      afterEq
      rightEq
      mapEq)

/-- The fifth Hopf event removes the second paired strands in its fixed exterior context. -/
private theorem positiveHopf_eventFourContextualEdge
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 4) =
      contextualizeExteriorMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
        [] [positiveHopfStrandIndex 5, positiveHopfStrandIndex 7] []
        [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1]
        (pairedDeathMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex 5) (positiveHopfStrandIndex 7)
          (by rfl) (by decide)) := by
  let i := positiveHopfCutEventIndex 4
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  have eventEq :
      positiveZeroFramedHopfCut.cut.exterior.events i =
        .death (positiveHopfStrandIndex 5) (positiveHopfStrandIndex 7) := by
    rfl
  have contexts := positiveHopf_eventFourContexts
  have contextual :=
    compileContextualFromWitness_heq_in_context
      𝒞 positiveZeroFramedHopfDiagram labeling
      (positiveZeroFramedHopfCut.cut.exterior.events i)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.castSucc)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.succ)
      (eventLeftContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      (eventRightContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      [] [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1]
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).1
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).2
      (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i)
      contexts.1 contexts.2 (by rfl) (by rfl)
  have localEdge :=
    compileCutOpenEventMorphism_heq_death
      𝒞 positiveZeroFramedHopfDiagram labeling
      (positiveZeroFramedHopfCut.cut.exterior.events i)
      (positiveHopfStrandIndex 5) (positiveHopfStrandIndex 7)
      (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i)
      eventEq
  have exterior :=
    contextualizeExteriorMorphism_heq
      𝒞 positiveZeroFramedHopfDiagram labeling
      (left := [])
      (before :=
        (positiveZeroFramedHopfCut.cut.exterior.events i).beforeWord)
      (after :=
        (positiveZeroFramedHopfCut.cut.exterior.events i).afterWord)
      (right := [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1])
      (left' := [])
      (before' := [positiveHopfStrandIndex 5, positiveHopfStrandIndex 7])
      (after' := [])
      (right' := [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1])
      (map := compileCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram labeling
        (positiveZeroFramedHopfCut.cut.exterior.events i)
        (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i))
      (map' := pairedDeathMorphism
        𝒞 positiveZeroFramedHopfDiagram labeling
        (positiveHopfStrandIndex 5) (positiveHopfStrandIndex 7)
        (eventEq ▸
          positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i).1
        (eventEq ▸
          positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i).2)
      rfl (congrArg CutOpenEvent.beforeWord eventEq)
      (congrArg CutOpenEvent.afterWord eventEq) rfl localEdge
  apply eq_of_heq
  simpa only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord] using
    contextual.trans exterior

/-- The fifth Hopf event, with all exterior strand indices replaced by their labels. -/
private theorem positiveHopf_eventFourDirect
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    HEq
      (compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 4))
      (contextualizeRibbonMorphism 𝒞
        []
        [{ label := labeling positiveHopfSecondHandle, direction := .forward },
          { label := labeling positiveHopfSecondHandle, direction := .dual }]
        []
        [{ label := labeling positiveHopfFirstHandle, direction := .forward },
          { label := labeling positiveHopfFirstHandle, direction := .dual }]
        (canonicalPositiveNegativeDeath 𝒞
          (labeling positiveHopfSecondHandle))) := by
  have core :=
    (heq_of_eq (positiveHopf_eventFourContextualEdge 𝒞 labeling)).trans
      (contextualizeExteriorMorphism_heq_core
        𝒞 positiveZeroFramedHopfDiagram labeling
        [] [positiveHopfStrandIndex 5, positiveHopfStrandIndex 7] []
        [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1]
        (pairedDeathMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex 5) (positiveHopfStrandIndex 7)
          (by rfl) (by decide)))
  have mapEq :
      HEq
        (pairedDeathMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex 5) (positiveHopfStrandIndex 7)
          (by rfl) (by decide))
        (canonicalPositiveNegativeDeath 𝒞
          (labeling positiveHopfSecondHandle)) := by
    unfold pairedDeathMorphism
    simp [positiveZeroFramedHopfDiagram, positiveZeroFramedHopfTrace,
      positiveHopfStrands, positiveHopfComponents,
      exteriorStrandLabel, positiveHopfSecondHandle,
      positiveHopfStrandIndex]
    congr 2
  have beforeEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (5 : Fin 8),
            positiveHopfStrandIndex (7 : Fin 8)] =
        [{ label := labeling positiveHopfSecondHandle, direction := .forward },
          { label := labeling positiveHopfSecondHandle, direction := .dual }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  have rightEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (6 : Fin 8),
            positiveHopfStrandIndex (1 : Fin 8)] =
        [{ label := labeling positiveHopfFirstHandle, direction := .forward },
          { label := labeling positiveHopfFirstHandle, direction := .dual }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  exact core.trans
    (contextualizeRibbonMorphism_heq 𝒞 rfl beforeEq rfl rightEq mapEq)

/-- The last explicit Hopf event compiles to the canonical paired death. -/
private theorem positiveHopf_eventFiveContextualEdge
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling word))
          (show
            positiveZeroFramedHopfCut.cut.exterior.activeOrder
                (positiveHopfCutEventIndex 5).castSucc =
              [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1] by
                rfl)).symm ≫
      compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 5) ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling word))
          (show
            positiveZeroFramedHopfCut.cut.exterior.activeOrder
                (positiveHopfCutEventIndex 5).succ = [] by
              rfl)) =
      pairedDeathMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
        (positiveHopfStrandIndex 6) (positiveHopfStrandIndex 1)
        (by rfl) (by decide) := by
  let i := positiveHopfCutEventIndex 5
  have eventEq :
      positiveZeroFramedHopfCut.cut.exterior.events i =
        .death (positiveHopfStrandIndex 6) (positiveHopfStrandIndex 1) := by
    rfl
  have beforeEq :
      positiveZeroFramedHopfCut.cut.exterior.activeOrder i.castSucc =
        [positiveHopfStrandIndex 6, positiveHopfStrandIndex 1] := by
    rfl
  have afterEq :
      positiveZeroFramedHopfCut.cut.exterior.activeOrder i.succ = [] := by
    rfl
  have contexts := positiveHopf_eventFiveContexts
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  simpa [i] using
    (compileContextualFromWitness_eq_death
      𝒞 positiveZeroFramedHopfDiagram labeling
      (positiveZeroFramedHopfCut.cut.exterior.events i)
      (positiveHopfStrandIndex 6) (positiveHopfStrandIndex 1)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.castSucc)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.succ)
      (eventLeftContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      (eventRightContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).1
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).2
      (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i)
      eventEq beforeEq afterEq contexts.1 contexts.2)

private theorem positiveHopf_eventFiveDirect
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 5) =
      pairedDeathMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
        (positiveHopfStrandIndex 6) (positiveHopfStrandIndex 1)
        (by rfl) (by decide) := by
  apply eq_of_heq
  apply middle_heq_of_transport_sandwich_eq
  exact positiveHopf_eventFiveContextualEdge 𝒞 labeling

/-- The last Hopf event is the canonical cap for the first component. -/
private theorem positiveHopf_eventFiveCanonical
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    HEq
      (compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 5))
      (canonicalPositiveNegativeDeath 𝒞
        (labeling positiveHopfFirstHandle)) := by
  refine (heq_of_eq (positiveHopf_eventFiveDirect 𝒞 labeling)).trans ?_
  have labelEq :
      exteriorStrandLabel 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex (1 : Fin 8)) =
        labeling positiveHopfFirstHandle := by
    rw [positiveHopf_exteriorStrandLabel]
    rfl
  have leftPositive :
      (positiveZeroFramedHopfDiagram.trace.strands
        (positiveHopfStrandIndex (6 : Fin 8))).orientation = .positive := by
    rfl
  unfold pairedDeathMorphism
  simp only [leftPositive, ↓reduceDIte]
  exact
    (CategoryTheory.eqToHom_comp_heq _ _).trans
      (canonicalPositiveNegativeDeath_heq 𝒞 labelEq)

/-!
The only topology input in this file.  It identifies one explicit finite
Kirby diagram with the familiar manifold `S^2 x S^2`; it contains no category,
character, graphical evaluation, or scalar equality.
-/
axiom positiveZeroFramedHopf_realizes_sphereTwoProduct :
  OrientedDiffeomorphism
    (realizeSpecialKirbyDiagram positiveZeroFramedHopfDiagram)
    sphereTwoProduct

/-- The canonical zero-marked representative supplied by the standard Hopf diagram. -/
noncomputable def positiveZeroFramedHopfRepresentative :
    SpecialKirbyRepresentativeOf sphereTwoProduct where
  diagram := positiveZeroFramedHopfDiagram
  cut := positiveZeroFramedHopfCut
  realizationDiffeomorphism :=
    positiveZeroFramedHopf_realizes_sphereTwoProduct
  diagramHomologyComparison :=
    specialKirbyDiagram_computesH₂ positiveZeroFramedHopfDiagram
  alpha := 0

theorem positiveZeroFramedHopfRepresentative_represents_zero :
    positiveZeroFramedHopfRepresentative.representsHomologyClass 0 := by
  unfold SpecialKirbyRepresentativeOf.representsHomologyClass
  exact map_zero _

/-- The manifold-level invariant may be evaluated on the explicit Hopf representative. -/
theorem twistedYetter_sphereTwoProduct_zero_eq_hopfRepresentative
    (𝒞η : TwistedPremodularCategory K) :
    TwistedYetter 𝒞η ⟨sphereTwoProduct, 0⟩ =
      evaluateMarkedDiagram 𝒞η
        positiveZeroFramedHopfRepresentative.toHomologicallyMarkedDiagram := by
  unfold TwistedYetter
  let chosenExistence :=
    specialKirbyRepresentative_exists sphereTwoProduct 0
  have targetCorrect :
      positiveZeroFramedHopfRepresentative.representsHomologyClass
        (inducedH₂ (identityOrientedDiffeomorphism sphereTwoProduct) 0) := by
    rw [map_zero]
    exact positiveZeroFramedHopfRepresentative_represents_zero
  exact
    ConditionalDescent.diffeomorphism_invariant_of_descent_data
      𝒞η
      (fun marked =>
        frozenFrontendRepresentativeIndependence
          𝒞η marked.diagram marked.cut marked.primalBoundary)
      (frozenFrontendLocalMoveInvariance 𝒞η)
      sphereTwoProduct sphereTwoProduct
      (identityOrientedDiffeomorphism sphereTwoProduct) 0
      chosenExistence.choose chosenExistence.choose_spec
      positiveZeroFramedHopfRepresentative targetCorrect

/-- The first crossing event is positive braiding in its unchanged right context. -/
private theorem positiveHopf_eventTwoContextualEdge
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 2) =
      contextualizeExteriorMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
        [] [positiveHopfStrandIndex 0, positiveHopfStrandIndex 2]
        [positiveHopfStrandIndex 5, positiveHopfStrandIndex 4]
        [positiveHopfStrandIndex 3, positiveHopfStrandIndex 1]
        (positiveCrossingWordMorphism 𝒞
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 0))
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 2))) := by
  let i := positiveHopfCutEventIndex 2
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  have eventEq :
      positiveZeroFramedHopfCut.cut.exterior.events i =
        .crossing
          (positiveHopfStrandIndex 0) (positiveHopfStrandIndex 2)
          (positiveHopfStrandIndex 4) (positiveHopfStrandIndex 5)
          .positive := by
    rfl
  have contexts := positiveHopf_eventTwoContexts
  have contextual :=
    compileContextualFromWitness_heq_in_context
      𝒞 positiveZeroFramedHopfDiagram labeling
      (positiveZeroFramedHopfCut.cut.exterior.events i)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.castSucc)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.succ)
      (eventLeftContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      (eventRightContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      [] [positiveHopfStrandIndex 3, positiveHopfStrandIndex 1]
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).1
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).2
      (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i)
      contexts.1 contexts.2 (by rfl) (by rfl)
  have localEdge :=
    compileCutOpenEventMorphism_heq_positiveCrossing
      𝒞 positiveZeroFramedHopfDiagram labeling
      (positiveZeroFramedHopfCut.cut.exterior.events i)
      (positiveHopfStrandIndex 0) (positiveHopfStrandIndex 2)
      (positiveHopfStrandIndex 4) (positiveHopfStrandIndex 5)
      (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i)
      eventEq
  have exterior :=
    contextualizeExteriorMorphism_heq
      𝒞 positiveZeroFramedHopfDiagram labeling
      (left := [])
      (before :=
        (positiveZeroFramedHopfCut.cut.exterior.events i).beforeWord)
      (after :=
        (positiveZeroFramedHopfCut.cut.exterior.events i).afterWord)
      (right := [positiveHopfStrandIndex 3, positiveHopfStrandIndex 1])
      (left' := [])
      (before' := [positiveHopfStrandIndex 0, positiveHopfStrandIndex 2])
      (after' := [positiveHopfStrandIndex 5, positiveHopfStrandIndex 4])
      (right' := [positiveHopfStrandIndex 3, positiveHopfStrandIndex 1])
      (map := compileCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram labeling
        (positiveZeroFramedHopfCut.cut.exterior.events i)
        (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i))
      (map' := positiveCrossingMorphism 𝒞
        (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex 0))
        (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex 2)))
      rfl (congrArg CutOpenEvent.beforeWord eventEq)
      (congrArg CutOpenEvent.afterWord eventEq) rfl localEdge
  apply eq_of_heq
  simpa only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord,
    positiveCrossingWordMorphism] using contextual.trans exterior

/-- The first crossing event, with all strand indices replaced by oriented labels. -/
private theorem positiveHopf_eventTwoDirect
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    HEq
      (compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 2))
      (contextualizeRibbonMorphism 𝒞
        []
        [{ label := labeling positiveHopfFirstHandle, direction := .forward },
          { label := labeling positiveHopfSecondHandle, direction := .forward }]
        [{ label := labeling positiveHopfSecondHandle, direction := .forward },
          { label := labeling positiveHopfFirstHandle, direction := .forward }]
        [{ label := labeling positiveHopfSecondHandle, direction := .dual },
          { label := labeling positiveHopfFirstHandle, direction := .dual }]
        (positiveCrossingWordMorphism 𝒞
          { label := labeling positiveHopfFirstHandle, direction := .forward }
          { label := labeling positiveHopfSecondHandle, direction := .forward })) := by
  have core :=
    (heq_of_eq (positiveHopf_eventTwoContextualEdge 𝒞 labeling)).trans
      (contextualizeExteriorMorphism_heq_core
        𝒞 positiveZeroFramedHopfDiagram labeling
        [] [positiveHopfStrandIndex 0, positiveHopfStrandIndex 2]
        [positiveHopfStrandIndex 5, positiveHopfStrandIndex 4]
        [positiveHopfStrandIndex 3, positiveHopfStrandIndex 1]
        (positiveCrossingWordMorphism 𝒞
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 0))
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 2))))
  have firstEq :
      orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex (0 : Fin 8)) =
        { label := labeling positiveHopfFirstHandle, direction := .forward } := by
    simpa [positiveHopfStrandHandle, positiveHopfStrandOrientation,
      ribbonDirectionOfStrandOrientation] using
      positiveHopf_orientedExteriorStrand 𝒞 labeling
        (positiveHopfStrandIndex (0 : Fin 8))
  have secondEq :
      orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex (2 : Fin 8)) =
        { label := labeling positiveHopfSecondHandle, direction := .forward } := by
    simpa [positiveHopfStrandHandle, positiveHopfStrandOrientation,
      ribbonDirectionOfStrandOrientation] using
      positiveHopf_orientedExteriorStrand 𝒞 labeling
        (positiveHopfStrandIndex (2 : Fin 8))
  have mapEq :
      HEq
        (positiveCrossingWordMorphism 𝒞
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 0))
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 2)))
        (positiveCrossingWordMorphism 𝒞
          { label := labeling positiveHopfFirstHandle, direction := .forward }
          { label := labeling positiveHopfSecondHandle, direction := .forward }) := by
    rw [firstEq, secondEq]
  have beforeEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (0 : Fin 8), positiveHopfStrandIndex (2 : Fin 8)] =
        [{ label := labeling positiveHopfFirstHandle, direction := .forward },
          { label := labeling positiveHopfSecondHandle, direction := .forward }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  have afterEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (5 : Fin 8), positiveHopfStrandIndex (4 : Fin 8)] =
        [{ label := labeling positiveHopfSecondHandle, direction := .forward },
          { label := labeling positiveHopfFirstHandle, direction := .forward }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  have rightEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (3 : Fin 8), positiveHopfStrandIndex (1 : Fin 8)] =
        [{ label := labeling positiveHopfSecondHandle, direction := .dual },
          { label := labeling positiveHopfFirstHandle, direction := .dual }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  exact core.trans
    (contextualizeRibbonMorphism_heq 𝒞 rfl beforeEq afterEq rightEq mapEq)

/-- The second crossing event is positive braiding in its fixed exterior context. -/
private theorem positiveHopf_eventThreeContextualEdge
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 3) =
      contextualizeExteriorMorphism 𝒞 positiveZeroFramedHopfDiagram labeling
        [positiveHopfStrandIndex 5]
        [positiveHopfStrandIndex 4, positiveHopfStrandIndex 3]
        [positiveHopfStrandIndex 7, positiveHopfStrandIndex 6]
        [positiveHopfStrandIndex 1]
        (positiveCrossingWordMorphism 𝒞
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 4))
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 3))) := by
  let i := positiveHopfCutEventIndex 3
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  have eventEq :
      positiveZeroFramedHopfCut.cut.exterior.events i =
        .crossing
          (positiveHopfStrandIndex 4) (positiveHopfStrandIndex 3)
          (positiveHopfStrandIndex 6) (positiveHopfStrandIndex 7)
          .positive := by
    rfl
  have contexts := positiveHopf_eventThreeContexts
  have contextual :=
    compileContextualFromWitness_heq_in_context
      𝒞 positiveZeroFramedHopfDiagram labeling
      (positiveZeroFramedHopfCut.cut.exterior.events i)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.castSucc)
      (positiveZeroFramedHopfCut.cut.exterior.activeOrder i.succ)
      (eventLeftContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      (eventRightContext positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i)
      [positiveHopfStrandIndex 5] [positiveHopfStrandIndex 1]
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).1
      (eventTransitionEquations positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut i).2
      (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i)
      contexts.1 contexts.2 (by rfl) (by rfl)
  have localEdge :=
    compileCutOpenEventMorphism_heq_positiveCrossing
      𝒞 positiveZeroFramedHopfDiagram labeling
      (positiveZeroFramedHopfCut.cut.exterior.events i)
      (positiveHopfStrandIndex 4) (positiveHopfStrandIndex 3)
      (positiveHopfStrandIndex 6) (positiveHopfStrandIndex 7)
      (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i)
      eventEq
  have exterior :=
    contextualizeExteriorMorphism_heq
      𝒞 positiveZeroFramedHopfDiagram labeling
      (left := [positiveHopfStrandIndex 5])
      (before :=
        (positiveZeroFramedHopfCut.cut.exterior.events i).beforeWord)
      (after :=
        (positiveZeroFramedHopfCut.cut.exterior.events i).afterWord)
      (right := [positiveHopfStrandIndex 1])
      (left' := [positiveHopfStrandIndex 5])
      (before' := [positiveHopfStrandIndex 4, positiveHopfStrandIndex 3])
      (after' := [positiveHopfStrandIndex 7, positiveHopfStrandIndex 6])
      (right' := [positiveHopfStrandIndex 1])
      (map := compileCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram labeling
        (positiveZeroFramedHopfCut.cut.exterior.events i)
        (positiveZeroFramedHopfCut.cut.exterior.strandContinuationsAreWellFormed i))
      (map' := positiveCrossingMorphism 𝒞
        (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex 4))
        (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
          (positiveHopfStrandIndex 3)))
      rfl (congrArg CutOpenEvent.beforeWord eventEq)
      (congrArg CutOpenEvent.afterWord eventEq) rfl localEdge
  apply eq_of_heq
  simpa only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord,
    positiveCrossingWordMorphism] using contextual.trans exterior

/-- The second crossing event, with all strand indices replaced by oriented labels. -/
private theorem positiveHopf_eventThreeDirect
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    HEq
      (compileContextualCutOpenEventMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 3))
      (contextualizeRibbonMorphism 𝒞
        [{ label := labeling positiveHopfSecondHandle, direction := .forward }]
        [{ label := labeling positiveHopfFirstHandle, direction := .forward },
          { label := labeling positiveHopfSecondHandle, direction := .dual }]
        [{ label := labeling positiveHopfSecondHandle, direction := .dual },
          { label := labeling positiveHopfFirstHandle, direction := .forward }]
        [{ label := labeling positiveHopfFirstHandle, direction := .dual }]
        (positiveCrossingWordMorphism 𝒞
          { label := labeling positiveHopfFirstHandle, direction := .forward }
          { label := labeling positiveHopfSecondHandle, direction := .dual })) := by
  have core :=
    (heq_of_eq (positiveHopf_eventThreeContextualEdge 𝒞 labeling)).trans
      (contextualizeExteriorMorphism_heq_core
        𝒞 positiveZeroFramedHopfDiagram labeling
        [positiveHopfStrandIndex 5]
        [positiveHopfStrandIndex 4, positiveHopfStrandIndex 3]
        [positiveHopfStrandIndex 7, positiveHopfStrandIndex 6]
        [positiveHopfStrandIndex 1]
        (positiveCrossingWordMorphism 𝒞
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 4))
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 3))))
  have leftEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (5 : Fin 8)] =
        [{ label := labeling positiveHopfSecondHandle, direction := .forward }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  have beforeEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (4 : Fin 8), positiveHopfStrandIndex (3 : Fin 8)] =
        [{ label := labeling positiveHopfFirstHandle, direction := .forward },
          { label := labeling positiveHopfSecondHandle, direction := .dual }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  have afterEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (7 : Fin 8), positiveHopfStrandIndex (6 : Fin 8)] =
        [{ label := labeling positiveHopfSecondHandle, direction := .dual },
          { label := labeling positiveHopfFirstHandle, direction := .forward }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  have rightEq :
      exteriorWord 𝒞 positiveZeroFramedHopfDiagram labeling
          [positiveHopfStrandIndex (1 : Fin 8)] =
        [{ label := labeling positiveHopfFirstHandle, direction := .dual }] := by
    simp only [exteriorWord, List.map_cons, List.map_nil,
      positiveHopf_orientedExteriorStrand]
    rfl
  have mapEq :
      HEq
        (positiveCrossingWordMorphism 𝒞
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 4))
          (orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex 3)))
        (positiveCrossingWordMorphism 𝒞
          { label := labeling positiveHopfFirstHandle, direction := .forward }
          { label := labeling positiveHopfSecondHandle, direction := .dual }) := by
    have firstEq :
        orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex (4 : Fin 8)) =
          { label := labeling positiveHopfFirstHandle, direction := .forward } := by
      simpa [positiveHopfStrandHandle, positiveHopfStrandOrientation,
        ribbonDirectionOfStrandOrientation] using
        positiveHopf_orientedExteriorStrand 𝒞 labeling
          (positiveHopfStrandIndex (4 : Fin 8))
    have secondEq :
        orientedExteriorStrand 𝒞 positiveZeroFramedHopfDiagram labeling
            (positiveHopfStrandIndex (3 : Fin 8)) =
          { label := labeling positiveHopfSecondHandle, direction := .dual } := by
      simpa [positiveHopfStrandHandle, positiveHopfStrandOrientation,
        ribbonDirectionOfStrandOrientation] using
        positiveHopf_orientedExteriorStrand 𝒞 labeling
          (positiveHopfStrandIndex (3 : Fin 8))
    rw [firstEq, secondEq]
  exact core.trans
    (contextualizeRibbonMorphism_heq 𝒞 leftEq beforeEq afterEq rightEq mapEq)

@[simp]
private theorem positiveHopf_label_twoHandleIndex_symm
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram)
    (component : positiveZeroFramedHopfTrace.ComponentId)
    (notDotted :
      (positiveZeroFramedHopfTrace.components component).role ≠ .dotted) :
    labeling (positiveHopfHandleData.twoHandleIndex.symm
        ⟨component, notDotted⟩) = labeling component :=
  congrArg labeling (positiveHopf_twoHandleIndex_symm component notDotted)

/-- The explicit six-event compiler is exactly the componentwise Hopf morphism. -/
private theorem positiveHopf_compile_eq_componentwise
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    compileCutOpenExteriorMorphism
        𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling =
      standardPositiveHopfClosure 𝒞
        (labeling positiveHopfFirstHandle)
        (labeling positiveHopfSecondHandle) := by
  rw [compileCutOpenExteriorMorphism_eq_compiledTrace]
  simp only [FiniteMorphismTrace.composeAll]
  change
    eqToHom _ ≫
        (compiledExteriorTrace 𝒞 positiveZeroFramedHopfDiagram
          positiveZeroFramedHopfCut labeling).composePrefix 6 _ ≫
      eqToHom _ = _
  simp only [FiniteMorphismTrace.composePrefix, compiledExteriorTrace,
    compileRoleAwareContextualCutOpenEventMorphism_eq_elementary]
  change
    eqToHom _ ≫
        ((((((𝟙 _ ≫
              compileContextualCutOpenEventMorphism 𝒞
                positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
                (positiveHopfCutEventIndex 0)) ≫
            compileContextualCutOpenEventMorphism 𝒞
              positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
              (positiveHopfCutEventIndex 1)) ≫
          compileContextualCutOpenEventMorphism 𝒞
            positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
            (positiveHopfCutEventIndex 2)) ≫
        compileContextualCutOpenEventMorphism 𝒞
          positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 3)) ≫
      compileContextualCutOpenEventMorphism 𝒞
        positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
        (positiveHopfCutEventIndex 4)) ≫
    compileContextualCutOpenEventMorphism 𝒞
      positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
      (positiveHopfCutEventIndex 5)) ≫
      eqToHom _ = _
  have eventZero := positiveHopf_eventZeroCanonical 𝒞 labeling
  have eventOne := positiveHopf_eventOneDirect 𝒞 labeling
  have eventTwo := positiveHopf_eventTwoDirect 𝒞 labeling
  have eventThree := positiveHopf_eventThreeDirect 𝒞 labeling
  have eventFour := positiveHopf_eventFourDirect 𝒞 labeling
  have eventFive := positiveHopf_eventFiveCanonical 𝒞 labeling
  have eventZeroFromIdentity :
      HEq
        (𝟙 _ ≫
          compileContextualCutOpenEventMorphism
            𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
              (positiveHopfCutEventIndex 0))
        (canonicalPositiveNegativeBirth 𝒞
          (labeling positiveHopfFirstHandle)) :=
    (heq_of_eq (Category.id_comp _)).trans eventZero
  have firstTwo :=
    CategoryTheory.heq_comp rfl rfl rfl eventZeroFromIdentity eventOne
  have firstThree :=
    CategoryTheory.heq_comp rfl rfl rfl firstTwo eventTwo
  have firstFour :=
    CategoryTheory.heq_comp rfl rfl rfl firstThree eventThree
  have firstFive :=
    CategoryTheory.heq_comp rfl rfl rfl firstFour eventFour
  have allSix :=
    CategoryTheory.heq_comp rfl rfl rfl firstFive eventFive
  have allSixComponentwise :
      HEq
        ((((((𝟙 _ ≫
              compileContextualCutOpenEventMorphism 𝒞
                positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
                (positiveHopfCutEventIndex 0)) ≫
            compileContextualCutOpenEventMorphism 𝒞
              positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
              (positiveHopfCutEventIndex 1)) ≫
          compileContextualCutOpenEventMorphism 𝒞
            positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
            (positiveHopfCutEventIndex 2)) ≫
        compileContextualCutOpenEventMorphism 𝒞
          positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
          (positiveHopfCutEventIndex 3)) ≫
      compileContextualCutOpenEventMorphism 𝒞
        positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
        (positiveHopfCutEventIndex 4)) ≫
    compileContextualCutOpenEventMorphism 𝒞
      positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling
      (positiveHopfCutEventIndex 5))
        (standardPositiveHopfClosure 𝒞
          (labeling positiveHopfFirstHandle)
          (labeling positiveHopfSecondHandle)) := by
    simpa only [standardPositiveHopfClosure, Category.assoc] using allSix
  exact eq_of_heq
    ((transport_sandwich_heq _ _ _).trans allSixComponentwise)

/-- Componentwise closure of two positive crossings is the ribbon trace of monodromy. -/
private theorem componentwisePositiveHopfMorphism_eq_trace
    (𝒞 : BundledPremodularCategory K)
    (first second : 𝒞.simples.Simple) :
    standardPositiveHopfClosure 𝒞 first second =
      𝒞.canonicalRibbonTrace
        (monodromyHom (𝒞.simpleObject first) (𝒞.simpleObject second)) := by
  exact standardPositiveHopfClosure_eq_monodromyTrace 𝒞 first second

/-- The explicit six-event compiler evaluates as the positive Hopf trace. -/
theorem positiveHopf_compile_closedScalar
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 positiveZeroFramedHopfDiagram) :
    𝒞.closedScalar
        (compileCutOpenExteriorMorphism
          𝒞 positiveZeroFramedHopfDiagram positiveZeroFramedHopfCut labeling) =
      positiveHopfLinkScalar 𝒞
        (labeling positiveHopfFirstHandle)
        (labeling positiveHopfSecondHandle) := by
  unfold positiveHopfLinkScalar
  apply congrArg 𝒞.closedScalar
  rw [positiveHopf_compile_eq_componentwise,
    componentwisePositiveHopfMorphism_eq_trace]

/-- Evaluate the zero marking using the literal zero THAM cycle. -/
theorem positiveHopf_evaluateMarking_eq_zeroCycle
    (𝒞η : TwistedPremodularCategory K) :
    evaluateMarkedDiagram 𝒞η
        positiveZeroFramedHopfRepresentative.toHomologicallyMarkedDiagram =
      evaluateCycle 𝒞η positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut
        positiveZeroFramedHopfDiagram.primalDegreeThreeBoundaryData 0 := by
  apply frozenFrontendRepresentativeIndependence
  change
    thamCycleClass positiveZeroFramedHopfDiagram.primalDegreeThreeBoundaryData
        (Quotient.out positiveZeroFramedHopfRepresentative.thamAlpha) =
      thamCycleClass positiveZeroFramedHopfDiagram.primalDegreeThreeBoundaryData 0
  rw [show
    thamCycleClass positiveZeroFramedHopfDiagram.primalDegreeThreeBoundaryData
        (Quotient.out positiveZeroFramedHopfRepresentative.thamAlpha) =
      positiveZeroFramedHopfRepresentative.thamAlpha by
    exact Quotient.out_eq positiveZeroFramedHopfRepresentative.thamAlpha]
  rw [show positiveZeroFramedHopfRepresentative.thamAlpha = 0 by
    change
      (turnoverPoincareDualityEquiv positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfRepresentative.primalBoundary
        (specialKirbyDiagram_computesH₂ positiveZeroFramedHopfDiagram)) 0 = 0
    exact
      (turnoverPoincareDualityEquiv positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfRepresentative.primalBoundary
        (specialKirbyDiagram_computesH₂ positiveZeroFramedHopfDiagram)).map_zero]
  rfl

/-- One zero-marking Hopf summand is the product of its two Kirby weights and
the corresponding positive Hopf-link scalar. -/
theorem positiveHopf_rawEvaluatorSummand_zero
    (𝒞η : TwistedPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞η.category positiveZeroFramedHopfDiagram) :
    rawEvaluatorSummand 𝒞η positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut
        positiveZeroFramedHopfDiagram.primalDegreeThreeBoundaryData 0 labeling =
      𝒞η.category.quantumDimension (labeling positiveHopfFirstHandle) *
        𝒞η.category.quantumDimension (labeling positiveHopfSecondHandle) *
          positiveHopfLinkScalar 𝒞η.category
            (labeling positiveHopfFirstHandle)
            (labeling positiveHopfSecondHandle) := by
  unfold rawEvaluatorSummand
  simp only [canonicalRoleAwareGraphCompiler,
    canonicalRibbonGraphicalEvaluation, RibbonExpression.interpret]
  have kirbyWeight_eq :
      ordinaryKirbyWeight 𝒞η.category labeling =
        𝒞η.category.quantumDimension (labeling positiveHopfFirstHandle) *
          𝒞η.category.quantumDimension
            (labeling positiveHopfSecondHandle) := by
    unfold ordinaryKirbyWeight
    rw [Fintype.prod_equiv positiveHopfTwoHandleEquiv
      (fun handle =>
        𝒞η.category.simples.quantumDimension (labeling handle))
      (fun handle =>
        𝒞η.category.simples.quantumDimension
          (labeling (positiveHopfTwoHandleEquiv.symm handle))) (by simp)]
    rw [Fin.prod_univ_two]
    rw [𝒞η.category.simples_quantumDimension_eq,
      𝒞η.category.simples_quantumDimension_eq]
    rw [positiveHopfTwoHandleEquiv_symm_zero,
      positiveHopfTwoHandleEquiv_symm_one]
  have characterWeight_eq :
      characterWeight
          (primal :=
            positiveZeroFramedHopfDiagram.primalDegreeThreeBoundaryData)
          𝒞η labeling
          (0 : ThamTwoCycles
            positiveZeroFramedHopfDiagram.primalDegreeThreeBoundaryData) = 1 := by
    simp [characterWeight]
  rw [kirbyWeight_eq, characterWeight_eq, mul_one]
  rw [positiveHopf_compile_closedScalar]

/-- The raw zero-marking value is the full two-label positive Hopf sum. -/
theorem positiveHopf_rawCycleSum_zero
    (𝒞η : TwistedPremodularCategory K) :
    rawCycleSum 𝒞η positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut
        positiveZeroFramedHopfDiagram.primalDegreeThreeBoundaryData 0 =
      ∑ i : 𝒞η.category.Simple,
        ∑ j : 𝒞η.category.Simple,
          𝒞η.category.quantumDimension i *
            𝒞η.category.quantumDimension j *
              positiveHopfLinkScalar 𝒞η.category i j := by
  classical
  rw [rawCycleSum_eq_sum_rawEvaluatorSummand]
  calc
    _ = ∑ labels : 𝒞η.category.Simple × 𝒞η.category.Simple,
        𝒞η.category.quantumDimension labels.1 *
          𝒞η.category.quantumDimension labels.2 *
            positiveHopfLinkScalar 𝒞η.category labels.1 labels.2 := by
      apply Fintype.sum_equiv
        (finTwoArrowEquiv 𝒞η.category.Simple)
      intro labeling
      exact positiveHopf_rawEvaluatorSummand_zero 𝒞η labeling
    _ = _ := by rw [Fintype.sum_prod_type]

/-- The global dimension of the transparent simple sector. -/
noncomputable def transparentGlobalDimension
    (𝒞 : BundledPremodularCategory K) : K := by
  classical
  exact
    ∑ j : 𝒞.Simple,
      if IsTransparentSimple 𝒞 j then
        𝒞.quantumDimension j ^ 2
      else 0

/-
ENO global-dimension nonvanishing, applied to the Muger center
`Z_2(C)`.  The transparent objects form a fusion subcategory, and the sum
below is exactly its global dimension.  This is a category-literature input;
it mentions no Kirby diagram, evaluator, manifold, or invariance conclusion.

Reference: Etingof--Nikshych--Ostrik, *On fusion categories*, Theorem 2.3,
applied to the full fusion subcategory of transparent objects.
-/
axiom egno_mugerCenterGlobalDimension_ne_zero
    (𝒞 : BundledPremodularCategory K) :
    transparentGlobalDimension 𝒞 ≠ 0

/-- Kirby-colour killing evaluates the full positive Hopf sum. -/
theorem positiveHopf_rawCycleSum_eq
    (𝒞η : TwistedPremodularCategory K) :
    rawCycleSum 𝒞η positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut
        positiveZeroFramedHopfDiagram.primalDegreeThreeBoundaryData 0 =
      𝒞η.category.globalDimension *
        transparentGlobalDimension 𝒞η.category := by
  rw [positiveHopf_rawCycleSum_zero]
  classical
  rw [Finset.sum_comm]
  calc
    (∑ j : 𝒞η.category.Simple,
        ∑ i : 𝒞η.category.Simple,
          𝒞η.category.quantumDimension i *
            𝒞η.category.quantumDimension j *
              positiveHopfLinkScalar 𝒞η.category i j) =
        ∑ j : 𝒞η.category.Simple,
          𝒞η.category.quantumDimension j *
            (∑ i : 𝒞η.category.Simple,
              𝒞η.category.quantumDimension i *
                positiveHopfLinkScalar 𝒞η.category i j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ j : 𝒞η.category.Simple,
          if IsTransparentSimple 𝒞η.category j then
            𝒞η.category.globalDimension *
              𝒞η.category.quantumDimension j ^ 2
          else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases transparent : IsTransparentSimple 𝒞η.category j
      · rw [if_pos transparent,
          (premodularKirbyColourKilling 𝒞η.category j).1 transparent]
        ring
      · rw [if_neg transparent,
          (premodularKirbyColourKilling 𝒞η.category j).2 transparent]
        ring
    _ = 𝒞η.category.globalDimension *
          transparentGlobalDimension 𝒞η.category := by
      unfold transparentGlobalDimension
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring

theorem positiveHopf_evaluateCycle_zero_eq
    (𝒞η : TwistedPremodularCategory K) :
    evaluateCycle 𝒞η positiveZeroFramedHopfDiagram
        positiveZeroFramedHopfCut
        positiveZeroFramedHopfDiagram.primalDegreeThreeBoundaryData 0 =
      𝒞η.category.globalDimension ^ 2 *
        transparentGlobalDimension 𝒞η.category := by
  unfold evaluateCycle thamDefinition511Normalization
  rw [positiveHopf_rawCycleSum_eq]
  simp [positiveZeroFramedHopfDiagram, positiveHopfHandleData]
  ring

theorem twistedYetter_sphereTwoProduct_zero_eq
    (𝒞η : TwistedPremodularCategory K) :
    TwistedYetter 𝒞η ⟨sphereTwoProduct, 0⟩ =
      𝒞η.category.globalDimension ^ 2 *
        transparentGlobalDimension 𝒞η.category := by
  rw [twistedYetter_sphereTwoProduct_zero_eq_hopfRepresentative]
  rw [positiveHopf_evaluateMarking_eq_zeroCycle]
  exact positiveHopf_evaluateCycle_zero_eq 𝒞η

theorem stabilizationMultiplier_eq
    (𝒞η : TwistedPremodularCategory K) :
    stabilizationMultiplier 𝒞η 𝒞η.category.globalDimension =
      𝒞η.category.globalDimension *
        transparentGlobalDimension 𝒞η.category := by
  unfold stabilizationMultiplier
  rw [twistedYetter_sphereTwoProduct_zero_eq]
  field_simp [egno_globalDimension_ne_zero 𝒞η.category]

theorem stabilizationMultiplier_ne_zero
    (𝒞η : TwistedPremodularCategory K) :
    stabilizationMultiplier 𝒞η 𝒞η.category.globalDimension ≠ 0 := by
  rw [stabilizationMultiplier_eq]
  exact mul_ne_zero
    (egno_globalDimension_ne_zero 𝒞η.category)
    (egno_mugerCenterGlobalDimension_ne_zero 𝒞η.category)

end

end TwistedYetter.StableNoGo
