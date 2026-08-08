import TwistedYetter.StableNoGo.EntranceAxioms
import TwistedYetter.StableNoGo.NumericalDefinitions
import TwistedYetter.StableNoGo.RawMultiplicativity
import TwistedYetter.Kirby.Final.Proofs.TwoThreeTraceFactorization

/-!
# Standard projective-plane and four-sphere diagrams

This file fixes three explicit finite diagrams: the `+1`-framed unknot, the
`-1`-framed unknot, and the empty Kirby diagram.  Its topology axioms identify
only these diagrams and their exact homology coordinates with `CP²`,
`CPbar²`, and `S⁴`.  All category and evaluator equalities are theorem
obligations below that boundary.

For the negative block we choose the manifold generator opposite to the
oriented two-handle core.  Consequently a manifold marking `n h₋` has primal
coordinate `-n` and THAM evaluator coordinate `n`.  This is the convention
used by `negativeShiftedGaussSum`; no dotted-disk sign enters here.
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

/-! ## One framed unknot -/

private def oneFramedUnknotComponents (sign : CrossingSign) : Fin 1 → Component
  | 0 =>
      { role := .ordinary
        orientation := .positive
        integerFraming := sign.toInteger }

private def oneFramedUnknotStrands : Fin 3 → Strand 1
  | 0 => { component := 0, orientation := .positive }
  | 1 => { component := 0, orientation := .negative }
  | 2 => { component := 0, orientation := .positive }

private def oneFramedUnknotEvents (sign : CrossingSign) : Fin 3 → DiagramEvent 3
  | 0 => .birth 0 1
  | 1 => .framingTwist 0 2 sign
  | 2 => .death 2 1

private def oneFramedUnknotActiveOrder : Fin 4 → List (Fin 3)
  | 0 => []
  | 1 => [0, 1]
  | 2 => [2, 1]
  | 3 => []

private theorem oneFramedUnknot_uniqueInputAndOutput (sign : CrossingSign) :
    EveryStrandHasUniqueInputAndOutput (oneFramedUnknotEvents sign) := by
  intro strand
  fin_cases strand <;>
    constructor
  · refine ⟨1, by simp [StrandOccursAsInput, DiagramEvent.beforeWord,
        oneFramedUnknotEvents], ?_⟩
    intro event membership
    fin_cases event <;>
      simp [StrandOccursAsInput, DiagramEvent.beforeWord,
        oneFramedUnknotEvents] at membership ⊢
  · refine ⟨0, by simp [StrandOccursAsOutput, DiagramEvent.afterWord,
        oneFramedUnknotEvents], ?_⟩
    intro event membership
    fin_cases event <;>
      simp [StrandOccursAsOutput, DiagramEvent.afterWord,
        oneFramedUnknotEvents] at membership ⊢
  · refine ⟨2, by simp [StrandOccursAsInput, DiagramEvent.beforeWord,
        oneFramedUnknotEvents], ?_⟩
    intro event membership
    fin_cases event <;>
      simp [StrandOccursAsInput, DiagramEvent.beforeWord,
        oneFramedUnknotEvents] at membership ⊢
  · refine ⟨0, by simp [StrandOccursAsOutput, DiagramEvent.afterWord,
        oneFramedUnknotEvents], ?_⟩
    intro event membership
    fin_cases event <;>
      simp [StrandOccursAsOutput, DiagramEvent.afterWord,
        oneFramedUnknotEvents] at membership ⊢
  · refine ⟨2, by simp [StrandOccursAsInput, DiagramEvent.beforeWord,
        oneFramedUnknotEvents], ?_⟩
    intro event membership
    fin_cases event <;>
      simp [StrandOccursAsInput, DiagramEvent.beforeWord,
        oneFramedUnknotEvents] at membership ⊢
  · refine ⟨1, by simp [StrandOccursAsOutput, DiagramEvent.afterWord,
        oneFramedUnknotEvents], ?_⟩
    intro event membership
    fin_cases event <;>
      simp [StrandOccursAsOutput, DiagramEvent.afterWord,
        oneFramedUnknotEvents] at membership ⊢

private theorem oneFramedUnknot_everyComponentIsConnected
    (sign : CrossingSign) :
    EveryComponentIsConnected oneFramedUnknotStrands
      (oneFramedUnknotEvents sign) := by
  intro component
  fin_cases component
  refine ⟨(0 : Fin 3), rfl, ?_⟩
  intro strand _
  fin_cases strand
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (by
      refine ⟨0, Or.inl ?_⟩
      cases sign <;> decide)
  · exact Relation.ReflTransGen.single (by
      refine ⟨1, Or.inl ?_⟩
      cases sign <;> decide)

/-- The finite birth--twist--death trace of a `±1`-framed unknot. -/
def oneFramedUnknotTrace (sign : CrossingSign) : CombinatorialLinkTrace where
  componentCount := 1
  strandCount := 3
  eventCount := 3
  components := oneFramedUnknotComponents sign
  strands := oneFramedUnknotStrands
  events := oneFramedUnknotEvents sign
  activeOrder := oneFramedUnknotActiveOrder
  initialBoundaryEmpty := rfl
  finalBoundaryEmpty := rfl
  transitionValid := by
    intro i
    fin_cases i
    · exact ⟨[], [], rfl, rfl⟩
    · exact ⟨[], [(1 : Fin 3)], rfl, rfl⟩
    · exact ⟨[], [], rfl, rfl⟩
  activeWordsNoDuplicates := by
    intro i
    fin_cases i <;> decide
  eventPortsAreDistinct := by
    intro i
    fin_cases i <;>
      simp [oneFramedUnknotEvents, DiagramEvent.beforeWord,
        DiagramEvent.afterWord]
  eventContinuationsAreWellFormed := by
    intro i first second membership
    fin_cases i <;>
      simp_all [oneFramedUnknotEvents, DiagramEvent.continuationPairs,
        oneFramedUnknotStrands]
  everyStrandHasUniqueInputAndOutput :=
    oneFramedUnknot_uniqueInputAndOutput sign
  everyComponentIsConnected := oneFramedUnknot_everyComponentIsConnected sign
  framingEventsMatchIntegerFraming := by
    intro component
    fin_cases component
    cases sign <;> decide

private theorem oneFramedUnknot_component_not_dotted
    (sign : CrossingSign) (component : (oneFramedUnknotTrace sign).ComponentId) :
    ((oneFramedUnknotTrace sign).components component).role ≠ .dotted := by
  change Fin 1 at component
  fin_cases component
  simp [oneFramedUnknotTrace, oneFramedUnknotComponents]

private def oneFramedUnknotHandleData (sign : CrossingSign) :
    SpecialHandleData (oneFramedUnknotTrace sign) where
  hOne := 0
  hTwo := 1
  hThree := 0
  oneHandleIndex :=
    { toFun := fun empty => Fin.elim0 empty
      invFun := fun dotted =>
        False.elim (oneFramedUnknot_component_not_dotted sign dotted.1 dotted.2)
      left_inv := fun empty => Fin.elim0 empty
      right_inv := fun dotted =>
        False.elim (oneFramedUnknot_component_not_dotted sign dotted.1 dotted.2) }
  twoHandleIndex :=
    { toFun := fun component =>
        ⟨component, oneFramedUnknot_component_not_dotted sign component⟩
      invFun := fun component => component.1
      left_inv := by intro component; rfl
      right_inv := by intro component; cases component; rfl }
  boundaryTwo := 0
  boundaryThree := 0
  boundary_squared_zero := rfl

/-- The special Kirby diagram of a `±1`-framed unknot. -/
def oneFramedUnknotDiagram (sign : CrossingSign) : SpecialKirbyDiagram where
  trace := oneFramedUnknotTrace sign
  handles := oneFramedUnknotHandleData sign

private def oneFramedUnknotToCutOpenEvent
    {sign : CrossingSign}
    (event : DiagramEvent (oneFramedUnknotTrace sign).strandCount) :
    CutOpenEvent (oneFramedUnknotTrace sign) :=
  match event with
  | .birth left right => .birth left right
  | .death left right => .death left right
  | .crossing overInput underInput overOutput underOutput crossingSign =>
      .crossing overInput underInput overOutput underOutput crossingSign
  | .framingTwist input output crossingSign =>
      .framingTwist input output crossingSign
  | .planarIsotopy continuations => .planarIsotopy continuations

private theorem oneFramedUnknotToCutOpenEvent_beforeWord
    {sign : CrossingSign}
    (event : DiagramEvent (oneFramedUnknotTrace sign).strandCount) :
    (oneFramedUnknotToCutOpenEvent event).beforeWord = event.beforeWord := by
  cases event <;> rfl

private theorem oneFramedUnknotToCutOpenEvent_afterWord
    {sign : CrossingSign}
    (event : DiagramEvent (oneFramedUnknotTrace sign).strandCount) :
    (oneFramedUnknotToCutOpenEvent event).afterWord = event.afterWord := by
  cases event <;> rfl

private def oneFramedUnknotCutOpenExterior (sign : CrossingSign) :
    CutOpenExteriorTrace (oneFramedUnknotTrace sign) where
  eventCount := 3
  events := fun i => oneFramedUnknotToCutOpenEvent
    ((oneFramedUnknotTrace sign).events i)
  activeOrder := oneFramedUnknotActiveOrder
  initialBoundaryEmpty := rfl
  finalBoundaryEmpty := rfl
  transitionValid := by
    intro i
    fin_cases i
    · exact ⟨[], [], rfl, rfl⟩
    · exact ⟨[], [(1 : Fin 3)], rfl, rfl⟩
    · exact ⟨[], [], rfl, rfl⟩
  strandContinuationsAreWellFormed := by
    intro i
    fin_cases i <;>
      simp [oneFramedUnknotTrace, oneFramedUnknotEvents,
        oneFramedUnknotToCutOpenEvent,
        CutOpenEvent.StrandContinuationsAreWellFormed,
        oneFramedUnknotStrands]
  eventPortsAreDistinct := by
    intro i
    simpa only [oneFramedUnknotToCutOpenEvent_beforeWord,
      oneFramedUnknotToCutOpenEvent_afterWord] using
        (oneFramedUnknotTrace sign).eventPortsAreDistinct i
  everyStrandHasUniqueInputAndOutput := by
    simpa only [oneFramedUnknotToCutOpenEvent_beforeWord,
      oneFramedUnknotToCutOpenEvent_afterWord] using
        oneFramedUnknot_uniqueInputAndOutput sign
  activeWordsNoDuplicates := by
    intro i
    exact (oneFramedUnknotTrace sign).activeWordsNoDuplicates i
  activeStrandsAreTwoHandles := by
    intro _ strand _
    exact oneFramedUnknot_component_not_dotted sign
      ((oneFramedUnknotTrace sign).strands strand).component

private def oneFramedUnknotDottedCutData (sign : CrossingSign) :
    DottedCutData (oneFramedUnknotTrace sign) where
  punctureWord := by
    intro dotted dottedRole
    exact False.elim
      (oneFramedUnknot_component_not_dotted sign dotted dottedRole)
  exterior := oneFramedUnknotCutOpenExterior sign

/-- The unknot has no dotted component, so its cut-open trace is the same trace. -/
def oneFramedUnknotCut (sign : CrossingSign) :
    DottedCutPresentation (oneFramedUnknotDiagram sign) where
  cut := oneFramedUnknotDottedCutData sign
  incidence_agrees_with_handle_boundary := by
    intro one
    exact Fin.elim0 one

private def oneFramedUnknotLabeling
    (𝒞 : BundledPremodularCategory K)
    (sign : CrossingSign)
    (simple : 𝒞.simples.Simple) :
    TwoHandleLabeling 𝒞 (oneFramedUnknotDiagram sign) :=
  fun _ => simple

private theorem singletonReplacement_leftContext_empty
    {α : Type*} {left right : List α} {a b c : α}
    (different : a ≠ b)
    (before : [a, c] = left ++ [a] ++ right)
    (after : [b, c] = left ++ [b] ++ right) :
    left = [] := by
  cases left with
  | nil => rfl
  | cons head tail =>
      have beforeHead : a = head := by
        have : some a = some head := by
          simpa only [List.cons_append] using congrArg List.head? before
        exact Option.some.inj this
      have afterHead : b = head := by
        have : some b = some head := by
          simpa only [List.cons_append] using congrArg List.head? after
        exact Option.some.inj this
      exact False.elim (different (beforeHead.trans afterHead.symm))

private theorem append_eq_nil_parts
    {α : Type*} {left right : List α}
    (equality : left ++ right = []) : left = [] ∧ right = [] := by
  cases left with
  | nil => simpa using equality
  | cons head tail => simp at equality

private def oneFramedUnknotEventZero (sign : CrossingSign) :
    Fin (oneFramedUnknotCut sign).cut.exterior.eventCount :=
  ⟨0, by
    simp [oneFramedUnknotCut, oneFramedUnknotDottedCutData,
      oneFramedUnknotCutOpenExterior]⟩

private def oneFramedUnknotEventOne (sign : CrossingSign) :
    Fin (oneFramedUnknotCut sign).cut.exterior.eventCount :=
  ⟨1, by
    simp [oneFramedUnknotCut, oneFramedUnknotDottedCutData,
      oneFramedUnknotCutOpenExterior]⟩

private def oneFramedUnknotEventTwo (sign : CrossingSign) :
    Fin (oneFramedUnknotCut sign).cut.exterior.eventCount :=
  ⟨2, by
    simp [oneFramedUnknotCut, oneFramedUnknotDottedCutData,
      oneFramedUnknotCutOpenExterior]⟩

private theorem oneFramedUnknot_eventLeftContext
    (sign : CrossingSign)
    (i : Fin (oneFramedUnknotCut sign).cut.exterior.eventCount) :
    eventLeftContext (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) i = [] := by
  fin_cases i
  · have transition :=
      eventTransitionEquations (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) (oneFramedUnknotEventZero sign)
    have concatenation := transition.1.symm
    change
      eventLeftContext (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign) (oneFramedUnknotEventZero sign) ++ [] ++
        eventRightContext (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign) (oneFramedUnknotEventZero sign) = []
      at concatenation
    have empty := append_eq_nil_parts (by simpa using concatenation)
    exact empty.1
  · have transition :=
      eventTransitionEquations (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) (oneFramedUnknotEventOne sign)
    apply singletonReplacement_leftContext_empty
        (left := eventLeftContext (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign) (oneFramedUnknotEventOne sign))
        (right := eventRightContext (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign) (oneFramedUnknotEventOne sign))
        (a := (0 : Fin 3)) (b := (2 : Fin 3)) (c := (1 : Fin 3))
    · intro equality
      have : (0 : Nat) = 2 := congrArg Fin.val equality
      omega
    · simpa [oneFramedUnknotCut, oneFramedUnknotDottedCutData,
        oneFramedUnknotCutOpenExterior, oneFramedUnknotTrace,
        oneFramedUnknotEvents, oneFramedUnknotToCutOpenEvent,
        oneFramedUnknotActiveOrder, oneFramedUnknotEventOne,
        CutOpenEvent.beforeWord] using transition.1
    · simpa [oneFramedUnknotCut, oneFramedUnknotDottedCutData,
        oneFramedUnknotCutOpenExterior, oneFramedUnknotTrace,
        oneFramedUnknotEvents, oneFramedUnknotToCutOpenEvent,
        oneFramedUnknotActiveOrder, oneFramedUnknotEventOne,
        CutOpenEvent.afterWord] using transition.2
  · have transition :=
      eventTransitionEquations (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) (oneFramedUnknotEventTwo sign)
    have concatenation := transition.2.symm
    change
      eventLeftContext (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign) (oneFramedUnknotEventTwo sign) ++ [] ++
        eventRightContext (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign) (oneFramedUnknotEventTwo sign) = []
      at concatenation
    have empty := append_eq_nil_parts (by simpa using concatenation)
    exact empty.1

private theorem oneFramedUnknot_eventRightContext
    (sign : CrossingSign)
    (i : Fin (oneFramedUnknotCut sign).cut.exterior.eventCount) :
    eventRightContext (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) i =
      match i.1 with
      | 1 => [(1 : Fin 3)]
      | _ => [] := by
  fin_cases i
  · have transition :=
      eventTransitionEquations (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) (oneFramedUnknotEventZero sign)
    have concatenation := transition.1.symm
    change
      eventLeftContext (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign) (oneFramedUnknotEventZero sign) ++ [] ++
        eventRightContext (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign) (oneFramedUnknotEventZero sign) = []
      at concatenation
    have empty := append_eq_nil_parts (by simpa using concatenation)
    exact empty.2

  · have transition :=
      eventTransitionEquations (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) (oneFramedUnknotEventOne sign)
    have leftEmpty := oneFramedUnknot_eventLeftContext sign
      (oneFramedUnknotEventOne sign)
    rw [leftEmpty] at transition
    have tails := congrArg List.tail transition.1
    simpa [oneFramedUnknotCut, oneFramedUnknotDottedCutData,
      oneFramedUnknotCutOpenExterior, oneFramedUnknotTrace,
      oneFramedUnknotEvents, oneFramedUnknotToCutOpenEvent,
      oneFramedUnknotActiveOrder, oneFramedUnknotEventOne,
      CutOpenEvent.beforeWord] using tails.symm
  · have transition :=
      eventTransitionEquations (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) (oneFramedUnknotEventTwo sign)
    have concatenation := transition.2.symm
    change
      eventLeftContext (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign) (oneFramedUnknotEventTwo sign) ++ [] ++
        eventRightContext (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign) (oneFramedUnknotEventTwo sign) = []
      at concatenation
    have empty := append_eq_nil_parts (by simpa using concatenation)
    exact empty.2

private theorem oneFramedUnknot_zero_one_orientations_differ
    (sign : CrossingSign) :
    ((oneFramedUnknotDiagram sign).trace.strands (0 : Fin 3)).orientation ≠
      ((oneFramedUnknotDiagram sign).trace.strands (1 : Fin 3)).orientation := by
  simp [oneFramedUnknotDiagram, oneFramedUnknotTrace,
    oneFramedUnknotStrands]

private theorem oneFramedUnknot_two_one_orientations_differ
    (sign : CrossingSign) :
    ((oneFramedUnknotDiagram sign).trace.strands (2 : Fin 3)).orientation ≠
      ((oneFramedUnknotDiagram sign).trace.strands (1 : Fin 3)).orientation := by
  simp [oneFramedUnknotDiagram, oneFramedUnknotTrace,
    oneFramedUnknotStrands]

private def oneFramedUnknotPrimalCycle
    (sign : CrossingSign) (n : ℤ) :
    PrimalTwoCycles (oneFramedUnknotDiagram sign) :=
  ⟨fun _ => n, by ext one; exact Fin.elim0 one⟩

private def oneFramedUnknotPrimalClass
    (sign : CrossingSign) (n : ℤ) :
    PrimalKirbyH₂ (oneFramedUnknotDiagram sign).primalDegreeThreeBoundaryData :=
  primalCycleClass _ (oneFramedUnknotPrimalCycle sign n)

private def oneFramedUnknotThamCycle
    (sign : CrossingSign) (n : ℤ) :
    ThamTwoCycles (oneFramedUnknotDiagram sign).primalDegreeThreeBoundaryData :=
  ⟨fun _ => n, by ext three; exact Fin.elim0 three⟩

private def oneFramedUnknotThamClass
    (sign : CrossingSign) (n : ℤ) :
    ThamKirbyH₂ (oneFramedUnknotDiagram sign).primalDegreeThreeBoundaryData :=
  thamCycleClass _ (oneFramedUnknotThamCycle sign n)

private theorem oneFramedUnknot_eventZeroContextualEdge
    (𝒞 : BundledPremodularCategory K)
    (sign : CrossingSign)
    (simple : 𝒞.simples.Simple) :
    eqToHom
        (congrArg
          (fun word => ribbonWordObject 𝒞
            (exteriorWord 𝒞 (oneFramedUnknotDiagram sign)
              (oneFramedUnknotLabeling 𝒞 sign simple) word))
          (show (oneFramedUnknotCut sign).cut.exterior.activeOrder
              (oneFramedUnknotEventZero sign).castSucc = [] by rfl)).symm ≫
      compileContextualCutOpenEventMorphism 𝒞
        (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
        (oneFramedUnknotLabeling 𝒞 sign simple)
        (oneFramedUnknotEventZero sign) ≫
      eqToHom
        (congrArg
          (fun word => ribbonWordObject 𝒞
            (exteriorWord 𝒞 (oneFramedUnknotDiagram sign)
              (oneFramedUnknotLabeling 𝒞 sign simple) word))
          (show (oneFramedUnknotCut sign).cut.exterior.activeOrder
              (oneFramedUnknotEventZero sign).succ = [(0 : Fin 3), (1 : Fin 3)] by rfl)) =
      pairedBirthMorphism 𝒞 (oneFramedUnknotDiagram sign)
        (oneFramedUnknotLabeling 𝒞 sign simple)
        (0 : Fin 3) (1 : Fin 3) (by rfl)
        (oneFramedUnknot_zero_one_orientations_differ sign) := by
  let i := oneFramedUnknotEventZero sign
  have eventEq :
      (oneFramedUnknotCut sign).cut.exterior.events i =
        .birth (0 : Fin 3) (1 : Fin 3) := by
    rfl
  have beforeEq :
      (oneFramedUnknotCut sign).cut.exterior.activeOrder i.castSucc = [] := by rfl
  have afterEq :
      (oneFramedUnknotCut sign).cut.exterior.activeOrder i.succ =
        [(0 : Fin 3), (1 : Fin 3)] := by rfl
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  simpa [i] using
    (compileContextualFromWitness_eq_birth
      𝒞 (oneFramedUnknotDiagram sign)
      (oneFramedUnknotLabeling 𝒞 sign simple)
      ((oneFramedUnknotCut sign).cut.exterior.events i)
      (0 : Fin 3) (1 : Fin 3)
      ((oneFramedUnknotCut sign).cut.exterior.activeOrder i.castSucc)
      ((oneFramedUnknotCut sign).cut.exterior.activeOrder i.succ)
      (eventLeftContext (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) i)
      (eventRightContext (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) i)
      (eventTransitionEquations (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) i).1
      (eventTransitionEquations (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) i).2
      ((oneFramedUnknotCut sign).cut.exterior.strandContinuationsAreWellFormed i)
      eventEq beforeEq afterEq
      (oneFramedUnknot_eventLeftContext sign i)
      (oneFramedUnknot_eventRightContext sign i))

private theorem oneFramedUnknot_eventZeroDirect
    (𝒞 : BundledPremodularCategory K)
    (sign : CrossingSign)
    (simple : 𝒞.simples.Simple) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞
        (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
        (oneFramedUnknotLabeling 𝒞 sign simple)
        (oneFramedUnknotEventZero sign))
      (canonicalPositiveNegativeBirth 𝒞 simple) := by
  refine
    (middle_heq_of_transport_sandwich_eq _ _ _ _
      (oneFramedUnknot_eventZeroContextualEdge 𝒞 sign simple)).trans ?_
  have labelEq :
      exteriorStrandLabel 𝒞 (oneFramedUnknotDiagram sign)
          (oneFramedUnknotLabeling 𝒞 sign simple) (1 : Fin 3) = simple := by
    rfl
  have leftPositive :
      ((oneFramedUnknotDiagram sign).trace.strands (0 : Fin 3)).orientation =
        .positive := by
    rfl
  unfold pairedBirthMorphism
  simp only [leftPositive, ↓reduceDIte]
  exact
    (CategoryTheory.comp_eqToHom_heq _ _).trans
      (canonicalPositiveNegativeBirth_heq 𝒞 labelEq)

private theorem oneFramedUnknot_eventOneDirect
    (𝒞 : BundledPremodularCategory K)
    (sign : CrossingSign)
    (simple : 𝒞.simples.Simple) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞
        (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
        (oneFramedUnknotLabeling 𝒞 sign simple)
        (oneFramedUnknotEventOne sign))
      (contextualizeRibbonMorphism 𝒞
        []
        [{ label := simple, direction := .forward }]
        [{ label := simple, direction := .forward }]
        [{ label := simple, direction := .dual }]
        (canonicalFramingTwistMorphism 𝒞
          { label := simple, direction := .forward }
          { label := simple, direction := .forward }
          sign rfl)) := by
  let i := oneFramedUnknotEventOne sign
  have eventEq :
      (oneFramedUnknotCut sign).cut.exterior.events i =
        .framingTwist (0 : Fin 3) (2 : Fin 3) sign := by
    rfl
  have localEdge :=
    compileFramingTwistMorphism_heq_canonical
      𝒞 (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
      (oneFramedUnknotLabeling 𝒞 sign simple)
      (0 : Fin 3) (2 : Fin 3) sign
      (eventEq ▸
        (oneFramedUnknotCut sign).cut.exterior.strandContinuationsAreWellFormed i)
  have core :=
    (compileContextualCutOpenEventMorphism_heq_core
      𝒞 (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
      (oneFramedUnknotLabeling 𝒞 sign simple) i).trans
      (contextualizeRibbonMorphism_heq 𝒞
        (congrArg (exteriorWord 𝒞 (oneFramedUnknotDiagram sign)
          (oneFramedUnknotLabeling 𝒞 sign simple))
          (oneFramedUnknot_eventLeftContext sign i))
        (congrArg (exteriorWord 𝒞 (oneFramedUnknotDiagram sign)
          (oneFramedUnknotLabeling 𝒞 sign simple))
          (congrArg CutOpenEvent.beforeWord eventEq))
        (congrArg (exteriorWord 𝒞 (oneFramedUnknotDiagram sign)
          (oneFramedUnknotLabeling 𝒞 sign simple))
          (congrArg CutOpenEvent.afterWord eventEq))
        (congrArg (exteriorWord 𝒞 (oneFramedUnknotDiagram sign)
          (oneFramedUnknotLabeling 𝒞 sign simple))
          (oneFramedUnknot_eventRightContext sign i))
        localEdge)
  simpa [exteriorWord, oneFramedUnknotDiagram,
    oneFramedUnknotTrace, oneFramedUnknotStrands,
    oneFramedUnknotLabeling, oneFramedUnknotEventOne, eventEq] using core

private theorem oneFramedUnknot_eventTwoContextualEdge
    (𝒞 : BundledPremodularCategory K)
    (sign : CrossingSign)
    (simple : 𝒞.simples.Simple) :
    eqToHom
        (congrArg
          (fun word => ribbonWordObject 𝒞
            (exteriorWord 𝒞 (oneFramedUnknotDiagram sign)
              (oneFramedUnknotLabeling 𝒞 sign simple) word))
          (show (oneFramedUnknotCut sign).cut.exterior.activeOrder
              (oneFramedUnknotEventTwo sign).castSucc = [(2 : Fin 3), (1 : Fin 3)] by rfl)).symm ≫
      compileContextualCutOpenEventMorphism 𝒞
        (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
        (oneFramedUnknotLabeling 𝒞 sign simple)
        (oneFramedUnknotEventTwo sign) ≫
      eqToHom
        (congrArg
          (fun word => ribbonWordObject 𝒞
            (exteriorWord 𝒞 (oneFramedUnknotDiagram sign)
              (oneFramedUnknotLabeling 𝒞 sign simple) word))
          (show (oneFramedUnknotCut sign).cut.exterior.activeOrder
              (oneFramedUnknotEventTwo sign).succ = [] by rfl)) =
      pairedDeathMorphism 𝒞 (oneFramedUnknotDiagram sign)
        (oneFramedUnknotLabeling 𝒞 sign simple)
        (2 : Fin 3) (1 : Fin 3) (by rfl)
        (oneFramedUnknot_two_one_orientations_differ sign) := by
  let i := oneFramedUnknotEventTwo sign
  have eventEq :
      (oneFramedUnknotCut sign).cut.exterior.events i =
        .death (2 : Fin 3) (1 : Fin 3) := by
    rfl
  have beforeEq :
      (oneFramedUnknotCut sign).cut.exterior.activeOrder i.castSucc =
        [(2 : Fin 3), (1 : Fin 3)] := by rfl
  have afterEq :
      (oneFramedUnknotCut sign).cut.exterior.activeOrder i.succ = [] := by rfl
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  simpa [i] using
    (compileContextualFromWitness_eq_death
      𝒞 (oneFramedUnknotDiagram sign)
      (oneFramedUnknotLabeling 𝒞 sign simple)
      ((oneFramedUnknotCut sign).cut.exterior.events i)
      (2 : Fin 3) (1 : Fin 3)
      ((oneFramedUnknotCut sign).cut.exterior.activeOrder i.castSucc)
      ((oneFramedUnknotCut sign).cut.exterior.activeOrder i.succ)
      (eventLeftContext (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) i)
      (eventRightContext (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) i)
      (eventTransitionEquations (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) i).1
      (eventTransitionEquations (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign) i).2
      ((oneFramedUnknotCut sign).cut.exterior.strandContinuationsAreWellFormed i)
      eventEq beforeEq afterEq
      (oneFramedUnknot_eventLeftContext sign i)
      (oneFramedUnknot_eventRightContext sign i))

private theorem oneFramedUnknot_eventTwoDirect
    (𝒞 : BundledPremodularCategory K)
    (sign : CrossingSign)
    (simple : 𝒞.simples.Simple) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞
        (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
        (oneFramedUnknotLabeling 𝒞 sign simple)
        (oneFramedUnknotEventTwo sign))
      (canonicalPositiveNegativeDeath 𝒞 simple) := by
  refine
    (middle_heq_of_transport_sandwich_eq _ _ _ _
      (oneFramedUnknot_eventTwoContextualEdge 𝒞 sign simple)).trans ?_
  have labelEq :
      exteriorStrandLabel 𝒞 (oneFramedUnknotDiagram sign)
          (oneFramedUnknotLabeling 𝒞 sign simple) (1 : Fin 3) = simple := by
    rfl
  have leftPositive :
      ((oneFramedUnknotDiagram sign).trace.strands (2 : Fin 3)).orientation =
        .positive := by
    rfl
  unfold pairedDeathMorphism
  simp only [leftPositive, ↓reduceDIte]
  exact
    (CategoryTheory.eqToHom_comp_heq _ _).trans
      (canonicalPositiveNegativeDeath_heq 𝒞 labelEq)

/-- The generic compiler reads the explicit unknot trace as birth, one
framing twist of the recorded sign, and death. -/
theorem compileOneFramedUnknot_eq_canonicalClosure
    (𝒞 : BundledPremodularCategory K)
    (sign : CrossingSign)
    (simple : 𝒞.simples.Simple) :
    compileCutOpenExteriorMorphism 𝒞
        (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign)
        (oneFramedUnknotLabeling 𝒞 sign simple) =
      canonicalPositiveNegativeBirth 𝒞 simple ≫
        contextualizeRibbonMorphism 𝒞
          []
          [{ label := simple, direction := .forward }]
          [{ label := simple, direction := .forward }]
          [{ label := simple, direction := .dual }]
          (canonicalFramingTwistMorphism 𝒞
            { label := simple, direction := .forward }
            { label := simple, direction := .forward }
            sign rfl) ≫
        canonicalPositiveNegativeDeath 𝒞 simple := by
  rw [compileCutOpenExteriorMorphism_eq_compiledTrace]
  simp only [FiniteMorphismTrace.composeAll]
  change
    eqToHom _ ≫
        (compiledExteriorTrace 𝒞 (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign)
          (oneFramedUnknotLabeling 𝒞 sign simple)).composePrefix 3 _ ≫
      eqToHom _ = _
  simp only [FiniteMorphismTrace.composePrefix, compiledExteriorTrace,
    compileRoleAwareContextualCutOpenEventMorphism_eq_elementary]
  change
    eqToHom _ ≫
        (((𝟙 _ ≫
            compileContextualCutOpenEventMorphism 𝒞
              (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
              (oneFramedUnknotLabeling 𝒞 sign simple)
              (oneFramedUnknotEventZero sign)) ≫
          compileContextualCutOpenEventMorphism 𝒞
            (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
            (oneFramedUnknotLabeling 𝒞 sign simple)
            (oneFramedUnknotEventOne sign)) ≫
        compileContextualCutOpenEventMorphism 𝒞
          (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
          (oneFramedUnknotLabeling 𝒞 sign simple)
          (oneFramedUnknotEventTwo sign)) ≫
      eqToHom _ = _
  have eventZero := oneFramedUnknot_eventZeroDirect 𝒞 sign simple
  have eventOne := oneFramedUnknot_eventOneDirect 𝒞 sign simple
  have eventTwo := oneFramedUnknot_eventTwoDirect 𝒞 sign simple
  have eventZeroFromIdentity :
      HEq
        (𝟙 _ ≫
          compileContextualCutOpenEventMorphism 𝒞
            (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
            (oneFramedUnknotLabeling 𝒞 sign simple)
            (oneFramedUnknotEventZero sign))
        (canonicalPositiveNegativeBirth 𝒞 simple) :=
    (heq_of_eq (Category.id_comp _)).trans eventZero
  have firstTwo :=
    CategoryTheory.heq_comp rfl rfl rfl eventZeroFromIdentity eventOne
  have allThree :=
    CategoryTheory.heq_comp rfl rfl rfl firstTwo eventTwo
  have allThreeAssociated :
      HEq
        (((𝟙 _ ≫
            compileContextualCutOpenEventMorphism 𝒞
              (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
              (oneFramedUnknotLabeling 𝒞 sign simple)
              (oneFramedUnknotEventZero sign)) ≫
          compileContextualCutOpenEventMorphism 𝒞
            (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
            (oneFramedUnknotLabeling 𝒞 sign simple)
            (oneFramedUnknotEventOne sign)) ≫
        compileContextualCutOpenEventMorphism 𝒞
          (oneFramedUnknotDiagram sign) (oneFramedUnknotCut sign)
          (oneFramedUnknotLabeling 𝒞 sign simple)
          (oneFramedUnknotEventTwo sign))
        (canonicalPositiveNegativeBirth 𝒞 simple ≫
          contextualizeRibbonMorphism 𝒞
            []
            [{ label := simple, direction := .forward }]
            [{ label := simple, direction := .forward }]
            [{ label := simple, direction := .dual }]
            (canonicalFramingTwistMorphism 𝒞
              { label := simple, direction := .forward }
              { label := simple, direction := .forward }
              sign rfl) ≫
          canonicalPositiveNegativeDeath 𝒞 simple) := by
    simpa only [Category.assoc] using allThree
  exact eq_of_heq
    ((transport_sandwich_heq _ _ _).trans allThreeAssociated)

theorem oneFramedUnknot_compiledScalar
    (𝒞η : TwistedPremodularCategory K)
    (sign : CrossingSign)
    (n : ℤ)
    (simple : 𝒞η.category.Simple) :
    canonicalRibbonGraphicalEvaluation 𝒞η.category
        (canonicalRoleAwareGraphCompiler 𝒞η
          (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign)
          (oneFramedUnknotDiagram sign).primalDegreeThreeBoundaryData
          (oneFramedUnknotLabeling 𝒞η.category sign simple)
          (oneFramedUnknotThamCycle sign n)) =
      𝒞η.category.quantumDimension simple *
        match sign with
        | .positive => simpleTwistScalar 𝒞η simple
        | .negative => (simpleTwistScalar 𝒞η simple)⁻¹ := by
  change
    𝒞η.category.closedScalar
        (compileCutOpenExteriorMorphism 𝒞η.category
          (oneFramedUnknotDiagram sign)
          (oneFramedUnknotCut sign)
          (oneFramedUnknotLabeling 𝒞η.category sign simple)) = _
  rw [compileOneFramedUnknot_eq_canonicalClosure]
  cases sign
  · rw [canonicalPositiveFramedLoop_eq_ribbonTrace]
    exact closedScalar_ribbonTrace_twist 𝒞η simple
  · rw [canonicalNegativeFramedLoop_eq_ribbonTrace]
    exact closedScalar_ribbonTrace_twist_inv 𝒞η simple

theorem oneFramedUnknot_rawEvaluatorSummand
    (𝒞η : TwistedPremodularCategory K)
    (sign : CrossingSign)
    (n : ℤ)
    (simple : 𝒞η.category.Simple) :
    rawEvaluatorSummand 𝒞η
        (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign)
        (oneFramedUnknotDiagram sign).primalDegreeThreeBoundaryData
        (oneFramedUnknotThamCycle sign n)
        (oneFramedUnknotLabeling 𝒞η.category sign simple) =
      𝒞η.category.quantumDimension simple ^ 2 *
        (match sign with
          | .positive => simpleTwistScalar 𝒞η simple
          | .negative => (simpleTwistScalar 𝒞η simple)⁻¹) *
        ((((𝒞η.character.value simple) ^ n : Kˣ) : K)) := by
  unfold rawEvaluatorSummand
  rw [show ordinaryKirbyWeight 𝒞η.category
      (oneFramedUnknotLabeling 𝒞η.category sign simple) =
        𝒞η.category.quantumDimension simple by
    simp [ordinaryKirbyWeight, oneFramedUnknotDiagram,
      oneFramedUnknotHandleData, oneFramedUnknotLabeling,
      𝒞η.category.simples_quantumDimension_eq]]
  rw [show characterWeight 𝒞η
      (oneFramedUnknotLabeling 𝒞η.category sign simple)
      (oneFramedUnknotThamCycle sign n) =
        ((((𝒞η.character.value simple) ^ n : Kˣ) : K)) by
    simp [characterWeight, oneFramedUnknotDiagram,
      oneFramedUnknotHandleData, oneFramedUnknotLabeling,
      oneFramedUnknotThamCycle]]
  rw [oneFramedUnknot_compiledScalar 𝒞η sign n simple]
  ring

/-! ## Exact topology and coordinate bindings -/

axiom positiveOneFramedUnknot_realizes_complexProjectivePlane :
  OrientedDiffeomorphism
    (realizeSpecialKirbyDiagram (oneFramedUnknotDiagram .positive))
    complexProjectivePlane

axiom negativeOneFramedUnknot_realizes_reversedComplexProjectivePlane :
  OrientedDiffeomorphism
    (realizeSpecialKirbyDiagram (oneFramedUnknotDiagram .negative))
    reversedComplexProjectivePlane

/-- Positive block: primal coordinate `n` is the manifold class `n h₊`. -/
axiom positiveOneFramedUnknot_primalCoordinate
    (n : ℤ) :
    inducedH₂ positiveOneFramedUnknot_realizes_complexProjectivePlane
        (specialKirbyDiagram_computesH₂
          (oneFramedUnknotDiagram .positive)
          (oneFramedUnknotPrimalClass .positive n)) =
      n • positiveProjectivePlaneGenerator

/-- Negative block: by convention primal coordinate `-n` is `n h₋`. -/
axiom negativeOneFramedUnknot_primalCoordinate
    (n : ℤ) :
    inducedH₂ negativeOneFramedUnknot_realizes_reversedComplexProjectivePlane
        (specialKirbyDiagram_computesH₂
          (oneFramedUnknotDiagram .negative)
          (oneFramedUnknotPrimalClass .negative (-n))) =
      n • negativeProjectivePlaneGenerator

/-- Positive block: the corresponding THAM evaluator coordinate is `n`. -/
axiom positiveOneFramedUnknot_turnoverCoordinate
    (n : ℤ) :
    turnoverPoincareDualityEquiv
        (oneFramedUnknotDiagram .positive)
        (specialKirbyDiagram_computesH₂
          (oneFramedUnknotDiagram .positive))
        (oneFramedUnknotPrimalClass .positive n) =
      oneFramedUnknotThamClass .positive n

/-- Negative block: primal coordinate `-n` has THAM evaluator coordinate `n`. -/
axiom negativeOneFramedUnknot_turnoverCoordinate
    (n : ℤ) :
    turnoverPoincareDualityEquiv
        (oneFramedUnknotDiagram .negative)
        (specialKirbyDiagram_computesH₂
          (oneFramedUnknotDiagram .negative))
        (oneFramedUnknotPrimalClass .negative (-n)) =
      oneFramedUnknotThamClass .negative n

/-- The canonical marked positive projective-plane representative. -/
noncomputable def positiveProjectivePlaneRepresentative (n : ℤ) :
    SpecialKirbyRepresentativeOf complexProjectivePlane where
  diagram := oneFramedUnknotDiagram .positive
  cut := oneFramedUnknotCut .positive
  realizationDiffeomorphism :=
    positiveOneFramedUnknot_realizes_complexProjectivePlane
  alpha := oneFramedUnknotPrimalClass .positive n

theorem positiveProjectivePlaneRepresentative_represents
    (n : ℤ) :
    (positiveProjectivePlaneRepresentative n).representsHomologyClass
      (n • positiveProjectivePlaneGenerator) := by
  exact positiveOneFramedUnknot_primalCoordinate n

theorem positiveProjectivePlaneRepresentative_thamAlpha
    (n : ℤ) :
    (positiveProjectivePlaneRepresentative n).thamAlpha =
      oneFramedUnknotThamClass .positive n := by
  exact positiveOneFramedUnknot_turnoverCoordinate n

/-- The canonical marked reverse projective-plane representative. -/
noncomputable def negativeProjectivePlaneRepresentative (n : ℤ) :
    SpecialKirbyRepresentativeOf reversedComplexProjectivePlane where
  diagram := oneFramedUnknotDiagram .negative
  cut := oneFramedUnknotCut .negative
  realizationDiffeomorphism :=
    negativeOneFramedUnknot_realizes_reversedComplexProjectivePlane
  alpha := oneFramedUnknotPrimalClass .negative (-n)

theorem negativeProjectivePlaneRepresentative_represents
    (n : ℤ) :
    (negativeProjectivePlaneRepresentative n).representsHomologyClass
      (n • negativeProjectivePlaneGenerator) := by
  exact negativeOneFramedUnknot_primalCoordinate n

theorem negativeProjectivePlaneRepresentative_thamAlpha
    (n : ℤ) :
    (negativeProjectivePlaneRepresentative n).thamAlpha =
      oneFramedUnknotThamClass .negative n := by
  exact negativeOneFramedUnknot_turnoverCoordinate n

private theorem twistedYetter_eq_projectivePlaneRepresentative
    (𝒞η : TwistedPremodularCategory K)
    (sign : CrossingSign) (n : ℤ) :
    TwistedYetter 𝒞η
        (match sign with
        | .positive => ⟨complexProjectivePlane,
            n • positiveProjectivePlaneGenerator⟩
        | .negative => ⟨reversedComplexProjectivePlane,
            n • negativeProjectivePlaneGenerator⟩) =
      evaluateMarkedDiagram 𝒞η
        (match sign with
        | .positive =>
            (positiveProjectivePlaneRepresentative n).toHomologicallyMarkedDiagram
        | .negative =>
            (negativeProjectivePlaneRepresentative n).toHomologicallyMarkedDiagram) := by
  cases sign with
  | positive =>
      unfold TwistedYetter
      let chosenExistence :=
        specialKirbyRepresentative_exists complexProjectivePlane
          (n • positiveProjectivePlaneGenerator)
      exact
        ConditionalDescent.diffeomorphism_invariant_of_descent_data
          𝒞η
          (fun marked =>
            frozenFrontendRepresentativeIndependence
              𝒞η marked.diagram marked.cut marked.primalBoundary)
          (frozenFrontendLocalMoveInvariance 𝒞η)
          complexProjectivePlane complexProjectivePlane
          (identityOrientedDiffeomorphism complexProjectivePlane)
          (n • positiveProjectivePlaneGenerator)
          chosenExistence.choose chosenExistence.choose_spec
          (positiveProjectivePlaneRepresentative n)
          (by
            rw [inducedH₂_identityOrientedDiffeomorphism]
            exact positiveProjectivePlaneRepresentative_represents n)
  | negative =>
      unfold TwistedYetter
      let chosenExistence :=
        specialKirbyRepresentative_exists reversedComplexProjectivePlane
          (n • negativeProjectivePlaneGenerator)
      exact
        ConditionalDescent.diffeomorphism_invariant_of_descent_data
          𝒞η
          (fun marked =>
            frozenFrontendRepresentativeIndependence
              𝒞η marked.diagram marked.cut marked.primalBoundary)
          (frozenFrontendLocalMoveInvariance 𝒞η)
          reversedComplexProjectivePlane reversedComplexProjectivePlane
          (identityOrientedDiffeomorphism reversedComplexProjectivePlane)
          (n • negativeProjectivePlaneGenerator)
          chosenExistence.choose chosenExistence.choose_spec
          (negativeProjectivePlaneRepresentative n)
          (by
            rw [inducedH₂_identityOrientedDiffeomorphism]
            exact negativeProjectivePlaneRepresentative_represents n)

private theorem projectivePlane_evaluateMarking_eq_explicitCycle
    (𝒞η : TwistedPremodularCategory K)
    (sign : CrossingSign) (n : ℤ) :
    evaluateMarkedDiagram 𝒞η
        (match sign with
        | .positive =>
            (positiveProjectivePlaneRepresentative n).toHomologicallyMarkedDiagram
        | .negative =>
            (negativeProjectivePlaneRepresentative n).toHomologicallyMarkedDiagram) =
      evaluateCycle 𝒞η (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign)
        (oneFramedUnknotDiagram sign).primalDegreeThreeBoundaryData
        (oneFramedUnknotThamCycle sign n) := by
  cases sign with
  | positive =>
      apply frozenFrontendRepresentativeIndependence
      change
        thamCycleClass _
            (Quotient.out (positiveProjectivePlaneRepresentative n).thamAlpha) =
          thamCycleClass _ (oneFramedUnknotThamCycle .positive n)
      rw [show thamCycleClass _
          (Quotient.out (positiveProjectivePlaneRepresentative n).thamAlpha) =
          (positiveProjectivePlaneRepresentative n).thamAlpha by
        exact Quotient.out_eq _]
      rw [positiveProjectivePlaneRepresentative_thamAlpha]
      rfl
  | negative =>
      apply frozenFrontendRepresentativeIndependence
      change
        thamCycleClass _
            (Quotient.out (negativeProjectivePlaneRepresentative n).thamAlpha) =
          thamCycleClass _ (oneFramedUnknotThamCycle .negative n)
      rw [show thamCycleClass _
          (Quotient.out (negativeProjectivePlaneRepresentative n).thamAlpha) =
          (negativeProjectivePlaneRepresentative n).thamAlpha by
        exact Quotient.out_eq _]
      rw [negativeProjectivePlaneRepresentative_thamAlpha]
      rfl

theorem oneFramedUnknot_rawCycleSum
    (𝒞η : TwistedPremodularCategory K)
    (sign : CrossingSign) (n : ℤ) :
    rawCycleSum 𝒞η (oneFramedUnknotDiagram sign)
        (oneFramedUnknotCut sign)
        (oneFramedUnknotDiagram sign).primalDegreeThreeBoundaryData
        (oneFramedUnknotThamCycle sign n) =
      match sign with
      | .positive => positiveShiftedGaussSum 𝒞η n
      | .negative => negativeShiftedGaussSum 𝒞η n := by
  classical
  rw [rawCycleSum_eq_sum_rawEvaluatorSummand]
  cases sign with
  | positive =>
      unfold positiveShiftedGaussSum
      apply Fintype.sum_equiv
        (Equiv.funUnique (Fin 1) 𝒞η.category.Simple)
      intro labeling
      have labelingEq :
          labeling = oneFramedUnknotLabeling 𝒞η.category .positive (labeling 0) := by
        funext handle
        fin_cases handle
        rfl
      rw [labelingEq]
      simpa using
        oneFramedUnknot_rawEvaluatorSummand
          𝒞η .positive n (labeling (0 : Fin 1))
  | negative =>
      unfold negativeShiftedGaussSum
      apply Fintype.sum_equiv
        (Equiv.funUnique (Fin 1) 𝒞η.category.Simple)
      intro labeling
      have labelingEq :
          labeling = oneFramedUnknotLabeling 𝒞η.category .negative (labeling 0) := by
        funext handle
        fin_cases handle
        rfl
      rw [labelingEq]
      simpa using
        oneFramedUnknot_rawEvaluatorSummand
          𝒞η .negative n (labeling (0 : Fin 1))

theorem twistedYetter_complexProjectivePlane
    (𝒞η : TwistedPremodularCategory K) (n : ℤ) :
    TwistedYetter 𝒞η
        ⟨complexProjectivePlane, n • positiveProjectivePlaneGenerator⟩ =
      𝒞η.category.globalDimension * positiveShiftedGaussSum 𝒞η n := by
  rw [twistedYetter_eq_projectivePlaneRepresentative 𝒞η .positive n]
  rw [projectivePlane_evaluateMarking_eq_explicitCycle 𝒞η .positive n]
  unfold evaluateCycle thamDefinition511Normalization
  rw [oneFramedUnknot_rawCycleSum]
  simp [oneFramedUnknotDiagram, oneFramedUnknotHandleData]

theorem twistedYetter_reversedComplexProjectivePlane
    (𝒞η : TwistedPremodularCategory K) (n : ℤ) :
    TwistedYetter 𝒞η
        ⟨reversedComplexProjectivePlane, n • negativeProjectivePlaneGenerator⟩ =
      𝒞η.category.globalDimension * negativeShiftedGaussSum 𝒞η n := by
  rw [twistedYetter_eq_projectivePlaneRepresentative 𝒞η .negative n]
  rw [projectivePlane_evaluateMarking_eq_explicitCycle 𝒞η .negative n]
  unfold evaluateCycle thamDefinition511Normalization
  rw [oneFramedUnknot_rawCycleSum]
  simp [oneFramedUnknotDiagram, oneFramedUnknotHandleData]

/-! ## Empty diagram for `S⁴` -/

/-- The empty closed link trace. -/
def emptyKirbyTrace : CombinatorialLinkTrace where
  componentCount := 0
  strandCount := 0
  eventCount := 0
  components := fun component => Fin.elim0 component
  strands := fun strand => Fin.elim0 strand
  events := fun event => Fin.elim0 event
  activeOrder := fun _ => []
  initialBoundaryEmpty := rfl
  finalBoundaryEmpty := rfl
  transitionValid := fun event => Fin.elim0 event
  activeWordsNoDuplicates := by intro _; exact List.nodup_nil
  eventPortsAreDistinct := fun event => Fin.elim0 event
  eventContinuationsAreWellFormed := fun event => Fin.elim0 event
  everyStrandHasUniqueInputAndOutput := fun strand => Fin.elim0 strand
  everyComponentIsConnected := fun component => Fin.elim0 component
  framingEventsMatchIntegerFraming := fun component => Fin.elim0 component

private def emptyKirbyHandleData : SpecialHandleData emptyKirbyTrace where
  hOne := 0
  hTwo := 0
  hThree := 0
  oneHandleIndex :=
    { toFun := fun index => Fin.elim0 index
      invFun := fun component => Fin.elim0 component.1
      left_inv := fun index => Fin.elim0 index
      right_inv := fun component => Fin.elim0 component.1 }
  twoHandleIndex :=
    { toFun := fun index => Fin.elim0 index
      invFun := fun component => Fin.elim0 component.1
      left_inv := fun index => Fin.elim0 index
      right_inv := fun component => Fin.elim0 component.1 }
  boundaryTwo := 0
  boundaryThree := 0
  boundary_squared_zero := rfl

/-- The special Kirby diagram with no one-, two-, or three-handles. -/
def emptyKirbyDiagram : SpecialKirbyDiagram where
  trace := emptyKirbyTrace
  handles := emptyKirbyHandleData

private def emptyCutOpenExterior : CutOpenExteriorTrace emptyKirbyTrace where
  eventCount := 0
  events := fun event => Fin.elim0 event
  activeOrder := fun _ => []
  initialBoundaryEmpty := rfl
  finalBoundaryEmpty := rfl
  transitionValid := fun event => Fin.elim0 event
  strandContinuationsAreWellFormed := fun event => Fin.elim0 event
  eventPortsAreDistinct := fun event => Fin.elim0 event
  everyStrandHasUniqueInputAndOutput := fun strand => Fin.elim0 strand
  activeWordsNoDuplicates := by intro _; exact List.nodup_nil
  activeStrandsAreTwoHandles := fun _ strand => Fin.elim0 strand

private def emptyDottedCutData : DottedCutData emptyKirbyTrace where
  punctureWord := fun dotted => Fin.elim0 dotted
  exterior := emptyCutOpenExterior

/-- The empty diagram has the unique empty dotted-cut presentation. -/
def emptyKirbyCut : DottedCutPresentation emptyKirbyDiagram where
  cut := emptyDottedCutData
  incidence_agrees_with_handle_boundary := fun one => Fin.elim0 one

axiom emptyKirbyDiagram_realizes_fourSphere :
  OrientedDiffeomorphism
    (realizeSpecialKirbyDiagram emptyKirbyDiagram) fourSphere

/-- The zero-marked empty representative of `S⁴`. -/
noncomputable def emptyFourSphereRepresentative :
    SpecialKirbyRepresentativeOf fourSphere where
  diagram := emptyKirbyDiagram
  cut := emptyKirbyCut
  realizationDiffeomorphism := emptyKirbyDiagram_realizes_fourSphere
  alpha := 0

theorem emptyFourSphereRepresentative_represents_zero :
    emptyFourSphereRepresentative.representsHomologyClass 0 := by
  exact map_zero _

private theorem emptyKirby_compile_eq_identity
    (𝒞 : BundledPremodularCategory K)
    (labeling : TwoHandleLabeling 𝒞 emptyKirbyDiagram) :
    compileCutOpenExteriorMorphism 𝒞 emptyKirbyDiagram emptyKirbyCut labeling =
      𝟙 (𝟙_ 𝒞.C) := by
  rw [compileCutOpenExteriorMorphism_eq_compiledTrace]
  simp [FiniteMorphismTrace.composeAll,
    FiniteMorphismTrace.composePrefix, compiledExteriorTrace,
    emptyKirbyDiagram, emptyKirbyCut, emptyDottedCutData,
    emptyCutOpenExterior, exteriorWord, ribbonWordObject]

theorem twistedYetter_fourSphere_zero
    (𝒞η : TwistedPremodularCategory K) :
    TwistedYetter 𝒞η ⟨fourSphere, 0⟩ =
      𝒞η.category.globalDimension := by
  let chosenExistence := specialKirbyRepresentative_exists fourSphere 0
  rw [show TwistedYetter 𝒞η ⟨fourSphere, 0⟩ =
      evaluateMarkedDiagram 𝒞η emptyFourSphereRepresentative.toHomologicallyMarkedDiagram by
    unfold TwistedYetter
    exact ConditionalDescent.diffeomorphism_invariant_of_descent_data
      𝒞η
      (fun marked =>
        frozenFrontendRepresentativeIndependence
          𝒞η marked.diagram marked.cut marked.primalBoundary)
      (frozenFrontendLocalMoveInvariance 𝒞η)
      fourSphere fourSphere (identityOrientedDiffeomorphism fourSphere) 0
      chosenExistence.choose chosenExistence.choose_spec
      emptyFourSphereRepresentative
      (by
        rw [inducedH₂_identityOrientedDiffeomorphism]
        exact emptyFourSphereRepresentative_represents_zero)]
  unfold evaluateMarkedDiagram evaluateMarking
  change
    evaluateCycle 𝒞η emptyKirbyDiagram emptyKirbyCut
        emptyKirbyDiagram.primalDegreeThreeBoundaryData
        (Quotient.out emptyFourSphereRepresentative.thamAlpha) =
      𝒞η.category.globalDimension
  rw [frozenFrontendRepresentativeIndependence 𝒞η
    emptyKirbyDiagram emptyKirbyCut
    emptyKirbyDiagram.primalDegreeThreeBoundaryData
    (Quotient.out emptyFourSphereRepresentative.thamAlpha) 0]
  · unfold evaluateCycle thamDefinition511Normalization
    rw [show rawCycleSum 𝒞η emptyKirbyDiagram emptyKirbyCut
        emptyKirbyDiagram.primalDegreeThreeBoundaryData 0 = 1 by
      unfold rawCycleSum
      change
        (∑ labeling : Fin 0 → 𝒞η.category.Simple,
          (∏ handle : Fin 0,
              𝒞η.category.simples.quantumDimension (labeling handle)) *
            1 *
            𝒞η.category.closedScalar
              (compileCutOpenExteriorMorphism 𝒞η.category
                emptyKirbyDiagram emptyKirbyCut labeling)) = 1
      simp [emptyKirby_compile_eq_identity,
        𝒞η.category.closedScalar_identity]]
    simp [emptyKirbyDiagram, emptyKirbyHandleData]
  · have outEq :
        thamCycleClass emptyKirbyDiagram.primalDegreeThreeBoundaryData
            (Quotient.out emptyFourSphereRepresentative.thamAlpha) =
          emptyFourSphereRepresentative.thamAlpha := by
        exact Quotient.out_eq _
    rw [outEq]
    change emptyFourSphereRepresentative.thamAlpha = 0
    change
      (turnoverPoincareDualityEquiv emptyKirbyDiagram
        (specialKirbyDiagram_computesH₂ emptyKirbyDiagram)) 0 = 0
    exact
      (turnoverPoincareDualityEquiv emptyKirbyDiagram
        (specialKirbyDiagram_computesH₂ emptyKirbyDiagram)).map_zero

end

end TwistedYetter.StableNoGo
