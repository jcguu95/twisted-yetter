import TwistedYetter.Kirby.Final.Proofs.SpecialCutMeridian
import TwistedYetter.Kirby.Final.Semantics.Independent.OneTwoLocalReplacement

namespace TwistedYetter.Kirby.Final.Proofs

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

theorem standardOneTwoBirth_eventCount
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.dottedCuts.exterior.eventCount =
      source.dottedCuts.exterior.eventCount + 3 := by
  have lengths :=
    congrArg List.length normalForm.2.2.1
  simp [serializedExteriorEvents, oneTwoLocalEvents] at lengths
  omega

theorem standardOneTwoBirth_componentCount
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.trace.componentCount =
      source.trace.componentCount + 2 := by
  have lengths :=
    congrArg List.length normalForm.1
  simp [serializedComponents, oneTwoLocalComponents] at lengths
  omega

theorem standardOneTwoBirth_strandCount
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.trace.strandCount =
      source.trace.strandCount + 3 := by
  have lengths :=
    congrArg List.length normalForm.2.1
  simp [serializedStrands, oneTwoLocalStrands] at lengths
  omega

theorem standardOneTwoBirth_eventZero
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    serializeCutOpenEvent
        (target.dottedCuts.exterior.events
          ⟨0, by
            rw [standardOneTwoBirth_eventCount normalForm]
            omega⟩) =
      .birth source.trace.strandCount
        (source.trace.strandCount + 1) := by
  have first :=
    congrArg (fun events => events[0]?)
      normalForm.2.2.1
  simp [serializedExteriorEvents, oneTwoLocalEvents] at first
  rcases first with ⟨_positive, first⟩
  simpa using first

def oneTwoFirstStrand
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.trace.StrandId :=
  ⟨source.trace.strandCount, by
    rw [standardOneTwoBirth_strandCount normalForm]
    omega⟩

def oneTwoSecondStrand
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.trace.StrandId :=
  ⟨source.trace.strandCount + 1, by
    rw [standardOneTwoBirth_strandCount normalForm]
    omega⟩

def oneTwoThirdStrand
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.trace.StrandId :=
  ⟨source.trace.strandCount + 2, by
    rw [standardOneTwoBirth_strandCount normalForm]
    omega⟩

theorem standardOneTwoBirth_eventZero_eq
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.dottedCuts.exterior.events
        ⟨0, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ =
      .birth
        (oneTwoFirstStrand normalForm)
        (oneTwoSecondStrand normalForm) := by
  have serialized := standardOneTwoBirth_eventZero normalForm
  generalize event_eq :
      target.dottedCuts.exterior.events
        ⟨0, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ = event at serialized ⊢
  cases event with
  | birth left right =>
      simp [serializeCutOpenEvent] at serialized
      apply congrArg₂ CutOpenEvent.birth
      · exact Fin.ext serialized.1
      · exact Fin.ext serialized.2
  | death left right =>
      simp [serializeCutOpenEvent] at serialized
  | crossing overInput underInput overOutput underOutput sign =>
      simp [serializeCutOpenEvent] at serialized
  | framingTwist input output sign =>
      simp [serializeCutOpenEvent] at serialized
  | planarIsotopy continuations =>
      simp [serializeCutOpenEvent] at serialized
  | projectorHole dotted punctures =>
      simp [serializeCutOpenEvent] at serialized

theorem standardOneTwoBirth_eventOne
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    serializeCutOpenEvent
        (target.dottedCuts.exterior.events
          ⟨1, by
            rw [standardOneTwoBirth_eventCount normalForm]
            omega⟩) =
      .projectorHole source.trace.componentCount
        [oneTwoLocalPuncture source] := by
  have second :=
    congrArg (fun events => events[1]?)
      normalForm.2.2.1
  simp [serializedExteriorEvents, oneTwoLocalEvents] at second
  rcases second with ⟨_positive, second⟩
  simpa using second

theorem standardOneTwoBirth_eventOne_exists
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    ∃ (dotted : target.trace.ComponentId)
      (puncture : DottedPuncture target.trace),
      target.dottedCuts.exterior.events
          ⟨1, by
            rw [standardOneTwoBirth_eventCount normalForm]
            omega⟩ =
        .projectorHole dotted [puncture] ∧
      dotted.1 = source.trace.componentCount ∧
      serializePuncture puncture = oneTwoLocalPuncture source := by
  have serialized := standardOneTwoBirth_eventOne normalForm
  generalize event_eq :
      target.dottedCuts.exterior.events
        ⟨1, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ = event at serialized
  cases event with
  | birth left right =>
      simp [serializeCutOpenEvent] at serialized
  | death left right =>
      simp [serializeCutOpenEvent] at serialized
  | crossing overInput underInput overOutput underOutput sign =>
      simp [serializeCutOpenEvent] at serialized
  | framingTwist input output sign =>
      simp [serializeCutOpenEvent] at serialized
  | planarIsotopy continuations =>
      simp [serializeCutOpenEvent] at serialized
  | projectorHole dotted punctures =>
      simp [serializeCutOpenEvent] at serialized
      rcases serialized with ⟨dotted_eq, punctures_eq⟩
      cases punctures with
      | nil =>
          simp at punctures_eq
      | cons puncture rest =>
          simp at punctures_eq
          rcases punctures_eq with ⟨rest_eq, puncture_eq⟩
          have rest_nil : rest = [] := by
            simpa using rest_eq
          subst rest
          refine ⟨dotted, puncture, rfl, dotted_eq, ?_⟩
          exact puncture_eq

theorem standardOneTwoBirth_eventTwo
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    serializeCutOpenEvent
        (target.dottedCuts.exterior.events
          ⟨2, by
            rw [standardOneTwoBirth_eventCount normalForm]
            omega⟩) =
      .death (source.trace.strandCount + 2)
        (source.trace.strandCount + 1) := by
  have third :=
    congrArg (fun events => events[2]?)
      normalForm.2.2.1
  simp [serializedExteriorEvents, oneTwoLocalEvents] at third
  rcases third with ⟨_positive, third⟩
  simpa using third

theorem standardOneTwoBirth_eventTwo_eq
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.dottedCuts.exterior.events
        ⟨2, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ =
      .death
        (oneTwoThirdStrand normalForm)
        (oneTwoSecondStrand normalForm) := by
  have serialized := standardOneTwoBirth_eventTwo normalForm
  generalize event_eq :
      target.dottedCuts.exterior.events
        ⟨2, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ = event at serialized ⊢
  cases event with
  | birth left right =>
      simp [serializeCutOpenEvent] at serialized
  | death left right =>
      simp [serializeCutOpenEvent] at serialized
      apply congrArg₂ CutOpenEvent.death
      · exact Fin.ext serialized.1
      · exact Fin.ext serialized.2
  | crossing overInput underInput overOutput underOutput sign =>
      simp [serializeCutOpenEvent] at serialized
  | framingTwist input output sign =>
      simp [serializeCutOpenEvent] at serialized
  | planarIsotopy continuations =>
      simp [serializeCutOpenEvent] at serialized
  | projectorHole dotted punctures =>
      simp [serializeCutOpenEvent] at serialized

theorem standardOneTwoBirth_firstStrandData
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    serializeStrand
        (target.trace.strands (oneTwoFirstStrand normalForm)) =
      {
        component := source.trace.componentCount + 1
        orientation := .positive
      } := by
  have atIndex :=
    congrArg (fun strands => strands[source.trace.strandCount]?)
      normalForm.2.1
  simp [serializedStrands, oneTwoLocalStrands,
    oneTwoFirstStrand] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  simpa using atIndex

theorem standardOneTwoBirth_secondStrandData
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    serializeStrand
        (target.trace.strands (oneTwoSecondStrand normalForm)) =
      {
        component := source.trace.componentCount + 1
        orientation := .negative
      } := by
  have atIndex :=
    congrArg (fun strands => strands[source.trace.strandCount + 1]?)
      normalForm.2.1
  simp [serializedStrands, oneTwoLocalStrands,
    oneTwoSecondStrand] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  simpa using atIndex

theorem standardOneTwoBirth_thirdStrandData
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    serializeStrand
        (target.trace.strands (oneTwoThirdStrand normalForm)) =
      {
        component := source.trace.componentCount + 1
        orientation := .positive
      } := by
  have atIndex :=
    congrArg (fun strands => strands[source.trace.strandCount + 2]?)
      normalForm.2.1
  simp [serializedStrands, oneTwoLocalStrands,
    oneTwoThirdStrand] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  simpa using atIndex

theorem standardOneTwoBirth_activeOrderZero
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.dottedCuts.exterior.activeOrder
        ⟨0, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ = [] := by
  have atIndex :=
    congrArg (fun orders => orders[0]?)
      normalForm.2.2.2.1
  simp [serializedActiveOrders, oneTwoLocalActiveOrders] at atIndex
  simpa using atIndex

theorem standardOneTwoBirth_activeOrderOne
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.dottedCuts.exterior.activeOrder
        ⟨1, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ =
      [oneTwoFirstStrand normalForm,
        oneTwoSecondStrand normalForm] := by
  have atIndex :=
    congrArg (fun orders => orders[1]?)
      normalForm.2.2.2.1
  simp [serializedActiveOrders, oneTwoLocalActiveOrders] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  change
    List.map Fin.val
        (target.dottedCuts.exterior.activeOrder
          ⟨1, by
            rw [standardOneTwoBirth_eventCount normalForm]
            omega⟩) =
      List.map Fin.val
        [oneTwoFirstStrand normalForm,
          oneTwoSecondStrand normalForm] at atIndex
  exact (List.map_injective_iff.mpr Fin.val_injective) atIndex

theorem standardOneTwoBirth_activeOrderTwo
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.dottedCuts.exterior.activeOrder
        ⟨2, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ =
      [oneTwoThirdStrand normalForm,
        oneTwoSecondStrand normalForm] := by
  have atIndex :=
    congrArg (fun orders => orders[2]?)
      normalForm.2.2.2.1
  simp [serializedActiveOrders, oneTwoLocalActiveOrders] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  change
    List.map Fin.val
        (target.dottedCuts.exterior.activeOrder
          ⟨2, by
            rw [standardOneTwoBirth_eventCount normalForm]
            omega⟩) =
      List.map Fin.val
        [oneTwoThirdStrand normalForm,
          oneTwoSecondStrand normalForm] at atIndex
  exact (List.map_injective_iff.mpr Fin.val_injective) atIndex

theorem standardOneTwoBirth_activeOrderThree
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    target.dottedCuts.exterior.activeOrder
        ⟨3, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ = [] := by
  have atIndex :=
    congrArg (fun orders => orders[3]?)
      normalForm.2.2.2.1
  simp [serializedActiveOrders, oneTwoLocalActiveOrders,
    source.dottedCuts.exterior.initialBoundaryEmpty] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  change
    List.map Fin.val
        (target.dottedCuts.exterior.activeOrder
          ⟨3, by
            rw [standardOneTwoBirth_eventCount normalForm]
            omega⟩) =
      List.map Fin.val [] at atIndex
  exact (List.map_injective_iff.mpr Fin.val_injective) atIndex

theorem standardOneTwoBirth_first_second_component
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    (target.trace.strands
        (oneTwoFirstStrand normalForm)).component =
      (target.trace.strands
        (oneTwoSecondStrand normalForm)).component := by
  have first :=
    congrArg SerializedStrand.component
      (standardOneTwoBirth_firstStrandData normalForm)
  have second :=
    congrArg SerializedStrand.component
      (standardOneTwoBirth_secondStrandData normalForm)
  exact Fin.ext (by
    simpa [serializeStrand] using first.trans second.symm)

theorem standardOneTwoBirth_first_second_orientation
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    (target.trace.strands
        (oneTwoFirstStrand normalForm)).orientation ≠
      (target.trace.strands
        (oneTwoSecondStrand normalForm)).orientation := by
  have first :=
    congrArg SerializedStrand.orientation
      (standardOneTwoBirth_firstStrandData normalForm)
  have second :=
    congrArg SerializedStrand.orientation
      (standardOneTwoBirth_secondStrandData normalForm)
  simp [serializeStrand] at first second
  rw [first, second]
  decide

theorem standardOneTwoBirth_third_second_component
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    (target.trace.strands
        (oneTwoThirdStrand normalForm)).component =
      (target.trace.strands
        (oneTwoSecondStrand normalForm)).component := by
  have third :=
    congrArg SerializedStrand.component
      (standardOneTwoBirth_thirdStrandData normalForm)
  have second :=
    congrArg SerializedStrand.component
      (standardOneTwoBirth_secondStrandData normalForm)
  exact Fin.ext (by
    simpa [serializeStrand] using third.trans second.symm)

theorem standardOneTwoBirth_third_second_orientation
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    (target.trace.strands
        (oneTwoThirdStrand normalForm)).orientation ≠
      (target.trace.strands
        (oneTwoSecondStrand normalForm)).orientation := by
  have third :=
    congrArg SerializedStrand.orientation
      (standardOneTwoBirth_thirdStrandData normalForm)
  have second :=
    congrArg SerializedStrand.orientation
      (standardOneTwoBirth_secondStrandData normalForm)
  simp [serializeStrand] at third second
  rw [third, second]
  decide

def oneTwoEventIndexZero
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    Fin target.dottedCuts.exterior.eventCount :=
  ⟨0, by
    rw [standardOneTwoBirth_eventCount normalForm]
    omega⟩

theorem standardOneTwoBirth_firstContextsEmpty
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    eventLeftContext target (oneTwoEventIndexZero normalForm) = [] ∧
      eventRightContext target (oneTwoEventIndexZero normalForm) = [] := by
  let i := oneTwoEventIndexZero normalForm
  have eventEq :
      target.dottedCuts.exterior.events i =
        .birth
          (oneTwoFirstStrand normalForm)
          (oneTwoSecondStrand normalForm) := by
    simpa [i, oneTwoEventIndexZero] using
      standardOneTwoBirth_eventZero_eq normalForm
  have beforeEq :
      target.dottedCuts.exterior.activeOrder i.castSucc = [] := by
    simpa [i, oneTwoEventIndexZero] using
      standardOneTwoBirth_activeOrderZero normalForm
  have transition := (eventTransitionEquations target i).1
  rw [beforeEq] at transition
  have eventBefore :
      (target.dottedCuts.exterior.events i).beforeWord = [] := by
    rw [eventEq]
    rfl
  rw [eventBefore] at transition
  simp at transition
  exact transition

noncomputable def compileContextualCutOpenEventMorphismFromWitness
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : CutOpenEvent diagram.trace)
    (before after left right : List diagram.trace.StrandId)
    (beforeEq : before = left ++ event.beforeWord ++ right)
    (afterEq : after = left ++ event.afterWord ++ right)
    (pairing : event.StrandContinuationsAreWellFormed) :
    ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling before) ⟶
      ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling after) := by
  have beforeObjectEq :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling word))
      beforeEq
  have afterObjectEq :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling word))
      afterEq
  have beforeContextObjectEq :
      ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling
            (left ++ event.beforeWord ++ right)) =
        ribbonWordObject 𝒞
          (List.append
            (List.append
              (exteriorWord 𝒞 diagram labeling left)
              (exteriorWord 𝒞 diagram labeling event.beforeWord))
            (exteriorWord 𝒞 diagram labeling right)) := by
    simp [exteriorWord, List.map_append]
  have afterContextObjectEq :
      ribbonWordObject 𝒞
          (exteriorWord 𝒞 diagram labeling
            (left ++ event.afterWord ++ right)) =
        ribbonWordObject 𝒞
          (List.append
            (List.append
              (exteriorWord 𝒞 diagram labeling left)
              (exteriorWord 𝒞 diagram labeling event.afterWord))
            (exteriorWord 𝒞 diagram labeling right)) := by
    simp [exteriorWord, List.map_append]
  exact
    eqToHom beforeObjectEq ≫
      eqToHom beforeContextObjectEq ≫
      contextualizeRibbonMorphism 𝒞
        (exteriorWord 𝒞 diagram labeling left)
        (exteriorWord 𝒞 diagram labeling event.beforeWord)
        (exteriorWord 𝒞 diagram labeling event.afterWord)
        (exteriorWord 𝒞 diagram labeling right)
        (compileCutOpenEventMorphism 𝒞 diagram labeling event pairing) ≫
      eqToHom afterContextObjectEq.symm ≫
      eqToHom afterObjectEq.symm

theorem compileContextualCutOpenEventMorphism_eq_fromWitness
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (i : Fin diagram.dottedCuts.exterior.eventCount) :
    compileContextualCutOpenEventMorphism 𝒞 diagram labeling i =
      compileContextualCutOpenEventMorphismFromWitness 𝒞 diagram labeling
        (diagram.dottedCuts.exterior.events i)
        (diagram.dottedCuts.exterior.activeOrder i.castSucc)
        (diagram.dottedCuts.exterior.activeOrder i.succ)
        (eventLeftContext diagram i)
        (eventRightContext diagram i)
        (eventTransitionEquations diagram i).1
        (eventTransitionEquations diagram i).2
        (diagram.dottedCuts.exterior.strandContinuationsAreWellFormed i) := by
  rfl

theorem compileContextualFromWitness_birth
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (leftOutput rightOutput : diagram.trace.StrandId)
    (before after left right : List diagram.trace.StrandId)
    (beforeEq :
      before =
        left ++
          (CutOpenEvent.birth leftOutput rightOutput).beforeWord ++
          right)
    (afterEq :
      after =
        left ++
          (CutOpenEvent.birth leftOutput rightOutput).afterWord ++
          right)
    (pairing :
      (CutOpenEvent.birth leftOutput rightOutput).StrandContinuationsAreWellFormed)
    (beforeEmpty : before = [])
    (afterCanonical : after = [leftOutput, rightOutput])
    (leftEmpty : left = [])
    (rightEmpty : right = []) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          beforeEmpty).symm ≫
      compileContextualCutOpenEventMorphismFromWitness
        𝒞 diagram labeling
        (.birth leftOutput rightOutput)
        before after left right beforeEq afterEq pairing ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          afterCanonical) =
      pairedBirthMorphism 𝒞 diagram labeling
        leftOutput rightOutput pairing.1 pairing.2 := by
  subst before
  subst after
  subst left
  subst right
  have beforeEmptyCanonical :
      beforeEmpty =
        (rfl : ([] : List diagram.trace.StrandId) = []) :=
    Subsingleton.elim _ _
  have afterCanonicalCanonical :
      afterCanonical =
        (rfl :
          ([leftOutput, rightOutput] :
              List diagram.trace.StrandId) =
            [leftOutput, rightOutput]) :=
    Subsingleton.elim _ _
  cases beforeEmptyCanonical
  cases afterCanonicalCanonical
  unfold compileContextualCutOpenEventMorphismFromWitness
  dsimp only
  simp [CutOpenEvent.beforeWord, CutOpenEvent.afterWord,
    exteriorWord, ribbonWordObject, contextualizeRibbonMorphism,
    compileCutOpenEventMorphism, ribbonWordAppendIso]
  monoidal

theorem compileContextualFromWitness_eq_birth
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : CutOpenEvent diagram.trace)
    (leftOutput rightOutput : diagram.trace.StrandId)
    (before after left right : List diagram.trace.StrandId)
    (beforeEq : before = left ++ event.beforeWord ++ right)
    (afterEq : after = left ++ event.afterWord ++ right)
    (pairing : event.StrandContinuationsAreWellFormed)
    (eventCanonical : event = .birth leftOutput rightOutput)
    (beforeEmpty : before = [])
    (afterCanonical : after = [leftOutput, rightOutput])
    (leftEmpty : left = [])
    (rightEmpty : right = []) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          beforeEmpty).symm ≫
      compileContextualCutOpenEventMorphismFromWitness
        𝒞 diagram labeling event
        before after left right beforeEq afterEq pairing ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          afterCanonical) =
      pairedBirthMorphism 𝒞 diagram labeling
        leftOutput rightOutput
        (eventCanonical ▸ pairing).1
        (eventCanonical ▸ pairing).2 := by
  subst event
  exact compileContextualFromWitness_birth
    𝒞 diagram labeling leftOutput rightOutput
      before after left right beforeEq afterEq pairing
      beforeEmpty afterCanonical leftEmpty rightEmpty

theorem standardOneTwoBirth_firstContextualEdge
    (𝒞 : PremodularFusionCategory K)
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target)
    (labeling : TwoHandleLabeling 𝒞 target) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardOneTwoBirth_activeOrderZero normalForm)).symm ≫
      compileContextualCutOpenEventMorphism 𝒞 target labeling
        (oneTwoEventIndexZero normalForm) ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardOneTwoBirth_activeOrderOne normalForm)) =
      pairedBirthMorphism 𝒞 target labeling
        (oneTwoFirstStrand normalForm)
        (oneTwoSecondStrand normalForm)
        (standardOneTwoBirth_first_second_component normalForm)
        (standardOneTwoBirth_first_second_orientation normalForm) := by
  let i := oneTwoEventIndexZero normalForm
  have eventEq :
      target.dottedCuts.exterior.events i =
        .birth
          (oneTwoFirstStrand normalForm)
          (oneTwoSecondStrand normalForm) := by
    simpa [i, oneTwoEventIndexZero] using
      standardOneTwoBirth_eventZero_eq normalForm
  have beforeEq :
      target.dottedCuts.exterior.activeOrder i.castSucc = [] := by
    simpa [i, oneTwoEventIndexZero] using
      standardOneTwoBirth_activeOrderZero normalForm
  have afterEq :
      target.dottedCuts.exterior.activeOrder i.succ =
        [oneTwoFirstStrand normalForm,
          oneTwoSecondStrand normalForm] := by
    simpa [i, oneTwoEventIndexZero] using
      standardOneTwoBirth_activeOrderOne normalForm
  have contexts :=
    standardOneTwoBirth_firstContextsEmpty normalForm
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  simpa using
    (compileContextualFromWitness_eq_birth
      𝒞 target labeling
      (target.dottedCuts.exterior.events i)
      (oneTwoFirstStrand normalForm)
      (oneTwoSecondStrand normalForm)
      (target.dottedCuts.exterior.activeOrder i.castSucc)
      (target.dottedCuts.exterior.activeOrder i.succ)
      (eventLeftContext target i)
      (eventRightContext target i)
      (eventTransitionEquations target i).1
      (eventTransitionEquations target i).2
      (target.dottedCuts.exterior.strandContinuationsAreWellFormed i)
      eventEq beforeEq afterEq contexts.1 contexts.2)

theorem compileContextualFromWitness_death
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (leftInput rightInput : diagram.trace.StrandId)
    (before after left right : List diagram.trace.StrandId)
    (beforeEq :
      before =
        left ++
          (CutOpenEvent.death leftInput rightInput).beforeWord ++
          right)
    (afterEq :
      after =
        left ++
          (CutOpenEvent.death leftInput rightInput).afterWord ++
          right)
    (pairing :
      (CutOpenEvent.death leftInput rightInput).StrandContinuationsAreWellFormed)
    (beforeCanonical : before = [leftInput, rightInput])
    (afterEmpty : after = [])
    (leftEmpty : left = [])
    (rightEmpty : right = []) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          beforeCanonical).symm ≫
      compileContextualCutOpenEventMorphismFromWitness
        𝒞 diagram labeling
        (.death leftInput rightInput)
        before after left right beforeEq afterEq pairing ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          afterEmpty) =
      pairedDeathMorphism 𝒞 diagram labeling
        leftInput rightInput pairing.1 pairing.2 := by
  subst before
  subst after
  subst left
  subst right
  have beforeCanonicalProof :
      beforeCanonical =
        (rfl :
          ([leftInput, rightInput] :
              List diagram.trace.StrandId) =
            [leftInput, rightInput]) :=
    Subsingleton.elim _ _
  have afterEmptyProof :
      afterEmpty =
        (rfl : ([] : List diagram.trace.StrandId) = []) :=
    Subsingleton.elim _ _
  cases beforeCanonicalProof
  cases afterEmptyProof
  unfold compileContextualCutOpenEventMorphismFromWitness
  dsimp only
  simp [CutOpenEvent.beforeWord, CutOpenEvent.afterWord,
    exteriorWord, ribbonWordObject, contextualizeRibbonMorphism,
    compileCutOpenEventMorphism, ribbonWordAppendIso]
  monoidal

theorem compileContextualFromWitness_eq_death
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : CutOpenEvent diagram.trace)
    (leftInput rightInput : diagram.trace.StrandId)
    (before after left right : List diagram.trace.StrandId)
    (beforeEq : before = left ++ event.beforeWord ++ right)
    (afterEq : after = left ++ event.afterWord ++ right)
    (pairing : event.StrandContinuationsAreWellFormed)
    (eventCanonical : event = .death leftInput rightInput)
    (beforeCanonical : before = [leftInput, rightInput])
    (afterEmpty : after = [])
    (leftEmpty : left = [])
    (rightEmpty : right = []) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          beforeCanonical).symm ≫
      compileContextualCutOpenEventMorphismFromWitness
        𝒞 diagram labeling event
        before after left right beforeEq afterEq pairing ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          afterEmpty) =
      pairedDeathMorphism 𝒞 diagram labeling
        leftInput rightInput
        (eventCanonical ▸ pairing).1
        (eventCanonical ▸ pairing).2 := by
  subst event
  exact compileContextualFromWitness_death
    𝒞 diagram labeling leftInput rightInput
    before after left right beforeEq afterEq pairing
    beforeCanonical afterEmpty leftEmpty rightEmpty

theorem oneTwoPuncture_input_eq
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target)
    (puncture : DottedPuncture target.trace)
    (serialized :
      serializePuncture puncture = oneTwoLocalPuncture source) :
    puncture.inputStrand = oneTwoFirstStrand normalForm := by
  exact Fin.ext (by
    simpa [serializePuncture, oneTwoLocalPuncture,
      oneTwoFirstStrand] using
      congrArg SerializedPuncture.inputStrand serialized)

theorem oneTwoPuncture_output_eq
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target)
    (puncture : DottedPuncture target.trace)
    (serialized :
      serializePuncture puncture = oneTwoLocalPuncture source) :
    puncture.outputStrand = oneTwoThirdStrand normalForm := by
  exact Fin.ext (by
    simpa [serializePuncture, oneTwoLocalPuncture,
      oneTwoThirdStrand] using
      congrArg SerializedPuncture.outputStrand serialized)

theorem standardOneTwoBirth_secondContexts
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target)
    (dotted : target.trace.ComponentId)
    (puncture : DottedPuncture target.trace)
    (eventEq :
      target.dottedCuts.exterior.events
          ⟨1, by
            rw [standardOneTwoBirth_eventCount normalForm]
            omega⟩ =
        .projectorHole dotted [puncture])
    (serialized :
      serializePuncture puncture = oneTwoLocalPuncture source) :
    eventLeftContext target
        ⟨1, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ = [] ∧
      eventRightContext target
        ⟨1, by
          rw [standardOneTwoBirth_eventCount normalForm]
          omega⟩ =
        [oneTwoSecondStrand normalForm] := by
  let i : Fin target.dottedCuts.exterior.eventCount :=
    ⟨1, by
      rw [standardOneTwoBirth_eventCount normalForm]
      omega⟩
  let left := eventLeftContext target i
  let right := eventRightContext target i
  have inputEq :=
    oneTwoPuncture_input_eq normalForm puncture serialized
  have beforeTransition := (eventTransitionEquations target i).1
  have activeBefore :
      target.dottedCuts.exterior.activeOrder i.castSucc =
        [oneTwoFirstStrand normalForm,
          oneTwoSecondStrand normalForm] := by
    simpa [i] using standardOneTwoBirth_activeOrderOne normalForm
  rw [activeBefore] at beforeTransition
  have eventAt :
      target.dottedCuts.exterior.events i =
        .projectorHole dotted [puncture] := by
    simpa [i] using eventEq
  have eventBefore :
      (target.dottedCuts.exterior.events i).beforeWord =
        [oneTwoFirstStrand normalForm] := by
    rw [eventAt]
    exact congrArg (fun strand => [strand]) inputEq
  rw [eventBefore] at beforeTransition
  change
    [oneTwoFirstStrand normalForm,
        oneTwoSecondStrand normalForm] =
      left ++ [oneTwoFirstStrand normalForm] ++ right
    at beforeTransition
  have lengthEquation :
      left.length + right.length = 1 := by
    have lengths := congrArg List.length beforeTransition
    simp at lengths
    omega
  by_cases leftEmpty : left = []
  · rw [leftEmpty] at beforeTransition
    simp at beforeTransition
    exact
      ⟨by simpa [left] using leftEmpty,
        by simpa [right] using beforeTransition.symm⟩
  · have leftPositive : 0 < left.length :=
      List.length_pos_of_ne_nil leftEmpty
    have rightLengthZero : right.length = 0 := by
      omega
    have rightEmpty : right = [] :=
      List.eq_nil_of_length_eq_zero rightLengthZero
    obtain ⟨only, tail, leftShape⟩ :=
      List.exists_cons_of_ne_nil leftEmpty
    have tailLengthZero : tail.length = 0 := by
      rw [leftShape] at lengthEquation
      simp at lengthEquation
      omega
    have tailEmpty : tail = [] :=
      List.eq_nil_of_length_eq_zero tailLengthZero
    rw [leftShape, tailEmpty, rightEmpty] at beforeTransition
    have impossible :
        oneTwoSecondStrand normalForm =
          oneTwoFirstStrand normalForm :=
      (List.cons.inj (List.cons.inj beforeTransition).2).1
    have values := congrArg Fin.val impossible
    simp [oneTwoFirstStrand, oneTwoSecondStrand] at values

def oneTwoEventIndexOne
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    Fin target.dottedCuts.exterior.eventCount :=
  ⟨1, by
    rw [standardOneTwoBirth_eventCount normalForm]
    omega⟩

def oneTwoEventIndexTwo
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    Fin target.dottedCuts.exterior.eventCount :=
  ⟨2, by
    rw [standardOneTwoBirth_eventCount normalForm]
    omega⟩

theorem standardOneTwoBirth_thirdContextsEmpty
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target) :
    eventLeftContext target (oneTwoEventIndexTwo normalForm) = [] ∧
      eventRightContext target (oneTwoEventIndexTwo normalForm) = [] := by
  let i := oneTwoEventIndexTwo normalForm
  have eventEq :
      target.dottedCuts.exterior.events i =
        .death
          (oneTwoThirdStrand normalForm)
          (oneTwoSecondStrand normalForm) := by
    simpa [i, oneTwoEventIndexTwo] using
      standardOneTwoBirth_eventTwo_eq normalForm
  have afterEq :
      target.dottedCuts.exterior.activeOrder i.succ = [] := by
    simpa [i, oneTwoEventIndexTwo] using
      standardOneTwoBirth_activeOrderThree normalForm
  have transition := (eventTransitionEquations target i).2
  rw [afterEq, eventEq] at transition
  simp [CutOpenEvent.afterWord] at transition
  exact transition

theorem standardOneTwoBirth_thirdContextualEdge
    (𝒞 : PremodularFusionCategory K)
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target)
    (labeling : TwoHandleLabeling 𝒞 target) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardOneTwoBirth_activeOrderTwo normalForm)).symm ≫
      compileContextualCutOpenEventMorphism 𝒞 target labeling
        (oneTwoEventIndexTwo normalForm) ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardOneTwoBirth_activeOrderThree normalForm)) =
      pairedDeathMorphism 𝒞 target labeling
        (oneTwoThirdStrand normalForm)
        (oneTwoSecondStrand normalForm)
        (standardOneTwoBirth_third_second_component normalForm)
        (standardOneTwoBirth_third_second_orientation normalForm) := by
  let i := oneTwoEventIndexTwo normalForm
  have eventEq :
      target.dottedCuts.exterior.events i =
        .death
          (oneTwoThirdStrand normalForm)
          (oneTwoSecondStrand normalForm) := by
    simpa [i, oneTwoEventIndexTwo] using
      standardOneTwoBirth_eventTwo_eq normalForm
  have beforeEq :
      target.dottedCuts.exterior.activeOrder i.castSucc =
        [oneTwoThirdStrand normalForm,
          oneTwoSecondStrand normalForm] := by
    simpa [i, oneTwoEventIndexTwo] using
      standardOneTwoBirth_activeOrderTwo normalForm
  have afterEq :
      target.dottedCuts.exterior.activeOrder i.succ = [] := by
    simpa [i, oneTwoEventIndexTwo] using
      standardOneTwoBirth_activeOrderThree normalForm
  have contexts :=
    standardOneTwoBirth_thirdContextsEmpty normalForm
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  simpa using
    (compileContextualFromWitness_eq_death
      𝒞 target labeling
      (target.dottedCuts.exterior.events i)
      (oneTwoThirdStrand normalForm)
      (oneTwoSecondStrand normalForm)
      (target.dottedCuts.exterior.activeOrder i.castSucc)
      (target.dottedCuts.exterior.activeOrder i.succ)
      (eventLeftContext target i)
      (eventRightContext target i)
      (eventTransitionEquations target i).1
      (eventTransitionEquations target i).2
      (target.dottedCuts.exterior.strandContinuationsAreWellFormed i)
      eventEq beforeEq afterEq contexts.1 contexts.2)

theorem compileContextualFromWitness_projector
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (dotted : diagram.trace.ComponentId)
    (puncture : DottedPuncture diagram.trace)
    (first second third : diagram.trace.StrandId)
    (before after left right : List diagram.trace.StrandId)
    (beforeEq :
      before =
        left ++
          (CutOpenEvent.projectorHole dotted [puncture]).beforeWord ++
          right)
    (afterEq :
      after =
        left ++
          (CutOpenEvent.projectorHole dotted [puncture]).afterWord ++
          right)
    (pairing :
      (CutOpenEvent.projectorHole dotted [puncture]).StrandContinuationsAreWellFormed)
    (beforeCanonical : before = [first, second])
    (afterCanonical : after = [third, second])
    (leftEmpty : left = [])
    (rightCanonical : right = [second])
    (inputCanonical : puncture.inputStrand = first)
    (outputCanonical : puncture.outputStrand = third) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          beforeCanonical).symm ≫
      compileContextualCutOpenEventMorphismFromWitness
        𝒞 diagram labeling
        (.projectorHole dotted [puncture])
        before after left right beforeEq afterEq pairing ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          afterCanonical) =
      eqToHom
          (congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 diagram labeling word))
            (congrArg
              (fun strand => [strand, second])
              inputCanonical.symm)) ≫
        contextualizeRibbonMorphism 𝒞
          []
          (exteriorWord 𝒞 diagram labeling
            [puncture.inputStrand])
          (exteriorWord 𝒞 diagram labeling
            [puncture.outputStrand])
          (exteriorWord 𝒞 diagram labeling [second])
          (compileCutOpenEventMorphism
            𝒞 diagram labeling
            (.projectorHole dotted [puncture]) pairing) ≫
        eqToHom
          (congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 diagram labeling word))
            (congrArg
              (fun strand => [strand, second])
              outputCanonical)) := by
  subst left
  subst right
  subst first
  subst third
  cases beforeCanonical
  cases afterCanonical
  unfold compileContextualCutOpenEventMorphismFromWitness
  dsimp only
  simp [CutOpenEvent.beforeWord, CutOpenEvent.afterWord,
    exteriorWord, ribbonWordObject, contextualizeRibbonMorphism,
    ribbonWordAppendIso]

theorem compileContextualFromWitness_eq_projector
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (event : CutOpenEvent diagram.trace)
    (dotted : diagram.trace.ComponentId)
    (puncture : DottedPuncture diagram.trace)
    (first second third : diagram.trace.StrandId)
    (before after left right : List diagram.trace.StrandId)
    (beforeEq : before = left ++ event.beforeWord ++ right)
    (afterEq : after = left ++ event.afterWord ++ right)
    (pairing : event.StrandContinuationsAreWellFormed)
    (eventCanonical : event = .projectorHole dotted [puncture])
    (beforeCanonical : before = [first, second])
    (afterCanonical : after = [third, second])
    (leftEmpty : left = [])
    (rightCanonical : right = [second])
    (inputCanonical : puncture.inputStrand = first)
    (outputCanonical : puncture.outputStrand = third) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          beforeCanonical).symm ≫
      compileContextualCutOpenEventMorphismFromWitness
        𝒞 diagram labeling event
        before after left right beforeEq afterEq pairing ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 diagram labeling word))
          afterCanonical) =
      eqToHom
          (congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 diagram labeling word))
            (congrArg
              (fun strand => [strand, second])
              inputCanonical.symm)) ≫
        contextualizeRibbonMorphism 𝒞
          []
          (exteriorWord 𝒞 diagram labeling
            [puncture.inputStrand])
          (exteriorWord 𝒞 diagram labeling
            [puncture.outputStrand])
          (exteriorWord 𝒞 diagram labeling [second])
          (compileCutOpenEventMorphism
            𝒞 diagram labeling
            (.projectorHole dotted [puncture])
            (eventCanonical ▸ pairing)) ≫
        eqToHom
          (congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 diagram labeling word))
            (congrArg
              (fun strand => [strand, second])
              outputCanonical)) := by
  subst event
  exact compileContextualFromWitness_projector
    𝒞 diagram labeling dotted puncture first second third
    before after left right beforeEq afterEq pairing
    beforeCanonical afterCanonical leftEmpty rightCanonical
    inputCanonical outputCanonical

theorem standardOneTwoBirth_secondContextualEdge
    (𝒞 : PremodularFusionCategory K)
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target)
    (labeling : TwoHandleLabeling 𝒞 target)
    (dotted : target.trace.ComponentId)
    (puncture : DottedPuncture target.trace)
    (eventEq :
      target.dottedCuts.exterior.events
          (oneTwoEventIndexOne normalForm) =
        .projectorHole dotted [puncture])
    (serialized :
      serializePuncture puncture = oneTwoLocalPuncture source) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardOneTwoBirth_activeOrderOne normalForm)).symm ≫
      compileContextualCutOpenEventMorphism 𝒞 target labeling
        (oneTwoEventIndexOne normalForm) ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardOneTwoBirth_activeOrderTwo normalForm)) =
      eqToHom
          (congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 target labeling word))
            (congrArg
              (fun strand =>
                [strand, oneTwoSecondStrand normalForm])
              (oneTwoPuncture_input_eq
                normalForm puncture serialized).symm)) ≫
        contextualizeRibbonMorphism 𝒞
          []
          (exteriorWord 𝒞 target labeling
            [puncture.inputStrand])
          (exteriorWord 𝒞 target labeling
            [puncture.outputStrand])
          (exteriorWord 𝒞 target labeling
            [oneTwoSecondStrand normalForm])
          (compileCutOpenEventMorphism
            𝒞 target labeling
            (.projectorHole dotted [puncture])
            (eventEq ▸
              target.dottedCuts.exterior.strandContinuationsAreWellFormed
                (oneTwoEventIndexOne normalForm))) ≫
        eqToHom
          (congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 target labeling word))
            (congrArg
              (fun strand =>
                [strand, oneTwoSecondStrand normalForm])
              (oneTwoPuncture_output_eq
                normalForm puncture serialized))) := by
  let i := oneTwoEventIndexOne normalForm
  have contexts :=
    standardOneTwoBirth_secondContexts
      normalForm dotted puncture eventEq serialized
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  simpa [i] using
    (compileContextualFromWitness_eq_projector
      𝒞 target labeling
      (target.dottedCuts.exterior.events i)
      dotted puncture
      (oneTwoFirstStrand normalForm)
      (oneTwoSecondStrand normalForm)
      (oneTwoThirdStrand normalForm)
      (target.dottedCuts.exterior.activeOrder i.castSucc)
      (target.dottedCuts.exterior.activeOrder i.succ)
      (eventLeftContext target i)
      (eventRightContext target i)
      (eventTransitionEquations target i).1
      (eventTransitionEquations target i).2
      (target.dottedCuts.exterior.strandContinuationsAreWellFormed i)
      eventEq
      (standardOneTwoBirth_activeOrderOne normalForm)
      (standardOneTwoBirth_activeOrderTwo normalForm)
      contexts.1 contexts.2
      (oneTwoPuncture_input_eq normalForm puncture serialized)
      (oneTwoPuncture_output_eq normalForm puncture serialized))

def projectorHoleMorphism
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (dotted : diagram.trace.ComponentId)
    (punctures : List (DottedPuncture diagram.trace)) :
    ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (CutOpenEvent.projectorHole dotted punctures).beforeWord) ⟶
      ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (CutOpenEvent.projectorHole dotted punctures).afterWord) := by
  have input_eq :=
    exteriorInputWord_eq_cutBoundaryWord 𝒞 diagram labeling punctures
  have output_eq :=
    exteriorOutputWord_eq_cutBoundaryWord 𝒞 diagram labeling punctures
  simp only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord]
  exact
    eqToHom (congrArg (ribbonWordObject 𝒞) input_eq) ≫
      tensorUnitProjector 𝒞
        (ribbonWordObject 𝒞
          (cutBoundaryWord 𝒞 diagram labeling punctures)) ≫
      eqToHom (congrArg (ribbonWordObject 𝒞) output_eq.symm)

theorem compileCutOpenEventMorphism_projectorHole
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (dotted : diagram.trace.ComponentId)
    (punctures : List (DottedPuncture diagram.trace))
    (pairing :
      (CutOpenEvent.projectorHole dotted punctures).StrandContinuationsAreWellFormed) :
    compileCutOpenEventMorphism 𝒞 diagram labeling
        (.projectorHole dotted punctures) pairing =
      projectorHoleMorphism 𝒞 diagram labeling dotted punctures := by
  unfold compileCutOpenEventMorphism projectorHoleMorphism
  simp only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord, id_eq]

theorem canonicalBirthProjectorDeathMorphism
    (𝒞 : PremodularFusionCategory K)
    (simple : 𝒞.simples.Simple) :
    canonicalPositiveNegativeBirth 𝒞 simple ≫
        contextualizeRibbonMorphism 𝒞
          []
          [{ label := simple, direction := .forward }]
          [{ label := simple, direction := .forward }]
          [{ label := simple, direction := .dual }]
          (tensorUnitProjector 𝒞
              (𝒞.simples.simpleObject simple) ⊗ₘ
            𝟙 (𝟙_ 𝒞.C)) ≫
        canonicalPositiveNegativeDeath 𝒞 simple =
      specialCutMeridianMorphismWithoutExplicitTwist 𝒞 simple := by
  unfold canonicalPositiveNegativeBirth canonicalPositiveNegativeDeath
  unfold contextualizeRibbonMorphism
  unfold specialCutMeridianMorphismWithoutExplicitTwist
  simp only [ribbonWordObject, orientedSimpleObject]
  dsimp [ribbonWordAppendIso]
  monoidal

theorem contextualizeRibbonMorphism_heq
    (𝒞 : PremodularFusionCategory K)
    {left before after right left' before' after' right' : RibbonWord 𝒞}
    {map :
      ribbonWordObject 𝒞 before ⟶ ribbonWordObject 𝒞 after}
    {map' :
      ribbonWordObject 𝒞 before' ⟶ ribbonWordObject 𝒞 after'}
    (leftEq : left = left')
    (beforeEq : before = before')
    (afterEq : after = after')
    (rightEq : right = right')
    (mapEq : HEq map map') :
    HEq
      (contextualizeRibbonMorphism 𝒞 left before after right map)
      (contextualizeRibbonMorphism 𝒞 left' before' after' right' map') := by
  subst left'
  subst before'
  subst after'
  subst right'
  cases mapEq
  rfl

theorem transportedCanonicalBirthProjectorDeathMorphism
    (𝒞 : PremodularFusionCategory K)
    (simple : 𝒞.simples.Simple)
    (before after right : RibbonWord 𝒞)
    (beforeCanonical :
      before = [{ label := simple, direction := .forward }])
    (afterCanonical :
      after = [{ label := simple, direction := .forward }])
    (rightCanonical :
      right = [{ label := simple, direction := .dual }])
    (beforeAfter : before = after)
    (birthBinding :
      positiveNegativeDualPairWord 𝒞 simple =
        List.append before right)
    (deathBinding :
      List.append after right =
        positiveNegativeDualPairWord 𝒞 simple) :
    canonicalPositiveNegativeBirth 𝒞 simple ≫
        eqToHom (congrArg (ribbonWordObject 𝒞) birthBinding) ≫
        contextualizeRibbonMorphism 𝒞
          [] before after right
          (tensorUnitProjector 𝒞
              (ribbonWordObject 𝒞 before) ≫
            eqToHom
              (congrArg (ribbonWordObject 𝒞) beforeAfter)) ≫
        eqToHom (congrArg (ribbonWordObject 𝒞) deathBinding) ≫
        canonicalPositiveNegativeDeath 𝒞 simple ≍
      specialCutMeridianMorphismWithoutExplicitTwist 𝒞 simple := by
  let canonicalBefore : RibbonWord 𝒞 :=
    [{ label := simple, direction := .forward }]
  let canonicalRight : RibbonWord 𝒞 :=
    [{ label := simple, direction := .dual }]
  have projectorHEq :
      HEq
        (tensorUnitProjector 𝒞 (ribbonWordObject 𝒞 before) ≫
          eqToHom (congrArg (ribbonWordObject 𝒞) beforeAfter))
        (tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) ⊗ₘ
          𝟙 (𝟙_ 𝒞.C)) := by
    have dropTransport :
        HEq
          (tensorUnitProjector 𝒞 (ribbonWordObject 𝒞 before) ≫
            eqToHom (congrArg (ribbonWordObject 𝒞) beforeAfter))
          (tensorUnitProjector 𝒞 (ribbonWordObject 𝒞 before)) :=
      comp_eqToHom_heq _ _
    have changeWord :
        HEq
          (tensorUnitProjector 𝒞 (ribbonWordObject 𝒞 before))
          (tensorUnitProjector 𝒞
            (ribbonWordObject 𝒞 canonicalBefore)) := by
      subst before
      rfl
    exact dropTransport.trans
      (changeWord.trans
        (heq_of_eq
          (tensorUnitProjector_singleton_forward_word 𝒞 simple)))
  have contextHEq :
      HEq
        (contextualizeRibbonMorphism 𝒞 [] before after right
          (tensorUnitProjector 𝒞 (ribbonWordObject 𝒞 before) ≫
            eqToHom (congrArg (ribbonWordObject 𝒞) beforeAfter)))
        (contextualizeRibbonMorphism 𝒞
          [] canonicalBefore canonicalBefore canonicalRight
          (tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) ⊗ₘ
            𝟙 (𝟙_ 𝒞.C))) :=
    contextualizeRibbonMorphism_heq 𝒞
      rfl beforeCanonical afterCanonical rightCanonical projectorHEq
  have birthHEq :
      HEq
        (canonicalPositiveNegativeBirth 𝒞 simple ≫
          eqToHom (congrArg (ribbonWordObject 𝒞) birthBinding))
        (canonicalPositiveNegativeBirth 𝒞 simple) :=
    comp_eqToHom_heq _ _
  have deathHEq :
      HEq
        (eqToHom (congrArg (ribbonWordObject 𝒞) deathBinding) ≫
          canonicalPositiveNegativeDeath 𝒞 simple)
        (canonicalPositiveNegativeDeath 𝒞 simple) :=
    eqToHom_comp_heq _ _
  have birthContextHEq :=
    CategoryTheory.heq_comp
      rfl
      (congrArg (ribbonWordObject 𝒞) birthBinding.symm)
      (congrArg (ribbonWordObject 𝒞) deathBinding)
      birthHEq contextHEq
  let canonicalComposite :
      ribbonWordObject 𝒞 ([] : RibbonWord 𝒞) ⟶
        ribbonWordObject 𝒞 ([] : RibbonWord 𝒞) :=
    (canonicalPositiveNegativeBirth 𝒞 simple ≫
      contextualizeRibbonMorphism 𝒞
        [] canonicalBefore canonicalBefore canonicalRight
        (tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) ⊗ₘ
          𝟙 (𝟙_ 𝒞.C))) ≫
      canonicalPositiveNegativeDeath 𝒞 simple
  have wholeHEq : HEq
      (((canonicalPositiveNegativeBirth 𝒞 simple ≫
          eqToHom (congrArg (ribbonWordObject 𝒞) birthBinding)) ≫
        contextualizeRibbonMorphism 𝒞
          [] before after right
          (tensorUnitProjector 𝒞
              (ribbonWordObject 𝒞 before) ≫
            eqToHom
              (congrArg (ribbonWordObject 𝒞) beforeAfter))) ≫
        (eqToHom (congrArg (ribbonWordObject 𝒞) deathBinding) ≫
          canonicalPositiveNegativeDeath 𝒞 simple))
      canonicalComposite :=
    CategoryTheory.heq_comp
      (f :=
        (canonicalPositiveNegativeBirth 𝒞 simple ≫
            eqToHom (congrArg (ribbonWordObject 𝒞) birthBinding)) ≫
          contextualizeRibbonMorphism 𝒞
            [] before after right
            (tensorUnitProjector 𝒞
                (ribbonWordObject 𝒞 before) ≫
              eqToHom
                (congrArg (ribbonWordObject 𝒞) beforeAfter)))
      (g :=
        eqToHom (congrArg (ribbonWordObject 𝒞) deathBinding) ≫
          canonicalPositiveNegativeDeath 𝒞 simple)
      (f' :=
        canonicalPositiveNegativeBirth 𝒞 simple ≫
          contextualizeRibbonMorphism 𝒞
            [] canonicalBefore canonicalBefore canonicalRight
            (tensorUnitProjector 𝒞
                (𝒞.simples.simpleObject simple) ⊗ₘ
              𝟙 (𝟙_ 𝒞.C)))
      (g' := canonicalPositiveNegativeDeath 𝒞 simple)
      rfl
      (congrArg (ribbonWordObject 𝒞) deathBinding)
      rfl
      birthContextHEq deathHEq
  have canonicalValue :
      canonicalComposite =
        specialCutMeridianMorphismWithoutExplicitTwist 𝒞 simple := by
    dsimp [canonicalComposite, canonicalBefore, canonicalRight]
    simpa only [Category.assoc] using
      canonicalBirthProjectorDeathMorphism 𝒞 simple
  have reassociate :
      canonicalPositiveNegativeBirth 𝒞 simple ≫
          eqToHom (congrArg (ribbonWordObject 𝒞) birthBinding) ≫
          contextualizeRibbonMorphism 𝒞
            [] before after right
            (tensorUnitProjector 𝒞
                (ribbonWordObject 𝒞 before) ≫
              eqToHom
                (congrArg (ribbonWordObject 𝒞) beforeAfter)) ≫
          eqToHom (congrArg (ribbonWordObject 𝒞) deathBinding) ≫
          canonicalPositiveNegativeDeath 𝒞 simple =
        ((canonicalPositiveNegativeBirth 𝒞 simple ≫
            eqToHom (congrArg (ribbonWordObject 𝒞) birthBinding)) ≫
          contextualizeRibbonMorphism 𝒞
            [] before after right
            (tensorUnitProjector 𝒞
                (ribbonWordObject 𝒞 before) ≫
              eqToHom
                (congrArg (ribbonWordObject 𝒞) beforeAfter))) ≫
          (eqToHom (congrArg (ribbonWordObject 𝒞) deathBinding) ≫
            canonicalPositiveNegativeDeath 𝒞 simple) := by
    simp only [Category.assoc]
  exact (heq_of_eq reassociate).trans
    (wholeHEq.trans (heq_of_eq canonicalValue))

theorem localBirthProjectorDeathMorphism
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (dotted : diagram.trace.ComponentId)
    (puncture : DottedPuncture diagram.trace)
    (first second third : diagram.trace.StrandId)
    (firstSecondComponent :
      (diagram.trace.strands first).component =
        (diagram.trace.strands second).component)
    (firstSecondOrientation :
      (diagram.trace.strands first).orientation ≠
        (diagram.trace.strands second).orientation)
    (thirdSecondComponent :
      (diagram.trace.strands third).component =
        (diagram.trace.strands second).component)
    (thirdSecondOrientation :
      (diagram.trace.strands third).orientation ≠
        (diagram.trace.strands second).orientation)
    (firstPositive :
      (diagram.trace.strands first).orientation = .positive)
    (secondNegative :
      (diagram.trace.strands second).orientation = .negative)
    (thirdPositive :
      (diagram.trace.strands third).orientation = .positive)
    (inputCanonical : puncture.inputStrand = first)
    (outputCanonical : puncture.outputStrand = third)
    (pairing :
      (CutOpenEvent.projectorHole dotted [puncture]).StrandContinuationsAreWellFormed) :
    pairedBirthMorphism 𝒞 diagram labeling
          first second firstSecondComponent firstSecondOrientation ≫
        eqToHom
          (congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 diagram labeling word))
            (congrArg
              (fun strand => [strand, second])
              inputCanonical.symm)) ≫
        contextualizeRibbonMorphism 𝒞
          []
          (exteriorWord 𝒞 diagram labeling
            [puncture.inputStrand])
          (exteriorWord 𝒞 diagram labeling
            [puncture.outputStrand])
          (exteriorWord 𝒞 diagram labeling [second])
          (compileCutOpenEventMorphism
            𝒞 diagram labeling
            (.projectorHole dotted [puncture]) pairing) ≫
        eqToHom
          (congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 diagram labeling word))
            (congrArg
              (fun strand => [strand, second])
              outputCanonical)) ≫
        pairedDeathMorphism 𝒞 diagram labeling
          third second thirdSecondComponent thirdSecondOrientation =
      specialCutMeridianMorphismWithoutExplicitTwist 𝒞
        (exteriorStrandLabel 𝒞 diagram labeling first) := by
  subst first
  subst third
  have inputOutputComponent :
      (diagram.trace.strands puncture.inputStrand).component =
        (diagram.trace.strands puncture.outputStrand).component :=
    puncture.input_on_two_handle.trans
      puncture.output_on_two_handle.symm
  have inputOutputOriented :=
    orientedExteriorStrand_eq_of_component_and_orientation
      𝒞 diagram labeling inputOutputComponent
      puncture.orientation_preserved
  have firstSecondLabel :=
    exteriorStrandLabel_eq_of_component_eq
      𝒞 diagram labeling firstSecondComponent
  have outputSecondLabel :=
    exteriorStrandLabel_eq_of_component_eq
      𝒞 diagram labeling thirdSecondComponent
  have inputWordCanonical :
      exteriorWord 𝒞 diagram labeling [puncture.inputStrand] =
        [{ label := exteriorStrandLabel 𝒞 diagram labeling second,
           direction := .forward }] := by
    simp [exteriorWord, orientedExteriorStrand,
      firstSecondLabel, firstPositive, ribbonDirectionOfStrandOrientation]
  have outputWordCanonical :
      exteriorWord 𝒞 diagram labeling [puncture.outputStrand] =
        [{ label := exteriorStrandLabel 𝒞 diagram labeling second,
           direction := .forward }] := by
    simp [exteriorWord, orientedExteriorStrand,
      outputSecondLabel, thirdPositive, ribbonDirectionOfStrandOrientation]
  have secondWordCanonical :
      exteriorWord 𝒞 diagram labeling [second] =
        [{ label := exteriorStrandLabel 𝒞 diagram labeling second,
           direction := .dual }] := by
    simp [exteriorWord, orientedExteriorStrand,
      secondNegative, ribbonDirectionOfStrandOrientation]
  have cutWordCanonical :
      cutBoundaryWord 𝒞 diagram labeling [puncture] =
        [{ label := exteriorStrandLabel 𝒞 diagram labeling second,
           direction := .forward }] :=
    (exteriorInputWord_eq_cutBoundaryWord
        𝒞 diagram labeling [puncture]).symm.trans inputWordCanonical
  have beforeAfter :
      exteriorWord 𝒞 diagram labeling [puncture.inputStrand] =
        exteriorWord 𝒞 diagram labeling [puncture.outputStrand] :=
    inputWordCanonical.trans outputWordCanonical.symm
  have birthBinding :
      positiveNegativeDualPairWord 𝒞
          (exteriorStrandLabel 𝒞 diagram labeling second) =
        List.append
          (exteriorWord 𝒞 diagram labeling [puncture.inputStrand])
          (exteriorWord 𝒞 diagram labeling [second]) := by
    calc
      positiveNegativeDualPairWord 𝒞
          (exteriorStrandLabel 𝒞 diagram labeling second) =
          List.append
            [{ label := exteriorStrandLabel 𝒞 diagram labeling second,
               direction := .forward }]
            [{ label := exteriorStrandLabel 𝒞 diagram labeling second,
               direction := .dual }] := rfl
      _ = _ := congrArg₂ List.append
        inputWordCanonical.symm secondWordCanonical.symm
  have deathBinding :
      List.append
          (exteriorWord 𝒞 diagram labeling [puncture.outputStrand])
          (exteriorWord 𝒞 diagram labeling [second]) =
        positiveNegativeDualPairWord 𝒞
          (exteriorStrandLabel 𝒞 diagram labeling second) := by
    calc
      List.append
          (exteriorWord 𝒞 diagram labeling [puncture.outputStrand])
          (exteriorWord 𝒞 diagram labeling [second]) =
          List.append
            [{ label := exteriorStrandLabel 𝒞 diagram labeling second,
               direction := .forward }]
            [{ label := exteriorStrandLabel 𝒞 diagram labeling second,
               direction := .dual }] :=
        congrArg₂ List.append outputWordCanonical secondWordCanonical
      _ = _ := rfl
  have transported :=
    transportedCanonicalBirthProjectorDeathMorphism 𝒞
      (exteriorStrandLabel 𝒞 diagram labeling second)
      (exteriorWord 𝒞 diagram labeling [puncture.inputStrand])
      (exteriorWord 𝒞 diagram labeling [puncture.outputStrand])
      (exteriorWord 𝒞 diagram labeling [second])
      inputWordCanonical outputWordCanonical secondWordCanonical
      beforeAfter birthBinding deathBinding
  rw [compileCutOpenEventMorphism_projectorHole]
  conv_rhs => rw [firstSecondLabel]
  have transportedEq := eq_of_heq transported
  simpa [pairedBirthMorphism, pairedDeathMorphism, projectorHoleMorphism,
    firstPositive, secondNegative, thirdPositive,
    firstSecondLabel, outputSecondLabel, inputOutputOriented,
    inputWordCanonical, outputWordCanonical, secondWordCanonical,
    cutWordCanonical] using
    transportedEq

theorem standardOneTwoBirth_localThreeEventMorphism
    (𝒞 : PremodularFusionCategory K)
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardOneTwoBirth source target)
    (labeling : TwoHandleLabeling 𝒞 target)
    (dotted : target.trace.ComponentId)
    (puncture : DottedPuncture target.trace)
    (serialized :
      serializePuncture puncture = oneTwoLocalPuncture source)
    (pairing :
      (CutOpenEvent.projectorHole dotted [puncture]).StrandContinuationsAreWellFormed) :
    pairedBirthMorphism 𝒞 target labeling
          (oneTwoFirstStrand normalForm)
          (oneTwoSecondStrand normalForm)
          (standardOneTwoBirth_first_second_component normalForm)
          (standardOneTwoBirth_first_second_orientation normalForm) ≫
        eqToHom
          (congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 target labeling word))
            (congrArg
              (fun strand =>
                [strand, oneTwoSecondStrand normalForm])
              (oneTwoPuncture_input_eq
                normalForm puncture serialized).symm)) ≫
        contextualizeRibbonMorphism 𝒞
          []
          (exteriorWord 𝒞 target labeling
            [puncture.inputStrand])
          (exteriorWord 𝒞 target labeling
            [puncture.outputStrand])
          (exteriorWord 𝒞 target labeling
            [oneTwoSecondStrand normalForm])
          (compileCutOpenEventMorphism
            𝒞 target labeling
            (.projectorHole dotted [puncture]) pairing) ≫
        eqToHom
          (congrArg
            (fun word =>
              ribbonWordObject 𝒞
                (exteriorWord 𝒞 target labeling word))
            (congrArg
              (fun strand =>
                [strand, oneTwoSecondStrand normalForm])
              (oneTwoPuncture_output_eq
                normalForm puncture serialized))) ≫
        pairedDeathMorphism 𝒞 target labeling
          (oneTwoThirdStrand normalForm)
          (oneTwoSecondStrand normalForm)
          (standardOneTwoBirth_third_second_component normalForm)
          (standardOneTwoBirth_third_second_orientation normalForm) =
      specialCutMeridianMorphismWithoutExplicitTwist 𝒞
        (exteriorStrandLabel 𝒞 target labeling
          (oneTwoFirstStrand normalForm)) := by
  have firstOrientation :=
    congrArg SerializedStrand.orientation
      (standardOneTwoBirth_firstStrandData normalForm)
  have secondOrientation :=
    congrArg SerializedStrand.orientation
      (standardOneTwoBirth_secondStrandData normalForm)
  have thirdOrientation :=
    congrArg SerializedStrand.orientation
      (standardOneTwoBirth_thirdStrandData normalForm)
  simp [serializeStrand] at firstOrientation secondOrientation thirdOrientation
  have inputEq :=
    oneTwoPuncture_input_eq normalForm puncture serialized
  have outputEq :=
    oneTwoPuncture_output_eq normalForm puncture serialized
  exact localBirthProjectorDeathMorphism
    𝒞 target labeling dotted puncture
    (oneTwoFirstStrand normalForm)
    (oneTwoSecondStrand normalForm)
    (oneTwoThirdStrand normalForm)
    (standardOneTwoBirth_first_second_component normalForm)
    (standardOneTwoBirth_first_second_orientation normalForm)
    (standardOneTwoBirth_third_second_component normalForm)
    (standardOneTwoBirth_third_second_orientation normalForm)
    firstOrientation secondOrientation thirdOrientation
    inputEq outputEq pairing

end

end TwistedYetter.Kirby.Final.Proofs
