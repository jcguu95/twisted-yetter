import TwistedYetter.Kirby.Final.Proofs.CancellationTraceFactorization
import TwistedYetter.Kirby.Final.Semantics.Independent.TwoThreeLocalReplacement

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe v uC

namespace TwistedYetter.Kirby.Final.Proofs

noncomputable section

theorem standardTwoThreeBirth_eventCount
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.dottedCuts.exterior.eventCount =
      source.dottedCuts.exterior.eventCount + 3 := by
  have lengths := congrArg List.length normalForm.2.2.1
  simp [serializedExteriorEvents, twoThreeLocalEvents] at lengths
  omega

theorem standardTwoThreeBirth_componentCount
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.trace.componentCount =
      source.trace.componentCount + 1 := by
  have lengths := congrArg List.length normalForm.1
  simp [serializedComponents, twoThreeLocalComponents] at lengths
  omega

theorem standardTwoThreeBirth_strandCount
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.trace.strandCount =
      source.trace.strandCount + 3 := by
  have lengths := congrArg List.length normalForm.2.1
  simp [serializedStrands, twoThreeLocalStrands] at lengths
  omega

def twoThreeFirstStrand
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.trace.StrandId :=
  ⟨source.trace.strandCount, by
    rw [standardTwoThreeBirth_strandCount normalForm]
    omega⟩

def twoThreeSecondStrand
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.trace.StrandId :=
  ⟨source.trace.strandCount + 1, by
    rw [standardTwoThreeBirth_strandCount normalForm]
    omega⟩

def twoThreeThirdStrand
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.trace.StrandId :=
  ⟨source.trace.strandCount + 2, by
    rw [standardTwoThreeBirth_strandCount normalForm]
    omega⟩

theorem standardTwoThreeBirth_eventZero_eq
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.dottedCuts.exterior.events
        ⟨0, by
          rw [standardTwoThreeBirth_eventCount normalForm]
          omega⟩ =
      .birth
        (twoThreeFirstStrand normalForm)
        (twoThreeSecondStrand normalForm) := by
  have atIndex :=
    congrArg (fun events => events[0]?) normalForm.2.2.1
  simp [serializedExteriorEvents, twoThreeLocalEvents] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  apply serializeCutOpenEvent_injective
  simpa [twoThreeFirstStrand, twoThreeSecondStrand] using atIndex

theorem standardTwoThreeBirth_eventTwo_eq
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.dottedCuts.exterior.events
        ⟨2, by
          rw [standardTwoThreeBirth_eventCount normalForm]
          omega⟩ =
      .death
        (twoThreeThirdStrand normalForm)
        (twoThreeSecondStrand normalForm) := by
  have atIndex :=
    congrArg (fun events => events[2]?) normalForm.2.2.1
  simp [serializedExteriorEvents, twoThreeLocalEvents] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  apply serializeCutOpenEvent_injective
  simpa [twoThreeThirdStrand, twoThreeSecondStrand] using atIndex

theorem standardTwoThreeBirth_eventOne_eq
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.dottedCuts.exterior.events
        ⟨1, by
          rw [standardTwoThreeBirth_eventCount normalForm]
          omega⟩ =
      .framingTwist
        (twoThreeFirstStrand normalForm)
        (twoThreeThirdStrand normalForm)
        .positive := by
  have atIndex :=
    congrArg (fun events => events[1]?) normalForm.2.2.1
  simp [serializedExteriorEvents, twoThreeLocalEvents] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  apply serializeCutOpenEvent_injective
  simpa [twoThreeFirstStrand, twoThreeThirdStrand] using atIndex

theorem standardTwoThreeBirth_stateZero
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.dottedCuts.exterior.activeOrder
        ⟨0, by
          rw [standardTwoThreeBirth_eventCount normalForm]
          omega⟩ = [] := by
  have atIndex :=
    congrArg (fun states => states[0]?) normalForm.2.2.2.1
  simp [serializedActiveOrders, twoThreeLocalActiveOrders] at atIndex
  simpa using atIndex

theorem standardTwoThreeBirth_stateOne
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.dottedCuts.exterior.activeOrder
        ⟨1, by
          rw [standardTwoThreeBirth_eventCount normalForm]
          omega⟩ =
      [twoThreeFirstStrand normalForm,
        twoThreeSecondStrand normalForm] := by
  have atIndex :=
    congrArg (fun states => states[1]?) normalForm.2.2.2.1
  simp [serializedActiveOrders, twoThreeLocalActiveOrders] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  change
    List.map Fin.val
        (target.dottedCuts.exterior.activeOrder
          ⟨1, by
            rw [standardTwoThreeBirth_eventCount normalForm]
            omega⟩) =
      List.map Fin.val
        [twoThreeFirstStrand normalForm,
          twoThreeSecondStrand normalForm] at atIndex
  exact (List.map_injective_iff.mpr Fin.val_injective) atIndex

theorem standardTwoThreeBirth_stateTwo
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.dottedCuts.exterior.activeOrder
        ⟨2, by
          rw [standardTwoThreeBirth_eventCount normalForm]
          omega⟩ =
      [twoThreeThirdStrand normalForm,
        twoThreeSecondStrand normalForm] := by
  have atIndex :=
    congrArg (fun states => states[2]?) normalForm.2.2.2.1
  simp [serializedActiveOrders, twoThreeLocalActiveOrders] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  change
    List.map Fin.val
        (target.dottedCuts.exterior.activeOrder
          ⟨2, by
            rw [standardTwoThreeBirth_eventCount normalForm]
            omega⟩) =
      List.map Fin.val
        [twoThreeThirdStrand normalForm,
          twoThreeSecondStrand normalForm] at atIndex
  exact (List.map_injective_iff.mpr Fin.val_injective) atIndex

theorem standardTwoThreeBirth_stateThree
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    target.dottedCuts.exterior.activeOrder
        ⟨3, by
          rw [standardTwoThreeBirth_eventCount normalForm]
          omega⟩ = [] := by
  have atIndex :=
    congrArg (fun states => states[3]?) normalForm.2.2.2.1
  simp [serializedActiveOrders, twoThreeLocalActiveOrders,
    source.dottedCuts.exterior.initialBoundaryEmpty] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  change
    List.map Fin.val
        (target.dottedCuts.exterior.activeOrder
          ⟨3, by
            rw [standardTwoThreeBirth_eventCount normalForm]
            omega⟩) =
      List.map Fin.val [] at atIndex
  exact (List.map_injective_iff.mpr Fin.val_injective) atIndex

theorem standardTwoThreeBirth_firstStrandData
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    serializeStrand
        (target.trace.strands (twoThreeFirstStrand normalForm)) =
      {
        component := source.trace.componentCount
        orientation := .positive
      } := by
  have atIndex :=
    congrArg (fun strands => strands[source.trace.strandCount]?)
      normalForm.2.1
  simp [serializedStrands, twoThreeLocalStrands] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  simpa [twoThreeFirstStrand] using atIndex

theorem standardTwoThreeBirth_secondStrandData
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    serializeStrand
        (target.trace.strands (twoThreeSecondStrand normalForm)) =
      {
        component := source.trace.componentCount
        orientation := .negative
      } := by
  have atIndex :=
    congrArg (fun strands => strands[source.trace.strandCount + 1]?)
      normalForm.2.1
  simp [serializedStrands, twoThreeLocalStrands] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  simpa [twoThreeSecondStrand] using atIndex

theorem standardTwoThreeBirth_thirdStrandData
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    serializeStrand
        (target.trace.strands (twoThreeThirdStrand normalForm)) =
      {
        component := source.trace.componentCount
        orientation := .positive
      } := by
  have atIndex :=
    congrArg (fun strands => strands[source.trace.strandCount + 2]?)
      normalForm.2.1
  simp [serializedStrands, twoThreeLocalStrands] at atIndex
  rcases atIndex with ⟨_positive, atIndex⟩
  simpa [twoThreeThirdStrand] using atIndex

structure TwoThreeGraphCoordinates
    (lower higher : HomologicallyMarkedDiagram) where
  indexEquiv :
    (Fin lower.diagram.handles.hTwo ⊕ Unit) ≃
      Fin higher.diagram.handles.hTwo

def TwoThreeGraphCoordinates.MatchesIsolatedComponent
    {lower higher : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates lower higher) : Prop :=
  (∀ i : Fin lower.diagram.handles.hTwo,
    (higher.diagram.handles.twoHandleIndex
      (coordinates.indexEquiv (Sum.inl i))).1.1 =
        (lower.diagram.handles.twoHandleIndex i).1.1) ∧
  ((higher.diagram.handles.twoHandleIndex
    (coordinates.indexEquiv (Sum.inr ()))).1.1 =
      lower.diagram.trace.componentCount)

theorem TwoThreeGraphCoordinates.oldComponent
    {lower higher : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates lower higher)
    (binding : coordinates.MatchesIsolatedComponent)
    (i : Fin lower.diagram.handles.hTwo) :
    (higher.diagram.handles.twoHandleIndex
      (coordinates.indexEquiv (Sum.inl i))).1.1 =
        (lower.diagram.handles.twoHandleIndex i).1.1 :=
  binding.1 i

def TwoThreeGraphCoordinates.ofAdded
    {lower higher : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport lower higher}
    (coordinates :
      AddedTwoHandleCoordinates lower higher transport) :
    TwoThreeGraphCoordinates lower higher where
  indexEquiv := coordinates.indexEquiv

theorem TwoThreeGraphCoordinates.ofAdded_matches
    {lower higher : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport lower higher}
    (coordinates :
      AddedTwoHandleCoordinates lower higher transport)
    (binding : coordinates.MatchesTwoThreeBirthComponent) :
    (TwoThreeGraphCoordinates.ofAdded coordinates).MatchesIsolatedComponent :=
  binding

def TwoThreeGraphCoordinates.ofRemoved
    {higher lower : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport higher lower}
    (coordinates :
      RemovedTwoHandleCoordinates higher lower transport) :
    TwoThreeGraphCoordinates lower higher where
  indexEquiv := coordinates.indexEquiv

theorem TwoThreeGraphCoordinates.ofRemoved_matches
    {higher lower : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport higher lower}
    (coordinates :
      RemovedTwoHandleCoordinates higher lower transport)
    (binding : coordinates.MatchesTwoThreeDeathComponent) :
    (TwoThreeGraphCoordinates.ofRemoved coordinates).MatchesIsolatedComponent :=
  binding

def TwoThreeGraphCoordinates.mergeLabeling
    {lower higher : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates lower higher)
    {Label : Type*}
    (lowerLabeling : Fin lower.diagram.handles.hTwo → Label)
    (newLabel : Label) :
    Fin higher.diagram.handles.hTwo → Label :=
  fun i =>
    match coordinates.indexEquiv.symm i with
    | .inl old => lowerLabeling old
    | .inr _ => newLabel

noncomputable def standardTwoThreeBirthTargetTrace
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (labeling : TwoHandleLabeling 𝒞 target) :
    FiniteMorphismTrace 𝒞.C
      (source.dottedCuts.exterior.eventCount + 3) :=
  FiniteMorphismTrace.castEventCount
    (standardTwoThreeBirth_eventCount normalForm).symm
    (compiledExteriorTrace 𝒞 target labeling)

theorem standardTwoThreeBirthTargetTrace_composeAll
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (labeling : TwoHandleLabeling 𝒞 target) :
    HEq
      (standardTwoThreeBirthTargetTrace 𝒞 normalForm labeling).composeAll
      (compiledExteriorTrace 𝒞 target labeling).composeAll := by
  exact FiniteMorphismTrace.castEventCount_composeAll _ _

theorem standardTwoThreeBirth_newLoopLabel
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple) :
    exteriorStrandLabel 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (twoThreeFirstStrand normalForm) =
      newLabel := by
  have firstData := standardTwoThreeBirth_firstStrandData normalForm
  have firstComponent :
      (target.diagram.trace.strands
        (twoThreeFirstStrand normalForm)).component.1 =
        source.diagram.trace.componentCount := by
    simpa [serializeStrand] using
      congrArg SerializedStrand.component firstData
  have firstRole :
      (target.diagram.trace.components
        (target.diagram.trace.strands
          (twoThreeFirstStrand normalForm)).component).role ≠ .dotted := by
    have componentEq :
        (target.diagram.trace.strands
          (twoThreeFirstStrand normalForm)).component =
          ⟨source.diagram.trace.componentCount, by
            rw [standardTwoThreeBirth_componentCount normalForm]
            omega⟩ := Fin.ext firstComponent
    rw [componentEq]
    have componentData :=
      congrArg
        (fun components => components[source.diagram.trace.componentCount]?)
        normalForm.1
    simp [serializedComponents, twoThreeLocalComponents] at componentData
    rcases componentData with ⟨_positive, componentData⟩
    simpa [componentData]
  unfold exteriorStrandLabel
  rw [dif_pos firstRole]
  have indexEq :
      target.diagram.handles.twoHandleIndex.symm
          ⟨(target.diagram.trace.strands
              (twoThreeFirstStrand normalForm)).component,
            firstRole⟩ =
        coordinates.indexEquiv (Sum.inr ()) := by
    apply target.diagram.handles.twoHandleIndex.injective
    apply Subtype.ext
    apply Fin.ext
    rw [Equiv.apply_symm_apply]
    calc
      (target.diagram.trace.strands
          (twoThreeFirstStrand normalForm)).component.1 =
          source.diagram.trace.componentCount := firstComponent
      _ =
          (target.diagram.handles.twoHandleIndex
            (coordinates.indexEquiv (Sum.inr ()))).1.1 :=
        coordinateBinding.2.symm
  rw [indexEq]
  simp [TwoThreeGraphCoordinates.mergeLabeling]

def standardTwoThreeBirthOldComponent
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (component : source.trace.ComponentId) :
    target.trace.ComponentId :=
  ⟨component.1, by
    rw [standardTwoThreeBirth_componentCount normalForm]
    omega⟩

def standardTwoThreeBirthOldStrand
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (strand : source.trace.StrandId) :
    target.trace.StrandId :=
  ⟨strand.1, by
    rw [standardTwoThreeBirth_strandCount normalForm]
    omega⟩

theorem standardTwoThreeBirth_oldComponentData
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (component : source.trace.ComponentId) :
    target.trace.components
        (standardTwoThreeBirthOldComponent normalForm component) =
      source.trace.components component := by
  have targetBound :
      component.1 < target.trace.componentCount := by
    rw [standardTwoThreeBirth_componentCount normalForm]
    omega
  have atIndex :=
    congrArg (fun components => components[component.1]?) normalForm.1
  simp [serializedComponents, twoThreeLocalComponents,
    standardTwoThreeBirthOldComponent, component.2, targetBound] at atIndex
  simpa [standardTwoThreeBirthOldComponent] using atIndex

theorem standardTwoThreeBirth_oldStrandComponentValue
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (strand : source.trace.StrandId) :
    (target.trace.strands
      (standardTwoThreeBirthOldStrand normalForm strand)).component.1 =
      (source.trace.strands strand).component.1 := by
  have targetBound :
      strand.1 < target.trace.strandCount := by
    rw [standardTwoThreeBirth_strandCount normalForm]
    omega
  have atIndex :=
    congrArg (fun strands => strands[strand.1]?) normalForm.2.1
  simp [serializedStrands, twoThreeLocalStrands,
    serializeStrand, standardTwoThreeBirthOldStrand,
    strand.2, targetBound] at atIndex
  rw [List.getElem?_append_left (by simp [strand.2])] at atIndex
  simp at atIndex
  exact atIndex.1

theorem standardTwoThreeBirth_oldStrandComponent
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (strand : source.trace.StrandId) :
    (target.trace.strands
      (standardTwoThreeBirthOldStrand normalForm strand)).component =
      standardTwoThreeBirthOldComponent normalForm
        (source.trace.strands strand).component :=
  Fin.ext
    (standardTwoThreeBirth_oldStrandComponentValue normalForm strand)

theorem standardTwoThreeBirth_oldStrandOrientation
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (strand : source.trace.StrandId) :
    (target.trace.strands
      (standardTwoThreeBirthOldStrand normalForm strand)).orientation =
      (source.trace.strands strand).orientation := by
  have targetBound :
      strand.1 < target.trace.strandCount := by
    rw [standardTwoThreeBirth_strandCount normalForm]
    omega
  have atIndex :=
    congrArg (fun strands => strands[strand.1]?) normalForm.2.1
  simp [serializedStrands, twoThreeLocalStrands,
    serializeStrand, standardTwoThreeBirthOldStrand,
    strand.2, targetBound] at atIndex
  rw [List.getElem?_append_left (by simp [strand.2])] at atIndex
  simp at atIndex
  exact atIndex.2

theorem standardTwoThreeBirth_oldExteriorStrandLabel
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (strand : source.diagram.trace.StrandId) :
    exteriorStrandLabel 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardTwoThreeBirthOldStrand normalForm strand) =
      exteriorStrandLabel 𝒞 source.diagram sourceLabeling strand := by
  let sourceComponent :=
    (source.diagram.trace.strands strand).component
  let targetComponent :=
    (target.diagram.trace.strands
      (standardTwoThreeBirthOldStrand normalForm strand)).component
  have componentValue :
      targetComponent.1 = sourceComponent.1 :=
    standardTwoThreeBirth_oldStrandComponentValue normalForm strand
  have componentEq :
      targetComponent =
        standardTwoThreeBirthOldComponent normalForm sourceComponent :=
    Fin.ext componentValue
  have componentData :
      target.diagram.trace.components targetComponent =
        source.diagram.trace.components sourceComponent := by
    rw [componentEq]
    exact standardTwoThreeBirth_oldComponentData normalForm sourceComponent
  unfold exteriorStrandLabel
  dsimp only [targetComponent, sourceComponent] at componentEq componentData ⊢
  split <;> rename_i targetRole
  · have sourceRole :
        (source.diagram.trace.components
          (source.diagram.trace.strands strand).component).role ≠
            .dotted := by
        simpa [componentData] using targetRole
    rw [dif_pos sourceRole]
    let sourceIndex :=
      source.diagram.handles.twoHandleIndex.symm
        ⟨(source.diagram.trace.strands strand).component, sourceRole⟩
    have targetIndexEq :
        target.diagram.handles.twoHandleIndex.symm
            ⟨(target.diagram.trace.strands
                (standardTwoThreeBirthOldStrand normalForm strand)).component,
              targetRole⟩ =
          coordinates.indexEquiv (Sum.inl sourceIndex) := by
      apply target.diagram.handles.twoHandleIndex.injective
      apply Subtype.ext
      apply Fin.ext
      rw [Equiv.apply_symm_apply]
      calc
        (target.diagram.trace.strands
            (standardTwoThreeBirthOldStrand normalForm strand)).component.1 =
            (source.diagram.trace.strands strand).component.1 :=
          componentValue
        _ =
            (source.diagram.handles.twoHandleIndex sourceIndex).1.1 := by
          simp [sourceIndex]
        _ =
            (target.diagram.handles.twoHandleIndex
              (coordinates.indexEquiv (Sum.inl sourceIndex))).1.1 :=
          (coordinates.oldComponent coordinateBinding sourceIndex).symm
    rw [targetIndexEq]
    simp [TwoThreeGraphCoordinates.mergeLabeling, sourceIndex]
  · have sourceRole :
        ¬(source.diagram.trace.components
          (source.diagram.trace.strands strand).component).role ≠
            .dotted := by
        simpa [componentData] using targetRole
    rw [dif_neg sourceRole]

theorem standardTwoThreeBirth_oldOrientedExteriorStrand
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (strand : source.diagram.trace.StrandId) :
    orientedExteriorStrand 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardTwoThreeBirthOldStrand normalForm strand) =
      orientedExteriorStrand 𝒞 source.diagram sourceLabeling strand := by
  apply congrArg₂
    (fun label direction =>
      ({ label := label, direction := direction } : OrientedSimple 𝒞))
  · exact standardTwoThreeBirth_oldExteriorStrandLabel
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel strand
  · exact congrArg ribbonDirectionOfStrandOrientation
      (standardTwoThreeBirth_oldStrandOrientation normalForm strand)

def standardTwoThreeBirthOldStrands
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (strands : List source.trace.StrandId) :
    List target.trace.StrandId :=
  strands.map (standardTwoThreeBirthOldStrand normalForm)

theorem standardTwoThreeBirth_oldStrands_values
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (strands : List source.trace.StrandId) :
    List.map Fin.val
        (standardTwoThreeBirthOldStrands normalForm strands) =
      List.map Fin.val strands := by
  induction strands with
  | nil => rfl
  | cons strand rest inductionHypothesis =>
      simp only [standardTwoThreeBirthOldStrands, List.map_cons]
      exact congrArg (List.cons strand.1) inductionHypothesis

theorem standardTwoThreeBirth_oldExteriorWord
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (strands : List source.diagram.trace.StrandId) :
    exteriorWord 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardTwoThreeBirthOldStrands normalForm strands) =
      exteriorWord 𝒞 source.diagram sourceLabeling strands := by
  induction strands with
  | nil => rfl
  | cons strand rest inductionHypothesis =>
      simp only [standardTwoThreeBirthOldStrands, List.map_cons,
        exteriorWord]
      rw [standardTwoThreeBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel strand]
      exact congrArg
        (List.cons
          (orientedExteriorStrand 𝒞 source.diagram
            sourceLabeling strand))
        inductionHypothesis

theorem standardTwoThreeBirth_oldActiveOrder
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (state : Fin (source.dottedCuts.exterior.eventCount + 1)) :
    target.dottedCuts.exterior.activeOrder
        ⟨state.1 + 3, by
          rw [standardTwoThreeBirth_eventCount normalForm]
          omega⟩ =
      standardTwoThreeBirthOldStrands normalForm
        (source.dottedCuts.exterior.activeOrder state) := by
  apply List.map_injective_iff.mpr Fin.val_injective
  have atIndex :=
    congrArg (fun orders => orders[state.1 + 3]?)
      normalForm.2.2.2.1
  rcases state with ⟨_ | state, stateBound⟩
  · calc
      _ = List.map (@Fin.val source.trace.strandCount)
          (source.dottedCuts.exterior.activeOrder 0) := by
            simp [serializedActiveOrders,
              twoThreeLocalActiveOrders] at atIndex
            rcases atIndex with ⟨_, atIndex⟩
            exact atIndex
      _ = _ :=
        (standardTwoThreeBirth_oldStrands_values normalForm _).symm
  · have sourceBound :
        state < source.dottedCuts.exterior.eventCount := by omega
    have targetBound :
        state + 3 < target.dottedCuts.exterior.eventCount := by
      rw [standardTwoThreeBirth_eventCount normalForm]
      omega
    simp [serializedActiveOrders, twoThreeLocalActiveOrders,
      sourceBound, targetBound] at atIndex
    calc
      _ = List.map (@Fin.val source.trace.strandCount)
          (source.dottedCuts.exterior.activeOrder
            ⟨state + 1, stateBound⟩) := by
              convert atIndex using 1
      _ = _ :=
        (standardTwoThreeBirth_oldStrands_values normalForm _).symm

theorem standardTwoThreeBirth_oldEventSerialized
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (event : Fin source.dottedCuts.exterior.eventCount) :
    serializeCutOpenEvent
        (target.dottedCuts.exterior.events
          ⟨event.1 + 3, by
            rw [standardTwoThreeBirth_eventCount normalForm]
            omega⟩) =
      serializeCutOpenEvent
        (source.dottedCuts.exterior.events event) := by
  have atIndex :=
    congrArg (fun events => events[event.1 + 3]?)
      normalForm.2.2.1
  have targetBound :
      event.1 + 3 <
        (serializedExteriorEvents target).length := by
    simp [serializedExteriorEvents,
      standardTwoThreeBirth_eventCount normalForm]
  simp [serializedExteriorEvents, twoThreeLocalEvents,
    targetBound, event.2] at atIndex
  exact atIndex.choose_spec

def standardTwoThreeBirthOldPuncture
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (puncture : DottedPuncture source.trace) :
    DottedPuncture target.trace where
  dottedComponent :=
    standardTwoThreeBirthOldComponent normalForm puncture.dottedComponent
  twoHandleComponent :=
    standardTwoThreeBirthOldComponent normalForm puncture.twoHandleComponent
  inputStrand :=
    standardTwoThreeBirthOldStrand normalForm puncture.inputStrand
  outputStrand :=
    standardTwoThreeBirthOldStrand normalForm puncture.outputStrand
  direction := puncture.direction
  cutPosition := puncture.cutPosition
  dotted_role := by
    simpa [standardTwoThreeBirth_oldComponentData normalForm] using
      puncture.dotted_role
  two_handle_role := by
    simpa [standardTwoThreeBirth_oldComponentData normalForm] using
      puncture.two_handle_role
  input_on_two_handle := by
    apply Fin.ext
    calc
      (target.trace.strands
          (standardTwoThreeBirthOldStrand normalForm
            puncture.inputStrand)).component.1 =
          (source.trace.strands puncture.inputStrand).component.1 :=
        standardTwoThreeBirth_oldStrandComponentValue
          normalForm puncture.inputStrand
      _ = puncture.twoHandleComponent.1 :=
        congrArg Fin.val puncture.input_on_two_handle
  output_on_two_handle := by
    apply Fin.ext
    calc
      (target.trace.strands
          (standardTwoThreeBirthOldStrand normalForm
            puncture.outputStrand)).component.1 =
          (source.trace.strands puncture.outputStrand).component.1 :=
        standardTwoThreeBirth_oldStrandComponentValue
          normalForm puncture.outputStrand
      _ = puncture.twoHandleComponent.1 :=
        congrArg Fin.val puncture.output_on_two_handle
  orientation_preserved := by
    rw [standardTwoThreeBirth_oldStrandOrientation normalForm,
      standardTwoThreeBirth_oldStrandOrientation normalForm]
    exact puncture.orientation_preserved

def standardTwoThreeBirthOldEvent
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    CutOpenEvent source.trace → CutOpenEvent target.trace
  | .birth left right =>
      .birth
        (standardTwoThreeBirthOldStrand normalForm left)
        (standardTwoThreeBirthOldStrand normalForm right)
  | .death left right =>
      .death
        (standardTwoThreeBirthOldStrand normalForm left)
        (standardTwoThreeBirthOldStrand normalForm right)
  | .crossing overInput underInput overOutput underOutput sign =>
      .crossing
        (standardTwoThreeBirthOldStrand normalForm overInput)
        (standardTwoThreeBirthOldStrand normalForm underInput)
        (standardTwoThreeBirthOldStrand normalForm overOutput)
        (standardTwoThreeBirthOldStrand normalForm underOutput)
        sign
  | .framingTwist input output sign =>
      .framingTwist
        (standardTwoThreeBirthOldStrand normalForm input)
        (standardTwoThreeBirthOldStrand normalForm output)
        sign
  | .planarIsotopy continuations =>
      .planarIsotopy
        (continuations.map fun pair =>
          (standardTwoThreeBirthOldStrand normalForm pair.1,
            standardTwoThreeBirthOldStrand normalForm pair.2))
  | .projectorHole dotted punctures =>
      .projectorHole
        (standardTwoThreeBirthOldComponent normalForm dotted)
        (punctures.map
          (standardTwoThreeBirthOldPuncture normalForm))

theorem standardTwoThreeBirth_oldEventSerialization
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (event : CutOpenEvent source.trace) :
    serializeCutOpenEvent
        (standardTwoThreeBirthOldEvent normalForm event) =
      serializeCutOpenEvent event := by
  cases event <;>
    simp [standardTwoThreeBirthOldEvent,
      standardTwoThreeBirthOldStrand,
      standardTwoThreeBirthOldComponent,
      standardTwoThreeBirthOldPuncture,
      serializeCutOpenEvent, serializePuncture]

theorem standardTwoThreeBirth_oldEvent
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (event : Fin source.dottedCuts.exterior.eventCount) :
    target.dottedCuts.exterior.events
        ⟨event.1 + 3, by
          rw [standardTwoThreeBirth_eventCount normalForm]
          omega⟩ =
      standardTwoThreeBirthOldEvent normalForm
        (source.dottedCuts.exterior.events event) := by
  apply serializeCutOpenEvent_injective
  rw [standardTwoThreeBirth_oldEventSerialized normalForm event]
  exact
    (standardTwoThreeBirth_oldEventSerialization normalForm _).symm

theorem standardTwoThreeBirth_oldEventStrandContinuationsAreWellFormed
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (event : CutOpenEvent source.trace)
    (pairing : event.StrandContinuationsAreWellFormed) :
    (standardTwoThreeBirthOldEvent normalForm event).StrandContinuationsAreWellFormed := by
  cases event with
  | birth left right =>
      exact
        ⟨by
          rw [standardTwoThreeBirth_oldStrandComponent,
            standardTwoThreeBirth_oldStrandComponent,
            pairing.1],
          by
            rw [standardTwoThreeBirth_oldStrandOrientation,
              standardTwoThreeBirth_oldStrandOrientation]
            exact pairing.2⟩
  | death left right =>
      exact
        ⟨by
          rw [standardTwoThreeBirth_oldStrandComponent,
            standardTwoThreeBirth_oldStrandComponent,
            pairing.1],
          by
            rw [standardTwoThreeBirth_oldStrandOrientation,
              standardTwoThreeBirth_oldStrandOrientation]
            exact pairing.2⟩
  | crossing overInput underInput overOutput underOutput sign =>
      exact
        ⟨by
          rw [standardTwoThreeBirth_oldStrandComponent,
            standardTwoThreeBirth_oldStrandComponent,
            pairing.1],
          by
            rw [standardTwoThreeBirth_oldStrandOrientation,
              standardTwoThreeBirth_oldStrandOrientation]
            exact pairing.2.1,
          by
            rw [standardTwoThreeBirth_oldStrandComponent,
              standardTwoThreeBirth_oldStrandComponent,
              pairing.2.2.1],
          by
            rw [standardTwoThreeBirth_oldStrandOrientation,
              standardTwoThreeBirth_oldStrandOrientation]
            exact pairing.2.2.2⟩
  | framingTwist input output sign =>
      exact
        ⟨by
          rw [standardTwoThreeBirth_oldStrandComponent,
            standardTwoThreeBirth_oldStrandComponent,
            pairing.1],
          by
            rw [standardTwoThreeBirth_oldStrandOrientation,
              standardTwoThreeBirth_oldStrandOrientation]
            exact pairing.2⟩
  | planarIsotopy continuations =>
      intro pair membership
      simp only [standardTwoThreeBirthOldEvent, List.mem_map] at membership
      rcases membership with ⟨sourcePair, sourceMembership, rfl⟩
      have sourcePairing := pairing sourcePair sourceMembership
      exact
        ⟨by
          rw [standardTwoThreeBirth_oldStrandComponent,
            standardTwoThreeBirth_oldStrandComponent,
            sourcePairing.1],
          by
            rw [standardTwoThreeBirth_oldStrandOrientation,
              standardTwoThreeBirth_oldStrandOrientation]
            exact sourcePairing.2⟩
  | projectorHole dotted punctures =>
      intro puncture membership
      simp only [standardTwoThreeBirthOldEvent, List.mem_map] at membership
      rcases membership with ⟨sourcePuncture, sourceMembership, rfl⟩
      have sourcePairing := pairing sourcePuncture sourceMembership
      exact
        ⟨by
          rw [standardTwoThreeBirthOldPuncture,
            standardTwoThreeBirth_oldStrandComponent,
            standardTwoThreeBirth_oldStrandComponent,
            sourcePairing.1],
          by
            rw [standardTwoThreeBirthOldPuncture,
              standardTwoThreeBirth_oldStrandOrientation,
              standardTwoThreeBirth_oldStrandOrientation]
            exact sourcePairing.2⟩

theorem standardTwoThreeBirth_oldEventBeforeWord
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (event : CutOpenEvent source.trace) :
    (standardTwoThreeBirthOldEvent normalForm event).beforeWord =
      standardTwoThreeBirthOldStrands normalForm event.beforeWord := by
  cases event <;>
    simp [standardTwoThreeBirthOldEvent,
      standardTwoThreeBirthOldStrands,
      standardTwoThreeBirthOldPuncture,
      CutOpenEvent.beforeWord]

theorem standardTwoThreeBirth_oldEventAfterWord
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (event : CutOpenEvent source.trace) :
    (standardTwoThreeBirthOldEvent normalForm event).afterWord =
      standardTwoThreeBirthOldStrands normalForm event.afterWord := by
  cases event <;>
    simp [standardTwoThreeBirthOldEvent,
      standardTwoThreeBirthOldStrands,
      standardTwoThreeBirthOldPuncture,
      CutOpenEvent.afterWord]

theorem standardTwoThreeBirth_oldEventMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : CutOpenEvent source.diagram.trace)
    (pairing : event.StrandContinuationsAreWellFormed) :
    HEq
      (compileCutOpenEventMorphism 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardTwoThreeBirthOldEvent normalForm event)
        (standardTwoThreeBirth_oldEventStrandContinuationsAreWellFormed
          normalForm event pairing))
      (compileCutOpenEventMorphism 𝒞 source.diagram
        sourceLabeling event pairing) := by
  cases event with
  | birth left right =>
      have rightLabelEq :=
        standardTwoThreeBirth_oldExteriorStrandLabel
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel right
      have leftOrientationEq :=
        standardTwoThreeBirth_oldStrandOrientation normalForm left
      simp only [compileCutOpenEventMorphism,
        standardTwoThreeBirthOldEvent]
      unfold pairedBirthMorphism
      by_cases leftPositive :
          (source.diagram.trace.strands left).orientation = .positive
      · have targetPositive :
            (target.diagram.trace.strands
              (standardTwoThreeBirthOldStrand normalForm left)).orientation =
                .positive := leftOrientationEq.trans leftPositive
        simp only [leftPositive, targetPositive, ↓reduceDIte]
        exact
          (CategoryTheory.comp_eqToHom_heq _ _).trans
            ((canonicalPositiveNegativeBirth_heq
              𝒞 rightLabelEq).trans
                (CategoryTheory.comp_eqToHom_heq _ _).symm)
      · have targetNotPositive :
            ¬(target.diagram.trace.strands
              (standardTwoThreeBirthOldStrand normalForm left)).orientation =
                .positive := by
          intro targetPositive
          exact leftPositive (leftOrientationEq.symm.trans targetPositive)
        simp only [leftPositive, targetNotPositive, ↓reduceDIte]
        exact
          (CategoryTheory.comp_eqToHom_heq _ _).trans
            ((canonicalNegativePositiveBirth_heq
              𝒞 rightLabelEq).trans
                (CategoryTheory.comp_eqToHom_heq _ _).symm)
  | death left right =>
      have rightLabelEq :=
        standardTwoThreeBirth_oldExteriorStrandLabel
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel right
      have leftOrientationEq :=
        standardTwoThreeBirth_oldStrandOrientation normalForm left
      simp only [compileCutOpenEventMorphism,
        standardTwoThreeBirthOldEvent]
      unfold pairedDeathMorphism
      by_cases leftPositive :
          (source.diagram.trace.strands left).orientation = .positive
      · have targetPositive :
            (target.diagram.trace.strands
              (standardTwoThreeBirthOldStrand normalForm left)).orientation =
                .positive := leftOrientationEq.trans leftPositive
        simp only [leftPositive, targetPositive, ↓reduceDIte]
        exact
          (CategoryTheory.eqToHom_comp_heq _ _).trans
            ((canonicalPositiveNegativeDeath_heq
              𝒞 rightLabelEq).trans
                (CategoryTheory.eqToHom_comp_heq _ _).symm)
      · have targetNotPositive :
            ¬(target.diagram.trace.strands
              (standardTwoThreeBirthOldStrand normalForm left)).orientation =
                .positive := by
          intro targetPositive
          exact leftPositive (leftOrientationEq.symm.trans targetPositive)
        simp only [leftPositive, targetNotPositive, ↓reduceDIte]
        exact
          (CategoryTheory.eqToHom_comp_heq _ _).trans
            ((canonicalNegativePositiveDeath_heq
              𝒞 rightLabelEq).trans
                (CategoryTheory.eqToHom_comp_heq _ _).symm)
  | crossing overInput underInput overOutput underOutput sign =>
      have overInputEq :=
        standardTwoThreeBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel overInput
      have underInputEq :=
        standardTwoThreeBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel underInput
      have overOutputEq :=
        standardTwoThreeBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel overOutput
      have underOutputEq :=
        standardTwoThreeBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel underOutput
      exact
        (compileCrossingMorphism_heq_canonical
          𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (standardTwoThreeBirthOldStrand normalForm overInput)
          (standardTwoThreeBirthOldStrand normalForm underInput)
          (standardTwoThreeBirthOldStrand normalForm overOutput)
          (standardTwoThreeBirthOldStrand normalForm underOutput)
          sign
          (standardTwoThreeBirth_oldEventStrandContinuationsAreWellFormed
            normalForm
            (.crossing overInput underInput
              overOutput underOutput sign)
            pairing)).trans
          ((canonicalCrossingMorphism_heq
            𝒞 overInputEq underInputEq overOutputEq underOutputEq sign
            _ _ _ _).trans
              (compileCrossingMorphism_heq_canonical
                𝒞 source.diagram sourceLabeling
                overInput underInput overOutput underOutput
                sign pairing).symm)
  | framingTwist input output sign =>
      have inputEq :=
        standardTwoThreeBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel input
      have outputEq :=
        standardTwoThreeBirth_oldOrientedExteriorStrand
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel output
      exact
        (compileFramingTwistMorphism_heq_canonical
          𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (standardTwoThreeBirthOldStrand normalForm input)
          (standardTwoThreeBirthOldStrand normalForm output)
          sign
          (standardTwoThreeBirth_oldEventStrandContinuationsAreWellFormed
            normalForm
            (.framingTwist input output sign)
            pairing)).trans
          ((canonicalFramingTwistMorphism_heq
            𝒞 inputEq outputEq sign _ _).trans
              (compileFramingTwistMorphism_heq_canonical
                𝒞 source.diagram sourceLabeling
                input output sign pairing).symm)
  | planarIsotopy continuations =>
      have beforeEq :=
        (congrArg
          (exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel))
          (standardTwoThreeBirth_oldEventBeforeWord normalForm
            (.planarIsotopy continuations))).trans
          (standardTwoThreeBirth_oldExteriorWord
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
            (continuations.map Prod.fst))
      have afterEq :=
        (congrArg
          (exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel))
          (standardTwoThreeBirth_oldEventAfterWord normalForm
            (.planarIsotopy continuations))).trans
          (standardTwoThreeBirth_oldExteriorWord
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
            (continuations.map Prod.snd))
      exact
        (compilePlanarIsotopyMorphism_heq_canonical
          𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (continuations.map fun
              (continuation :
                source.diagram.trace.StrandId ×
                  source.diagram.trace.StrandId) =>
            (standardTwoThreeBirthOldStrand normalForm continuation.1,
              standardTwoThreeBirthOldStrand normalForm continuation.2))
          (standardTwoThreeBirth_oldEventStrandContinuationsAreWellFormed
            normalForm (.planarIsotopy continuations) pairing)).trans
          ((canonicalPlanarIsotopyMorphism_heq
            𝒞 beforeEq afterEq _ _).trans
              (compilePlanarIsotopyMorphism_heq_canonical
                𝒞 source.diagram sourceLabeling
                continuations pairing).symm)
  | projectorHole dotted punctures =>
      have beforeEq :=
        (congrArg
          (exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel))
          (standardTwoThreeBirth_oldEventBeforeWord normalForm
            (.projectorHole dotted punctures))).trans
          (standardTwoThreeBirth_oldExteriorWord
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
            (punctures.map DottedPuncture.inputStrand))
      have afterEq :=
        (congrArg
          (exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel))
          (standardTwoThreeBirth_oldEventAfterWord normalForm
            (.projectorHole dotted punctures))).trans
          (standardTwoThreeBirth_oldExteriorWord
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
            (punctures.map DottedPuncture.outputStrand))
      exact
        (compileProjectorHoleMorphism_heq_canonical
          𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (standardTwoThreeBirthOldComponent normalForm dotted)
          (punctures.map (standardTwoThreeBirthOldPuncture normalForm))
          (standardTwoThreeBirth_oldEventStrandContinuationsAreWellFormed
            normalForm (.projectorHole dotted punctures) pairing)).trans
          ((canonicalProjectorHoleMorphism_heq
            𝒞 beforeEq afterEq _ _).trans
              (compileProjectorHoleMorphism_heq_canonical
                𝒞 source.diagram sourceLabeling
                dotted punctures pairing).symm)

theorem standardTwoThreeBirth_oldStateExteriorWord
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (state : Fin (source.diagram.dottedCuts.exterior.eventCount + 1)) :
    exteriorWord 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (target.diagram.dottedCuts.exterior.activeOrder
          ⟨state.1 + 3, by
            rw [standardTwoThreeBirth_eventCount normalForm]
            omega⟩) =
      exteriorWord 𝒞 source.diagram sourceLabeling
        (source.diagram.dottedCuts.exterior.activeOrder state) := by
  rw [standardTwoThreeBirth_oldActiveOrder normalForm state]
  exact standardTwoThreeBirth_oldExteriorWord
    𝒞 coordinates coordinateBinding normalForm
    sourceLabeling newLabel _

def standardTwoThreeBirthOldEventIndex
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (event : Fin source.dottedCuts.exterior.eventCount) :
    Fin target.dottedCuts.exterior.eventCount :=
  ⟨event.1 + 3, by
    rw [standardTwoThreeBirth_eventCount normalForm]
    omega⟩

theorem standardTwoThreeBirth_oldContexts_of_before_nonempty
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (event : Fin source.dottedCuts.exterior.eventCount)
    (beforeNonempty :
      (source.dottedCuts.exterior.events event).beforeWord ≠ []) :
    eventLeftContext target
          (standardTwoThreeBirthOldEventIndex normalForm event) =
        standardTwoThreeBirthOldStrands normalForm
          (eventLeftContext source event) ∧
      eventRightContext target
          (standardTwoThreeBirthOldEventIndex normalForm event) =
        standardTwoThreeBirthOldStrands normalForm
          (eventRightContext source event) := by
  let targetEvent :=
    standardTwoThreeBirthOldEventIndex normalForm event
  have eventEq :
      target.dottedCuts.exterior.events targetEvent =
        standardTwoThreeBirthOldEvent normalForm
          (source.dottedCuts.exterior.events event) := by
    simpa [targetEvent, standardTwoThreeBirthOldEventIndex] using
      standardTwoThreeBirth_oldEvent normalForm event
  have targetBefore :
      target.dottedCuts.exterior.activeOrder targetEvent.castSucc =
        standardTwoThreeBirthOldStrands normalForm
          (source.dottedCuts.exterior.activeOrder event.castSucc) := by
    simpa [targetEvent, standardTwoThreeBirthOldEventIndex] using
      standardTwoThreeBirth_oldActiveOrder normalForm event.castSucc
  have mappedSourceTransition :
      standardTwoThreeBirthOldStrands normalForm
          (source.dottedCuts.exterior.activeOrder event.castSucc) =
        standardTwoThreeBirthOldStrands normalForm
            (eventLeftContext source event) ++
          (standardTwoThreeBirthOldEvent normalForm
            (source.dottedCuts.exterior.events event)).beforeWord ++
          standardTwoThreeBirthOldStrands normalForm
            (eventRightContext source event) := by
    have mapped :=
      congrArg (standardTwoThreeBirthOldStrands normalForm)
        (eventTransitionEquations source event).1
    simpa [standardTwoThreeBirthOldStrands, List.map_append,
      standardTwoThreeBirth_oldEventBeforeWord] using mapped
  have secondDecomposition :
      target.dottedCuts.exterior.activeOrder targetEvent.castSucc =
        standardTwoThreeBirthOldStrands normalForm
            (eventLeftContext source event) ++
          (target.dottedCuts.exterior.events targetEvent).beforeWord ++
          standardTwoThreeBirthOldStrands normalForm
            (eventRightContext source event) := by
    rw [targetBefore, eventEq]
    exact mappedSourceTransition
  have middleNonempty :
      (target.dottedCuts.exterior.events targetEvent).beforeWord ≠ [] := by
    rw [eventEq, standardTwoThreeBirth_oldEventBeforeWord]
    simpa [standardTwoThreeBirthOldStrands] using beforeNonempty
  exact
    list_context_unique_of_nodup
      (target.dottedCuts.exterior.activeWordsNoDuplicates
        targetEvent.castSucc)
      middleNonempty
      (eventTransitionEquations target targetEvent).1
      secondDecomposition

theorem standardTwoThreeBirth_oldContexts_of_after_nonempty
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (event : Fin source.dottedCuts.exterior.eventCount)
    (afterNonempty :
      (source.dottedCuts.exterior.events event).afterWord ≠ []) :
    eventLeftContext target
          (standardTwoThreeBirthOldEventIndex normalForm event) =
        standardTwoThreeBirthOldStrands normalForm
          (eventLeftContext source event) ∧
      eventRightContext target
          (standardTwoThreeBirthOldEventIndex normalForm event) =
        standardTwoThreeBirthOldStrands normalForm
          (eventRightContext source event) := by
  let targetEvent :=
    standardTwoThreeBirthOldEventIndex normalForm event
  have eventEq :
      target.dottedCuts.exterior.events targetEvent =
        standardTwoThreeBirthOldEvent normalForm
          (source.dottedCuts.exterior.events event) := by
    simpa [targetEvent, standardTwoThreeBirthOldEventIndex] using
      standardTwoThreeBirth_oldEvent normalForm event
  have targetAfter :
      target.dottedCuts.exterior.activeOrder targetEvent.succ =
        standardTwoThreeBirthOldStrands normalForm
          (source.dottedCuts.exterior.activeOrder event.succ) := by
    simpa [targetEvent, standardTwoThreeBirthOldEventIndex] using
      standardTwoThreeBirth_oldActiveOrder normalForm event.succ
  have mappedSourceTransition :
      standardTwoThreeBirthOldStrands normalForm
          (source.dottedCuts.exterior.activeOrder event.succ) =
        standardTwoThreeBirthOldStrands normalForm
            (eventLeftContext source event) ++
          (standardTwoThreeBirthOldEvent normalForm
            (source.dottedCuts.exterior.events event)).afterWord ++
          standardTwoThreeBirthOldStrands normalForm
            (eventRightContext source event) := by
    have mapped :=
      congrArg (standardTwoThreeBirthOldStrands normalForm)
        (eventTransitionEquations source event).2
    simpa [standardTwoThreeBirthOldStrands, List.map_append,
      standardTwoThreeBirth_oldEventAfterWord] using mapped
  have secondDecomposition :
      target.dottedCuts.exterior.activeOrder targetEvent.succ =
        standardTwoThreeBirthOldStrands normalForm
            (eventLeftContext source event) ++
          (target.dottedCuts.exterior.events targetEvent).afterWord ++
          standardTwoThreeBirthOldStrands normalForm
            (eventRightContext source event) := by
    rw [targetAfter, eventEq]
    exact mappedSourceTransition
  have middleNonempty :
      (target.dottedCuts.exterior.events targetEvent).afterWord ≠ [] := by
    rw [eventEq, standardTwoThreeBirth_oldEventAfterWord]
    simpa [standardTwoThreeBirthOldStrands] using afterNonempty
  exact
    list_context_unique_of_nodup
      (target.dottedCuts.exterior.activeWordsNoDuplicates
        targetEvent.succ)
      middleNonempty
      (eventTransitionEquations target targetEvent).2
      secondDecomposition

theorem standardTwoThreeBirth_oldContextualMorphism_of_contexts
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : Fin source.diagram.dottedCuts.exterior.eventCount)
    (contexts :
      eventLeftContext target.diagram
            (standardTwoThreeBirthOldEventIndex normalForm event) =
          standardTwoThreeBirthOldStrands normalForm
            (eventLeftContext source.diagram event) ∧
        eventRightContext target.diagram
            (standardTwoThreeBirthOldEventIndex normalForm event) =
          standardTwoThreeBirthOldStrands normalForm
            (eventRightContext source.diagram event)) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardTwoThreeBirthOldEventIndex normalForm event))
      (compileContextualCutOpenEventMorphism 𝒞 source.diagram
        sourceLabeling event) := by
  let targetEvent :=
    standardTwoThreeBirthOldEventIndex normalForm event
  let sourceEvent :=
    source.diagram.dottedCuts.exterior.events event
  have targetEventEq :
      target.diagram.dottedCuts.exterior.events targetEvent =
        standardTwoThreeBirthOldEvent normalForm sourceEvent := by
    simpa [targetEvent, sourceEvent,
      standardTwoThreeBirthOldEventIndex] using
      standardTwoThreeBirth_oldEvent normalForm event
  have leftEq :
      exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (eventLeftContext target.diagram targetEvent) =
        exteriorWord 𝒞 source.diagram sourceLabeling
          (eventLeftContext source.diagram event) :=
    (congrArg
      (exteriorWord 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel))
      contexts.1).trans
      (standardTwoThreeBirth_oldExteriorWord
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel _)
  have rightEq :
      exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (eventRightContext target.diagram targetEvent) =
        exteriorWord 𝒞 source.diagram sourceLabeling
          (eventRightContext source.diagram event) :=
    (congrArg
      (exteriorWord 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel))
      contexts.2).trans
      (standardTwoThreeBirth_oldExteriorWord
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel _)
  have beforeEq :
      exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.diagram.dottedCuts.exterior.events targetEvent).beforeWord =
        exteriorWord 𝒞 source.diagram sourceLabeling
          sourceEvent.beforeWord := by
    rw [targetEventEq,
      standardTwoThreeBirth_oldEventBeforeWord]
    exact
      standardTwoThreeBirth_oldExteriorWord
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel _
  have afterEq :
      exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.diagram.dottedCuts.exterior.events targetEvent).afterWord =
        exteriorWord 𝒞 source.diagram sourceLabeling
          sourceEvent.afterWord := by
    rw [targetEventEq,
      standardTwoThreeBirth_oldEventAfterWord]
    exact
      standardTwoThreeBirth_oldExteriorWord
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel _
  have targetMapEq :
      HEq
        (compileCutOpenEventMorphism 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.diagram.dottedCuts.exterior.events targetEvent)
          (target.diagram.dottedCuts.exterior.strandContinuationsAreWellFormed targetEvent))
        (compileCutOpenEventMorphism 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (standardTwoThreeBirthOldEvent normalForm sourceEvent)
          (standardTwoThreeBirth_oldEventStrandContinuationsAreWellFormed normalForm
            sourceEvent
            (source.diagram.dottedCuts.exterior.strandContinuationsAreWellFormed event))) := by
    congr!
  have mapEq :
      HEq
        (compileCutOpenEventMorphism 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.diagram.dottedCuts.exterior.events targetEvent)
          (target.diagram.dottedCuts.exterior.strandContinuationsAreWellFormed targetEvent))
        (compileCutOpenEventMorphism 𝒞 source.diagram sourceLabeling
          sourceEvent
          (source.diagram.dottedCuts.exterior.strandContinuationsAreWellFormed event)) :=
    targetMapEq.trans
      (standardTwoThreeBirth_oldEventMorphism
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel sourceEvent
        (source.diagram.dottedCuts.exterior.strandContinuationsAreWellFormed event))
  exact
    (compileContextualCutOpenEventMorphism_heq_core
      𝒞 target.diagram
      (coordinates.mergeLabeling sourceLabeling newLabel)
      targetEvent).trans
      ((contextualizeRibbonMorphism_heq
        𝒞 leftEq beforeEq afterEq rightEq mapEq).trans
        (compileContextualCutOpenEventMorphism_heq_core
          𝒞 source.diagram sourceLabeling event).symm)

theorem standardTwoThreeBirth_oldBirthContextualMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : Fin source.diagram.dottedCuts.exterior.eventCount)
    (left right : source.diagram.trace.StrandId)
    (eventEq :
      source.diagram.dottedCuts.exterior.events event =
        .birth left right) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardTwoThreeBirthOldEventIndex normalForm event))
      (compileContextualCutOpenEventMorphism 𝒞 source.diagram
        sourceLabeling event) := by
  have contexts :=
    standardTwoThreeBirth_oldContexts_of_after_nonempty
      normalForm event (by
        rw [eventEq]
        simp [CutOpenEvent.afterWord])
  exact
    standardTwoThreeBirth_oldContextualMorphism_of_contexts
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel event contexts

theorem standardTwoThreeBirth_oldContextualMorphism_of_before_nonempty
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : Fin source.diagram.dottedCuts.exterior.eventCount)
    (beforeNonempty :
      (source.diagram.dottedCuts.exterior.events event).beforeWord ≠ []) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardTwoThreeBirthOldEventIndex normalForm event))
      (compileContextualCutOpenEventMorphism 𝒞 source.diagram
        sourceLabeling event) := by
  have contexts :=
    standardTwoThreeBirth_oldContexts_of_before_nonempty
      normalForm event beforeNonempty
  exact
    standardTwoThreeBirth_oldContextualMorphism_of_contexts
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel event contexts

theorem standardTwoThreeBirth_oldContextualMorphism_of_after_nonempty
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : Fin source.diagram.dottedCuts.exterior.eventCount)
    (afterNonempty :
      (source.diagram.dottedCuts.exterior.events event).afterWord ≠ []) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardTwoThreeBirthOldEventIndex normalForm event))
      (compileContextualCutOpenEventMorphism 𝒞 source.diagram
        sourceLabeling event) := by
  have contexts :=
    standardTwoThreeBirth_oldContexts_of_after_nonempty
      normalForm event afterNonempty
  exact
    standardTwoThreeBirth_oldContextualMorphism_of_contexts
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel event contexts

theorem standardTwoThreeBirth_oldContextualMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple)
    (event : Fin source.diagram.dottedCuts.exterior.eventCount) :
    HEq
      (compileContextualCutOpenEventMorphism 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        (standardTwoThreeBirthOldEventIndex normalForm event))
      (compileContextualCutOpenEventMorphism 𝒞 source.diagram
        sourceLabeling event) := by
  generalize eventEq :
    source.diagram.dottedCuts.exterior.events event = sourceEvent
  cases sourceEvent with
  | birth left right =>
      apply standardTwoThreeBirth_oldContextualMorphism_of_after_nonempty
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel
      rw [eventEq]
      simp [CutOpenEvent.afterWord]
  | death left right =>
      apply standardTwoThreeBirth_oldContextualMorphism_of_before_nonempty
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel
      rw [eventEq]
      simp [CutOpenEvent.beforeWord]
  | crossing overInput underInput overOutput underOutput sign =>
      apply standardTwoThreeBirth_oldContextualMorphism_of_before_nonempty
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel
      rw [eventEq]
      simp [CutOpenEvent.beforeWord]
  | framingTwist input output sign =>
      apply standardTwoThreeBirth_oldContextualMorphism_of_before_nonempty
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel
      rw [eventEq]
      simp [CutOpenEvent.beforeWord]
  | planarIsotopy continuations =>
      cases continuations with
      | cons continuation rest =>
          apply standardTwoThreeBirth_oldContextualMorphism_of_before_nonempty
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
          rw [eventEq]
          simp [CutOpenEvent.beforeWord]
      | nil =>
          have targetEventEq :=
            standardTwoThreeBirth_oldEvent normalForm event
          rw [eventEq] at targetEventEq
          have targetIdentity :=
            compileContextual_planarNil_heq_identity
              𝒞 target.diagram
              (coordinates.mergeLabeling sourceLabeling newLabel)
              (standardTwoThreeBirthOldEventIndex normalForm event)
              targetEventEq
          have sourceIdentity :=
            compileContextual_planarNil_heq_identity
              𝒞 source.diagram sourceLabeling event eventEq
          have objectEq :
              ribbonWordObject 𝒞
                  (exteriorWord 𝒞 target.diagram
                    (coordinates.mergeLabeling sourceLabeling newLabel)
                    (target.diagram.dottedCuts.exterior.activeOrder
                      (standardTwoThreeBirthOldEventIndex normalForm event).castSucc)) =
                ribbonWordObject 𝒞
                  (exteriorWord 𝒞 source.diagram sourceLabeling
                    (source.diagram.dottedCuts.exterior.activeOrder
                      event.castSucc)) := by
            simpa [standardTwoThreeBirthOldEventIndex] using
              congrArg (ribbonWordObject 𝒞)
                (standardTwoThreeBirth_oldStateExteriorWord
                  𝒞 coordinates coordinateBinding normalForm
                  sourceLabeling newLabel
                  event.castSucc)
          have identityEq :
              HEq
                (𝟙 (ribbonWordObject 𝒞
                  (exteriorWord 𝒞 target.diagram
                    (coordinates.mergeLabeling sourceLabeling newLabel)
                    (target.diagram.dottedCuts.exterior.activeOrder
                      (standardTwoThreeBirthOldEventIndex normalForm event).castSucc))))
                (𝟙 (ribbonWordObject 𝒞
                  (exteriorWord 𝒞 source.diagram sourceLabeling
                    (source.diagram.dottedCuts.exterior.activeOrder
                      event.castSucc)))) := by
            exact identity_heq_of_object_eq objectEq
          exact targetIdentity.trans (identityEq.trans sourceIdentity.symm)
  | projectorHole dotted punctures =>
      cases punctures with
      | cons puncture rest =>
          apply standardTwoThreeBirth_oldContextualMorphism_of_before_nonempty
            𝒞 coordinates coordinateBinding normalForm
            sourceLabeling newLabel
          rw [eventEq]
          simp [CutOpenEvent.beforeWord]
      | nil =>
          have targetEventEq :=
            standardTwoThreeBirth_oldEvent normalForm event
          rw [eventEq] at targetEventEq
          have targetIdentity :=
            compileContextual_projectorNil_heq_identity
              𝒞 target.diagram
              (coordinates.mergeLabeling sourceLabeling newLabel)
              (standardTwoThreeBirthOldEventIndex normalForm event)
              (standardTwoThreeBirthOldComponent normalForm dotted)
              targetEventEq
          have sourceIdentity :=
            compileContextual_projectorNil_heq_identity
              𝒞 source.diagram sourceLabeling event dotted eventEq
          have objectEq :
              ribbonWordObject 𝒞
                  (exteriorWord 𝒞 target.diagram
                    (coordinates.mergeLabeling sourceLabeling newLabel)
                    (target.diagram.dottedCuts.exterior.activeOrder
                      (standardTwoThreeBirthOldEventIndex normalForm event).castSucc)) =
                ribbonWordObject 𝒞
                  (exteriorWord 𝒞 source.diagram sourceLabeling
                    (source.diagram.dottedCuts.exterior.activeOrder
                      event.castSucc)) := by
            simpa [standardTwoThreeBirthOldEventIndex] using
              congrArg (ribbonWordObject 𝒞)
                (standardTwoThreeBirth_oldStateExteriorWord
                  𝒞 coordinates coordinateBinding normalForm
                  sourceLabeling newLabel
                  event.castSucc)
          have identityEq :
              HEq
                (𝟙 (ribbonWordObject 𝒞
                  (exteriorWord 𝒞 target.diagram
                    (coordinates.mergeLabeling sourceLabeling newLabel)
                    (target.diagram.dottedCuts.exterior.activeOrder
                      (standardTwoThreeBirthOldEventIndex normalForm event).castSucc))))
                (𝟙 (ribbonWordObject 𝒞
                  (exteriorWord 𝒞 source.diagram sourceLabeling
                    (source.diagram.dottedCuts.exterior.activeOrder
                      event.castSucc)))) := by
            exact identity_heq_of_object_eq objectEq
          exact targetIdentity.trans (identityEq.trans sourceIdentity.symm)

theorem standardTwoThreeBirth_dropThreeTrace_eq_source
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple) :
    (standardTwoThreeBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).dropThree =
      compiledExteriorTrace 𝒞 source.diagram sourceLabeling := by
  apply FiniteMorphismTrace.eq_of_object_edge
  · intro state
    change
      ribbonWordObject 𝒞
          (exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel)
            (target.diagram.dottedCuts.exterior.activeOrder
              ⟨state.1 + 3, by
                rw [standardTwoThreeBirth_eventCount normalForm]
                omega⟩)) =
        ribbonWordObject 𝒞
          (exteriorWord 𝒞 source.diagram sourceLabeling
            (source.diagram.dottedCuts.exterior.activeOrder state))
    exact congrArg (ribbonWordObject 𝒞)
      (standardTwoThreeBirth_oldStateExteriorWord
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel state)
  · intro event
    change HEq
      (compileContextualCutOpenEventMorphism 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel)
        ⟨event.1 + 3, by
          rw [standardTwoThreeBirth_eventCount normalForm]
          omega⟩)
      (compileContextualCutOpenEventMorphism 𝒞 source.diagram
        sourceLabeling event)
    simpa [standardTwoThreeBirthOldEventIndex] using
      standardTwoThreeBirth_oldContextualMorphism
        𝒞 coordinates coordinateBinding normalForm
        sourceLabeling newLabel event

theorem standardTwoThreeBirth_first_second_component
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    (target.trace.strands
        (twoThreeFirstStrand normalForm)).component =
      (target.trace.strands
        (twoThreeSecondStrand normalForm)).component := by
  apply Fin.ext
  have first :=
    congrArg SerializedStrand.component
      (standardTwoThreeBirth_firstStrandData normalForm)
  have second :=
    congrArg SerializedStrand.component
      (standardTwoThreeBirth_secondStrandData normalForm)
  simpa [serializeStrand] using first.trans second.symm

theorem standardTwoThreeBirth_third_second_component
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    (target.trace.strands
        (twoThreeThirdStrand normalForm)).component =
      (target.trace.strands
        (twoThreeSecondStrand normalForm)).component := by
  apply Fin.ext
  have third :=
    congrArg SerializedStrand.component
      (standardTwoThreeBirth_thirdStrandData normalForm)
  have second :=
    congrArg SerializedStrand.component
      (standardTwoThreeBirth_secondStrandData normalForm)
  simpa [serializeStrand] using third.trans second.symm

theorem standardTwoThreeBirth_first_second_orientation
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    (target.trace.strands
        (twoThreeFirstStrand normalForm)).orientation ≠
      (target.trace.strands
        (twoThreeSecondStrand normalForm)).orientation := by
  have first :=
    congrArg SerializedStrand.orientation
      (standardTwoThreeBirth_firstStrandData normalForm)
  have second :=
    congrArg SerializedStrand.orientation
      (standardTwoThreeBirth_secondStrandData normalForm)
  have first' :
      (target.trace.strands
        (twoThreeFirstStrand normalForm)).orientation =
        .positive := by
    simpa [serializeStrand] using first
  have second' :
      (target.trace.strands
        (twoThreeSecondStrand normalForm)).orientation =
        .negative := by
    simpa [serializeStrand] using second
  rw [first', second']
  decide

theorem standardTwoThreeBirth_third_second_orientation
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    (target.trace.strands
        (twoThreeThirdStrand normalForm)).orientation ≠
      (target.trace.strands
        (twoThreeSecondStrand normalForm)).orientation := by
  have third :=
    congrArg SerializedStrand.orientation
      (standardTwoThreeBirth_thirdStrandData normalForm)
  have second :=
    congrArg SerializedStrand.orientation
      (standardTwoThreeBirth_secondStrandData normalForm)
  have third' :
      (target.trace.strands
        (twoThreeThirdStrand normalForm)).orientation =
        .positive := by
    simpa [serializeStrand] using third
  have second' :
      (target.trace.strands
        (twoThreeSecondStrand normalForm)).orientation =
        .negative := by
    simpa [serializeStrand] using second
  rw [third', second']
  decide

def twoThreeEventIndexZero
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    Fin target.dottedCuts.exterior.eventCount :=
  ⟨0, by
    rw [standardTwoThreeBirth_eventCount normalForm]
    omega⟩

def twoThreeEventIndexOne
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    Fin target.dottedCuts.exterior.eventCount :=
  ⟨1, by
    rw [standardTwoThreeBirth_eventCount normalForm]
    omega⟩

def twoThreeEventIndexTwo
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    Fin target.dottedCuts.exterior.eventCount :=
  ⟨2, by
    rw [standardTwoThreeBirth_eventCount normalForm]
    omega⟩

theorem standardTwoThreeBirth_firstContextsEmpty
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    eventLeftContext target (twoThreeEventIndexZero normalForm) = [] ∧
      eventRightContext target (twoThreeEventIndexZero normalForm) = [] := by
  let i := twoThreeEventIndexZero normalForm
  have eventEq :
      target.dottedCuts.exterior.events i =
        .birth
          (twoThreeFirstStrand normalForm)
          (twoThreeSecondStrand normalForm) := by
    simpa [i, twoThreeEventIndexZero] using
      standardTwoThreeBirth_eventZero_eq normalForm
  have beforeEq :
      target.dottedCuts.exterior.activeOrder i.castSucc = [] := by
    simpa [i, twoThreeEventIndexZero] using
      standardTwoThreeBirth_stateZero normalForm
  have transition := (eventTransitionEquations target i).1
  rw [beforeEq, eventEq] at transition
  simp [CutOpenEvent.beforeWord] at transition
  exact transition

theorem standardTwoThreeBirth_thirdContextsEmpty
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    eventLeftContext target (twoThreeEventIndexTwo normalForm) = [] ∧
      eventRightContext target (twoThreeEventIndexTwo normalForm) = [] := by
  let i := twoThreeEventIndexTwo normalForm
  have eventEq :
      target.dottedCuts.exterior.events i =
        .death
          (twoThreeThirdStrand normalForm)
          (twoThreeSecondStrand normalForm) := by
    simpa [i, twoThreeEventIndexTwo] using
      standardTwoThreeBirth_eventTwo_eq normalForm
  have afterEq :
      target.dottedCuts.exterior.activeOrder i.succ = [] := by
    simpa [i, twoThreeEventIndexTwo] using
      standardTwoThreeBirth_stateThree normalForm
  have transition := (eventTransitionEquations target i).2
  rw [afterEq, eventEq] at transition
  simp [CutOpenEvent.afterWord] at transition
  exact transition

theorem standardTwoThreeBirth_firstContextualEdge
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (labeling : TwoHandleLabeling 𝒞 target) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardTwoThreeBirth_stateZero normalForm)).symm ≫
      compileContextualCutOpenEventMorphism 𝒞 target labeling
        (twoThreeEventIndexZero normalForm) ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardTwoThreeBirth_stateOne normalForm)) =
      pairedBirthMorphism 𝒞 target labeling
        (twoThreeFirstStrand normalForm)
        (twoThreeSecondStrand normalForm)
        (standardTwoThreeBirth_first_second_component normalForm)
        (standardTwoThreeBirth_first_second_orientation normalForm) := by
  let i := twoThreeEventIndexZero normalForm
  have eventEq :
      target.dottedCuts.exterior.events i =
        .birth
          (twoThreeFirstStrand normalForm)
          (twoThreeSecondStrand normalForm) := by
    simpa [i, twoThreeEventIndexZero] using
      standardTwoThreeBirth_eventZero_eq normalForm
  have beforeEq :
      target.dottedCuts.exterior.activeOrder i.castSucc = [] := by
    simpa [i, twoThreeEventIndexZero] using
      standardTwoThreeBirth_stateZero normalForm
  have afterEq :
      target.dottedCuts.exterior.activeOrder i.succ =
        [twoThreeFirstStrand normalForm,
          twoThreeSecondStrand normalForm] := by
    simpa [i, twoThreeEventIndexZero] using
      standardTwoThreeBirth_stateOne normalForm
  have contexts := standardTwoThreeBirth_firstContextsEmpty normalForm
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  simpa using
    (compileContextualFromWitness_eq_birth
      𝒞 target labeling
      (target.dottedCuts.exterior.events i)
      (twoThreeFirstStrand normalForm)
      (twoThreeSecondStrand normalForm)
      (target.dottedCuts.exterior.activeOrder i.castSucc)
      (target.dottedCuts.exterior.activeOrder i.succ)
      (eventLeftContext target i)
      (eventRightContext target i)
      (eventTransitionEquations target i).1
      (eventTransitionEquations target i).2
      (target.dottedCuts.exterior.strandContinuationsAreWellFormed i)
      eventEq beforeEq afterEq contexts.1 contexts.2)

theorem standardTwoThreeBirth_thirdContextualEdge
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (labeling : TwoHandleLabeling 𝒞 target) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardTwoThreeBirth_stateTwo normalForm)).symm ≫
      compileContextualCutOpenEventMorphism 𝒞 target labeling
        (twoThreeEventIndexTwo normalForm) ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardTwoThreeBirth_stateThree normalForm)) =
      pairedDeathMorphism 𝒞 target labeling
        (twoThreeThirdStrand normalForm)
        (twoThreeSecondStrand normalForm)
        (standardTwoThreeBirth_third_second_component normalForm)
        (standardTwoThreeBirth_third_second_orientation normalForm) := by
  let i := twoThreeEventIndexTwo normalForm
  have eventEq :
      target.dottedCuts.exterior.events i =
        .death
          (twoThreeThirdStrand normalForm)
          (twoThreeSecondStrand normalForm) := by
    simpa [i, twoThreeEventIndexTwo] using
      standardTwoThreeBirth_eventTwo_eq normalForm
  have beforeEq :
      target.dottedCuts.exterior.activeOrder i.castSucc =
        [twoThreeThirdStrand normalForm,
          twoThreeSecondStrand normalForm] := by
    simpa [i, twoThreeEventIndexTwo] using
      standardTwoThreeBirth_stateTwo normalForm
  have afterEq :
      target.dottedCuts.exterior.activeOrder i.succ = [] := by
    simpa [i, twoThreeEventIndexTwo] using
      standardTwoThreeBirth_stateThree normalForm
  have contexts := standardTwoThreeBirth_thirdContextsEmpty normalForm
  rw [compileContextualCutOpenEventMorphism_eq_fromWitness]
  simpa using
    (compileContextualFromWitness_eq_death
      𝒞 target labeling
      (target.dottedCuts.exterior.events i)
      (twoThreeThirdStrand normalForm)
      (twoThreeSecondStrand normalForm)
      (target.dottedCuts.exterior.activeOrder i.castSucc)
      (target.dottedCuts.exterior.activeOrder i.succ)
      (eventLeftContext target i)
      (eventRightContext target i)
      (eventTransitionEquations target i).1
      (eventTransitionEquations target i).2
      (target.dottedCuts.exterior.strandContinuationsAreWellFormed i)
      eventEq beforeEq afterEq contexts.1 contexts.2)

theorem standardTwoThreeBirth_secondContexts
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target) :
    eventLeftContext target (twoThreeEventIndexOne normalForm) = [] ∧
      eventRightContext target (twoThreeEventIndexOne normalForm) =
        [twoThreeSecondStrand normalForm] := by
  let i := twoThreeEventIndexOne normalForm
  let left := eventLeftContext target i
  let right := eventRightContext target i
  have beforeTransition := (eventTransitionEquations target i).1
  have activeBefore :
      target.dottedCuts.exterior.activeOrder i.castSucc =
        [twoThreeFirstStrand normalForm,
          twoThreeSecondStrand normalForm] := by
    simpa [i, twoThreeEventIndexOne] using
      standardTwoThreeBirth_stateOne normalForm
  rw [activeBefore] at beforeTransition
  have eventAt :
      target.dottedCuts.exterior.events i =
        .framingTwist
          (twoThreeFirstStrand normalForm)
          (twoThreeThirdStrand normalForm)
          .positive := by
    simpa [i, twoThreeEventIndexOne] using
      standardTwoThreeBirth_eventOne_eq normalForm
  have eventBefore :
      (target.dottedCuts.exterior.events i).beforeWord =
        [twoThreeFirstStrand normalForm] := by
    rw [eventAt]
    rfl
  rw [eventBefore] at beforeTransition
  change
    [twoThreeFirstStrand normalForm,
        twoThreeSecondStrand normalForm] =
      left ++ [twoThreeFirstStrand normalForm] ++ right
    at beforeTransition
  have lengthEquation : left.length + right.length = 1 := by
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
    have rightLengthZero : right.length = 0 := by omega
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
        twoThreeSecondStrand normalForm =
          twoThreeFirstStrand normalForm :=
      (List.cons.inj (List.cons.inj beforeTransition).2).1
    have values := congrArg Fin.val impossible
    simp [twoThreeFirstStrand, twoThreeSecondStrand] at values

theorem compileCutOpenEventMorphism_heq_of_event_eq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    {event replacement : CutOpenEvent diagram.trace}
    (eventEq : event = replacement)
    (pairing : event.StrandContinuationsAreWellFormed) :
    HEq
      (compileCutOpenEventMorphism 𝒞 diagram labeling event pairing)
      (compileCutOpenEventMorphism 𝒞 diagram labeling replacement
        (eventEq ▸ pairing)) := by
  subst replacement
  rfl

theorem standardTwoThreeBirth_secondContextualEdge
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (labeling : TwoHandleLabeling 𝒞 target) :
    eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardTwoThreeBirth_stateOne normalForm)).symm ≫
      compileContextualCutOpenEventMorphism 𝒞 target labeling
        (twoThreeEventIndexOne normalForm) ≫
      eqToHom
        (congrArg
          (fun word =>
            ribbonWordObject 𝒞
              (exteriorWord 𝒞 target labeling word))
          (standardTwoThreeBirth_stateTwo normalForm)) =
      contextualizeRibbonMorphism 𝒞
        []
        (exteriorWord 𝒞 target labeling
          [twoThreeFirstStrand normalForm])
        (exteriorWord 𝒞 target labeling
          [twoThreeThirdStrand normalForm])
        (exteriorWord 𝒞 target labeling
          [twoThreeSecondStrand normalForm])
        (compileCutOpenEventMorphism 𝒞 target labeling
          (.framingTwist
            (twoThreeFirstStrand normalForm)
            (twoThreeThirdStrand normalForm)
            .positive)
          ((standardTwoThreeBirth_eventOne_eq normalForm) ▸
            target.dottedCuts.exterior.strandContinuationsAreWellFormed
              (twoThreeEventIndexOne normalForm))) := by
  let i := twoThreeEventIndexOne normalForm
  have eventEq :
      target.dottedCuts.exterior.events i =
        .framingTwist
          (twoThreeFirstStrand normalForm)
          (twoThreeThirdStrand normalForm)
          .positive := by
    simpa [i, twoThreeEventIndexOne] using
      standardTwoThreeBirth_eventOne_eq normalForm
  have beforeEq :
      target.dottedCuts.exterior.activeOrder i.castSucc =
        [twoThreeFirstStrand normalForm,
          twoThreeSecondStrand normalForm] := by
    simpa [i, twoThreeEventIndexOne] using
      standardTwoThreeBirth_stateOne normalForm
  have afterEq :
      target.dottedCuts.exterior.activeOrder i.succ =
        [twoThreeThirdStrand normalForm,
          twoThreeSecondStrand normalForm] := by
    simpa [i, twoThreeEventIndexOne] using
      standardTwoThreeBirth_stateTwo normalForm
  have contexts := standardTwoThreeBirth_secondContexts normalForm
  have leftWordEq :
      exteriorWord 𝒞 target labeling (eventLeftContext target i) = [] := by
    rw [contexts.1]
    rfl
  have beforeWordEq :
      exteriorWord 𝒞 target labeling
          (target.dottedCuts.exterior.events i).beforeWord =
        exteriorWord 𝒞 target labeling
          [twoThreeFirstStrand normalForm] := by
    exact congrArg (exteriorWord 𝒞 target labeling)
      (congrArg CutOpenEvent.beforeWord eventEq)
  have afterWordEq :
      exteriorWord 𝒞 target labeling
          (target.dottedCuts.exterior.events i).afterWord =
        exteriorWord 𝒞 target labeling
          [twoThreeThirdStrand normalForm] := by
    exact congrArg (exteriorWord 𝒞 target labeling)
      (congrArg CutOpenEvent.afterWord eventEq)
  have rightWordEq :
      exteriorWord 𝒞 target labeling (eventRightContext target i) =
        exteriorWord 𝒞 target labeling
          [twoThreeSecondStrand normalForm] := by
    rw [contexts.2]
  have eventMorphism :
      HEq
        (compileCutOpenEventMorphism 𝒞 target labeling
          (target.dottedCuts.exterior.events i)
          (target.dottedCuts.exterior.strandContinuationsAreWellFormed i))
        (compileCutOpenEventMorphism 𝒞 target labeling
          (.framingTwist
            (twoThreeFirstStrand normalForm)
            (twoThreeThirdStrand normalForm)
            .positive)
          (eventEq ▸
            target.dottedCuts.exterior.strandContinuationsAreWellFormed i)) := by
    exact
      compileCutOpenEventMorphism_heq_of_event_eq
        𝒞 target labeling eventEq
        (target.dottedCuts.exterior.strandContinuationsAreWellFormed i)
  have compiledContext :
      HEq
        (compileContextualCutOpenEventMorphism 𝒞 target labeling i)
        (contextualizeRibbonMorphism 𝒞
          []
          (exteriorWord 𝒞 target labeling
            [twoThreeFirstStrand normalForm])
          (exteriorWord 𝒞 target labeling
            [twoThreeThirdStrand normalForm])
          (exteriorWord 𝒞 target labeling
            [twoThreeSecondStrand normalForm])
          (compileCutOpenEventMorphism 𝒞 target labeling
            (.framingTwist
              (twoThreeFirstStrand normalForm)
              (twoThreeThirdStrand normalForm)
              .positive)
            (eventEq ▸
              target.dottedCuts.exterior.strandContinuationsAreWellFormed i))) :=
    (compileContextualCutOpenEventMorphism_heq_core
      𝒞 target labeling i).trans
      (contextualizeRibbonMorphism_heq 𝒞
        leftWordEq beforeWordEq afterWordEq rightWordEq eventMorphism)
  have strip :=
    transport_sandwich_heq
      (congrArg
        (fun word =>
          ribbonWordObject 𝒞
            (exteriorWord 𝒞 target labeling word))
        (standardTwoThreeBirth_stateOne normalForm)).symm
      (congrArg
        (fun word =>
          ribbonWordObject 𝒞
            (exteriorWord 𝒞 target labeling word))
        (standardTwoThreeBirth_stateTwo normalForm))
      (compileContextualCutOpenEventMorphism 𝒞 target labeling i)
  exact eq_of_heq (strip.trans compiledContext)

theorem canonicalPositiveFramedLoop_eq_ribbonTrace
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (simple : 𝒞.simples.Simple) :
    canonicalPositiveNegativeBirth 𝒞 simple ≫
        contextualizeRibbonMorphism 𝒞
          []
          [{ label := simple, direction := .forward }]
          [{ label := simple, direction := .forward }]
          [{ label := simple, direction := .dual }]
          (canonicalFramingTwistMorphism 𝒞
            { label := simple, direction := .forward }
            { label := simple, direction := .forward }
            .positive rfl) ≫
        canonicalPositiveNegativeDeath 𝒞 simple =
      ribbonTraceMorphism 𝒞 simple
        (𝟙 (𝒞.simples.simpleObject simple)) := by
  let X := 𝒞.simples.simpleObject simple
  calc
    _ =
        (η_ X (Xᘁ)) ≫
          ((𝒞.ribbon.twist.hom.app X ▷ Xᘁ) ≫
            (β_ X (Xᘁ)).hom) ≫
          (ε_ X (Xᘁ)) := by
      simp [X, canonicalPositiveNegativeBirth,
        canonicalPositiveNegativeDeath, contextualizeRibbonMorphism,
        canonicalFramingTwistMorphism, ribbonWordObject,
        ribbonWordAppendIso, orientedSimpleObject,
        -BraidedCategory.braiding_naturality,
        -BraidedCategory.braiding_naturality_assoc,
        -BraidedCategory.braiding_naturality_left,
        -BraidedCategory.braiding_naturality_left_assoc]
      monoidal
    _ =
        (η_ X (Xᘁ)) ≫
          ((β_ X (Xᘁ)).hom ≫
            (Xᘁ ◁ 𝒞.ribbon.twist.hom.app X)) ≫
          (ε_ X (Xᘁ)) := by
      exact congrArg
        (fun middle => (η_ X (Xᘁ)) ≫ middle ≫ (ε_ X (Xᘁ)))
        (BraidedCategory.braiding_naturality_left
          (𝒞.ribbon.twist.hom.app X) (Xᘁ))
    _ = _ := by
      simp [X, ribbonTraceMorphism]

theorem canonicalFramingTwistMorphism_heq_of_oriented_eq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {before₁ before₂ after₁ after₂ : OrientedSimple 𝒞}
    (beforeEq : before₁ = before₂)
    (afterEq : after₁ = after₂)
    (sign : CrossingSign)
    (outputEq₁ : before₁ = after₁)
    (outputEq₂ : before₂ = after₂) :
    HEq
      (canonicalFramingTwistMorphism 𝒞
        before₁ after₁ sign outputEq₁)
      (canonicalFramingTwistMorphism 𝒞
        before₂ after₂ sign outputEq₂) := by
  subst before₂
  subst after₂
  rfl

theorem standardTwoThreeBirth_localThreeEventMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (labeling : TwoHandleLabeling 𝒞 target)
    (pairing :
      (CutOpenEvent.framingTwist
        (twoThreeFirstStrand normalForm)
        (twoThreeThirdStrand normalForm)
        .positive).StrandContinuationsAreWellFormed) :
    pairedBirthMorphism 𝒞 target labeling
          (twoThreeFirstStrand normalForm)
          (twoThreeSecondStrand normalForm)
          (standardTwoThreeBirth_first_second_component normalForm)
          (standardTwoThreeBirth_first_second_orientation normalForm) ≫
        contextualizeRibbonMorphism 𝒞
          []
          (exteriorWord 𝒞 target labeling
            [twoThreeFirstStrand normalForm])
          (exteriorWord 𝒞 target labeling
            [twoThreeThirdStrand normalForm])
          (exteriorWord 𝒞 target labeling
            [twoThreeSecondStrand normalForm])
          (compileCutOpenEventMorphism 𝒞 target labeling
            (.framingTwist
              (twoThreeFirstStrand normalForm)
              (twoThreeThirdStrand normalForm)
              .positive)
            pairing) ≫
        pairedDeathMorphism 𝒞 target labeling
          (twoThreeThirdStrand normalForm)
          (twoThreeSecondStrand normalForm)
          (standardTwoThreeBirth_third_second_component normalForm)
          (standardTwoThreeBirth_third_second_orientation normalForm) =
      ribbonTraceMorphism 𝒞
        (exteriorStrandLabel 𝒞 target labeling
          (twoThreeFirstStrand normalForm))
        (𝟙 (𝒞.simples.simpleObject
          (exteriorStrandLabel 𝒞 target labeling
            (twoThreeFirstStrand normalForm)))) := by
  have firstOrientation :=
    congrArg SerializedStrand.orientation
      (standardTwoThreeBirth_firstStrandData normalForm)
  have secondOrientation :=
    congrArg SerializedStrand.orientation
      (standardTwoThreeBirth_secondStrandData normalForm)
  have thirdOrientation :=
    congrArg SerializedStrand.orientation
      (standardTwoThreeBirth_thirdStrandData normalForm)
  have firstPositive :
      (target.trace.strands
        (twoThreeFirstStrand normalForm)).orientation = .positive := by
    simpa [serializeStrand] using firstOrientation
  have secondNegative :
      (target.trace.strands
        (twoThreeSecondStrand normalForm)).orientation = .negative := by
    simpa [serializeStrand] using secondOrientation
  have thirdPositive :
      (target.trace.strands
        (twoThreeThirdStrand normalForm)).orientation = .positive := by
    simpa [serializeStrand] using thirdOrientation
  have firstThirdComponent :
      (target.trace.strands
        (twoThreeFirstStrand normalForm)).component =
      (target.trace.strands
        (twoThreeThirdStrand normalForm)).component :=
    (standardTwoThreeBirth_first_second_component normalForm).trans
      (standardTwoThreeBirth_third_second_component normalForm).symm
  have firstThirdLabel :
      exteriorStrandLabel 𝒞 target labeling
          (twoThreeFirstStrand normalForm) =
        exteriorStrandLabel 𝒞 target labeling
          (twoThreeThirdStrand normalForm) :=
    exteriorStrandLabel_eq_of_component_eq
      𝒞 target labeling firstThirdComponent
  have firstSecondLabel :
      exteriorStrandLabel 𝒞 target labeling
          (twoThreeFirstStrand normalForm) =
        exteriorStrandLabel 𝒞 target labeling
          (twoThreeSecondStrand normalForm) :=
    exteriorStrandLabel_eq_of_component_eq
      𝒞 target labeling
        (standardTwoThreeBirth_first_second_component normalForm)
  have thirdSecondLabel :
      exteriorStrandLabel 𝒞 target labeling
          (twoThreeThirdStrand normalForm) =
        exteriorStrandLabel 𝒞 target labeling
          (twoThreeSecondStrand normalForm) :=
    exteriorStrandLabel_eq_of_component_eq
      𝒞 target labeling
        (standardTwoThreeBirth_third_second_component normalForm)
  let canonicalForward : OrientedSimple 𝒞 :=
    { label :=
        exteriorStrandLabel 𝒞 target labeling
          (twoThreeSecondStrand normalForm),
      direction := .forward }
  let canonicalDual : OrientedSimple 𝒞 :=
    { label :=
        exteriorStrandLabel 𝒞 target labeling
          (twoThreeSecondStrand normalForm),
      direction := .dual }
  let canonicalBefore : RibbonWord 𝒞 := [canonicalForward]
  let canonicalRight : RibbonWord 𝒞 := [canonicalDual]
  have birthBinding :
      positiveNegativeDualPairWord 𝒞
          (exteriorStrandLabel 𝒞 target labeling
            (twoThreeSecondStrand normalForm)) =
        exteriorWord 𝒞 target labeling
          [twoThreeFirstStrand normalForm,
            twoThreeSecondStrand normalForm] := by
    exact positiveNegativeDualPairWord_eq_exteriorWord
      𝒞 target labeling
      (twoThreeFirstStrand normalForm)
      (twoThreeSecondStrand normalForm)
      (standardTwoThreeBirth_first_second_component normalForm)
      firstPositive secondNegative
  have deathBinding :
      positiveNegativeDualPairWord 𝒞
          (exteriorStrandLabel 𝒞 target labeling
            (twoThreeSecondStrand normalForm)) =
        exteriorWord 𝒞 target labeling
          [twoThreeThirdStrand normalForm,
            twoThreeSecondStrand normalForm] := by
    exact positiveNegativeDualPairWord_eq_exteriorWord
      𝒞 target labeling
      (twoThreeThirdStrand normalForm)
      (twoThreeSecondStrand normalForm)
      (standardTwoThreeBirth_third_second_component normalForm)
      thirdPositive secondNegative
  have beforeCanonical :
      exteriorWord 𝒞 target labeling
          [twoThreeFirstStrand normalForm] =
        canonicalBefore := by
    simp [canonicalBefore, canonicalForward, exteriorWord,
      orientedExteriorStrand, ribbonDirectionOfStrandOrientation,
      firstPositive, firstSecondLabel]
  have afterCanonical :
      exteriorWord 𝒞 target labeling
          [twoThreeThirdStrand normalForm] =
        canonicalBefore := by
    simp [canonicalBefore, canonicalForward, exteriorWord,
      orientedExteriorStrand, ribbonDirectionOfStrandOrientation,
      thirdPositive, thirdSecondLabel]
  have rightCanonical :
      exteriorWord 𝒞 target labeling
          [twoThreeSecondStrand normalForm] =
        canonicalRight := by
    simp [canonicalRight, canonicalDual, exteriorWord,
      orientedExteriorStrand, ribbonDirectionOfStrandOrientation,
      secondNegative]
  have firstCanonical :
      orientedExteriorStrand 𝒞 target labeling
          (twoThreeFirstStrand normalForm) =
        canonicalForward := by
    simp [canonicalForward, orientedExteriorStrand,
      ribbonDirectionOfStrandOrientation, firstPositive,
      firstSecondLabel]
  have thirdCanonical :
      orientedExteriorStrand 𝒞 target labeling
          (twoThreeThirdStrand normalForm) =
        canonicalForward := by
    simp [canonicalForward, orientedExteriorStrand,
      ribbonDirectionOfStrandOrientation, thirdPositive,
      thirdSecondLabel]
  have framingHEq :
      HEq
        (compileCutOpenEventMorphism 𝒞 target labeling
          (.framingTwist
            (twoThreeFirstStrand normalForm)
            (twoThreeThirdStrand normalForm)
            .positive)
          pairing)
        (canonicalFramingTwistMorphism 𝒞
          canonicalForward canonicalForward .positive rfl) := by
    have compiled :=
      compileFramingTwistMorphism_heq_canonical
        𝒞 target labeling
        (twoThreeFirstStrand normalForm)
        (twoThreeThirdStrand normalForm)
        .positive pairing
    exact compiled.trans
      (canonicalFramingTwistMorphism_heq_of_oriented_eq
        𝒞 firstCanonical thirdCanonical .positive _ rfl)
  have contextHEq :
      HEq
        (contextualizeRibbonMorphism 𝒞
          []
          (exteriorWord 𝒞 target labeling
            [twoThreeFirstStrand normalForm])
          (exteriorWord 𝒞 target labeling
            [twoThreeThirdStrand normalForm])
          (exteriorWord 𝒞 target labeling
            [twoThreeSecondStrand normalForm])
          (compileCutOpenEventMorphism 𝒞 target labeling
            (.framingTwist
              (twoThreeFirstStrand normalForm)
              (twoThreeThirdStrand normalForm)
              .positive)
            pairing))
        (contextualizeRibbonMorphism 𝒞
          [] canonicalBefore canonicalBefore canonicalRight
          (canonicalFramingTwistMorphism 𝒞
            canonicalForward canonicalForward .positive rfl)) :=
    contextualizeRibbonMorphism_heq 𝒞
      rfl beforeCanonical afterCanonical rightCanonical framingHEq
  have birthHEq :
      HEq
        (pairedBirthMorphism 𝒞 target labeling
          (twoThreeFirstStrand normalForm)
          (twoThreeSecondStrand normalForm)
          (standardTwoThreeBirth_first_second_component normalForm)
          (standardTwoThreeBirth_first_second_orientation normalForm))
        (canonicalPositiveNegativeBirth 𝒞
          (exteriorStrandLabel 𝒞 target labeling
            (twoThreeSecondStrand normalForm))) := by
    simp [pairedBirthMorphism, firstPositive, birthBinding]
  have deathHEq :
      HEq
        (pairedDeathMorphism 𝒞 target labeling
          (twoThreeThirdStrand normalForm)
          (twoThreeSecondStrand normalForm)
          (standardTwoThreeBirth_third_second_component normalForm)
          (standardTwoThreeBirth_third_second_orientation normalForm))
        (canonicalPositiveNegativeDeath 𝒞
          (exteriorStrandLabel 𝒞 target labeling
            (twoThreeSecondStrand normalForm))) := by
    simp [pairedDeathMorphism, thirdPositive, deathBinding]
  have birthContextHEq :=
    CategoryTheory.heq_comp
      rfl
      (congrArg (ribbonWordObject 𝒞) birthBinding.symm)
      (congrArg (ribbonWordObject 𝒞) deathBinding.symm)
      birthHEq contextHEq
  have wholeHEq :=
    CategoryTheory.heq_comp
      rfl
      (congrArg (ribbonWordObject 𝒞) deathBinding.symm)
      rfl
      birthContextHEq deathHEq
  have canonicalValue :=
    canonicalPositiveFramedLoop_eq_ribbonTrace 𝒞
      (exteriorStrandLabel 𝒞 target labeling
        (twoThreeSecondStrand normalForm))
  have traceEq :
      ribbonTraceMorphism 𝒞
          (exteriorStrandLabel 𝒞 target labeling
            (twoThreeSecondStrand normalForm))
          (𝟙 (𝒞.simples.simpleObject
            (exteriorStrandLabel 𝒞 target labeling
              (twoThreeSecondStrand normalForm)))) =
        ribbonTraceMorphism 𝒞
          (exteriorStrandLabel 𝒞 target labeling
            (twoThreeFirstStrand normalForm))
          (𝟙 (𝒞.simples.simpleObject
            (exteriorStrandLabel 𝒞 target labeling
              (twoThreeFirstStrand normalForm)))) := by
    rw [firstSecondLabel]
  have canonicalValue' :
      (canonicalPositiveNegativeBirth 𝒞
            (exteriorStrandLabel 𝒞 target labeling
              (twoThreeSecondStrand normalForm)) ≫
          contextualizeRibbonMorphism 𝒞
            [] canonicalBefore canonicalBefore canonicalRight
            (canonicalFramingTwistMorphism 𝒞
              canonicalForward canonicalForward .positive rfl)) ≫
        canonicalPositiveNegativeDeath 𝒞
          (exteriorStrandLabel 𝒞 target labeling
            (twoThreeSecondStrand normalForm)) =
      ribbonTraceMorphism 𝒞
        (exteriorStrandLabel 𝒞 target labeling
          (twoThreeFirstStrand normalForm))
        (𝟙 (𝒞.simples.simpleObject
          (exteriorStrandLabel 𝒞 target labeling
            (twoThreeFirstStrand normalForm)))) := by
    simpa [canonicalBefore, canonicalRight, canonicalForward,
      canonicalDual] using canonicalValue.trans traceEq
  simpa only [Category.assoc] using
    (eq_of_heq wholeHEq).trans canonicalValue'

theorem standardTwoThreeBirth_prefixThreeMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : CombinatorialSpecialKirbyDiagram}
    (normalForm : IsStandardTwoThreeBirth source target)
    (labeling : TwoHandleLabeling 𝒞 target) :
    HEq
      ((standardTwoThreeBirthTargetTrace 𝒞 normalForm labeling).composePrefix
        3 (by omega))
      (ribbonTraceMorphism 𝒞
        (exteriorStrandLabel 𝒞 target labeling
          (twoThreeFirstStrand normalForm))
        (𝟙 (𝒞.simples.simpleObject
          (exteriorStrandLabel 𝒞 target labeling
            (twoThreeFirstStrand normalForm))))) := by
  have castPrefix :=
    FiniteMorphismTrace.castEventCount_composePrefix
      (standardTwoThreeBirth_eventCount normalForm).symm
      (compiledExteriorTrace 𝒞 target labeling)
      3 (by omega) (by
        rw [standardTwoThreeBirth_eventCount normalForm]
        omega)
  have localMorphism :=
    standardTwoThreeBirth_localThreeEventMorphism
      𝒞 normalForm labeling
      ((standardTwoThreeBirth_eventOne_eq normalForm) ▸
        target.dottedCuts.exterior.strandContinuationsAreWellFormed
          (twoThreeEventIndexOne normalForm))
  have first :=
    standardTwoThreeBirth_firstContextualEdge
      𝒞 normalForm labeling
  have second :=
    standardTwoThreeBirth_secondContextualEdge
      𝒞 normalForm labeling
  have third :=
    standardTwoThreeBirth_thirdContextualEdge
      𝒞 normalForm labeling
  have assembled :=
    congrArg₂ (fun f g => f ≫ g) first
      (congrArg₂ (fun f g => f ≫ g) second third)
  simp only [Category.assoc] at assembled localMorphism
  have assembledValue := assembled.trans localMorphism
  apply castPrefix.trans
  simp only [FiniteMorphismTrace.composePrefix,
    compiledExteriorTrace, Category.id_comp]
  apply middle_heq_of_transport_sandwich_eq
  simpa [twoThreeEventIndexZero, twoThreeEventIndexOne,
    twoThreeEventIndexTwo, Category.assoc] using assembledValue

theorem standardTwoThreeBirth_targetTraceMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple) :
    HEq
      ((standardTwoThreeBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).composeAll)
      (ribbonTraceMorphism 𝒞
          (exteriorStrandLabel 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel)
            (twoThreeFirstStrand normalForm))
          (𝟙 (𝒞.simples.simpleObject
            (exteriorStrandLabel 𝒞 target.diagram
              (coordinates.mergeLabeling sourceLabeling newLabel)
              (twoThreeFirstStrand normalForm)))) ≫
        compiledExteriorTraceFromUnit
          𝒞 source.diagram sourceLabeling) := by
  have threeBound :
      3 ≤ source.diagram.dottedCuts.exterior.eventCount + 3 := by
    omega
  have prefixMorphism :
      HEq
        ((standardTwoThreeBirthTargetTrace 𝒞 normalForm
          (coordinates.mergeLabeling sourceLabeling newLabel)).composePrefix
            3 threeBound)
        (ribbonTraceMorphism 𝒞
          (exteriorStrandLabel 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel)
            (twoThreeFirstStrand normalForm))
          (𝟙 (𝒞.simples.simpleObject
            (exteriorStrandLabel 𝒞 target.diagram
              (coordinates.mergeLabeling sourceLabeling newLabel)
              (twoThreeFirstStrand normalForm))))) :=
    standardTwoThreeBirth_prefixThreeMorphism
      𝒞 normalForm (coordinates.mergeLabeling sourceLabeling newLabel)
  have tracesEq :
      (standardTwoThreeBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).dropThree =
          compiledExteriorTrace 𝒞 source.diagram sourceLabeling :=
    standardTwoThreeBirth_dropThreeTrace_eq_source
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel
  have suffixRaw :
      HEq
        ((standardTwoThreeBirthTargetTrace 𝒞 normalForm
          (coordinates.mergeLabeling sourceLabeling newLabel)).dropThree.composeAll)
        ((compiledExteriorTrace 𝒞 source.diagram sourceLabeling).composeAll) := by
    rw [tracesEq]
  have suffix :
      HEq
        ((standardTwoThreeBirthTargetTrace 𝒞 normalForm
          (coordinates.mergeLabeling sourceLabeling newLabel)).dropThree.composeAll)
        (compiledExteriorTraceFromUnit
          𝒞 source.diagram sourceLabeling) :=
    suffixRaw.trans (CategoryTheory.eqToHom_comp_heq _ _).symm
  have sourceObjectEq :
      (standardTwoThreeBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).object 0 =
          𝟙_ 𝒞.C := by
    change ribbonWordObject 𝒞
        (exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.diagram.dottedCuts.exterior.activeOrder 0)) =
      𝟙_ 𝒞.C
    rw [target.diagram.dottedCuts.exterior.initialBoundaryEmpty]
    rfl
  have middleObjectEq :
      (standardTwoThreeBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).object
          ⟨3, by omega⟩ =
        𝟙_ 𝒞.C := by
    change ribbonWordObject 𝒞
        (exteriorWord 𝒞 target.diagram
          (coordinates.mergeLabeling sourceLabeling newLabel)
          (target.diagram.dottedCuts.exterior.activeOrder
            ⟨3, by
              rw [standardTwoThreeBirth_eventCount normalForm]
              omega⟩)) =
      𝟙_ 𝒞.C
    have middleWordEq :
        exteriorWord 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel)
            (target.diagram.dottedCuts.exterior.activeOrder
              ⟨3, by
                rw [standardTwoThreeBirth_eventCount normalForm]
                omega⟩) =
          exteriorWord 𝒞 source.diagram sourceLabeling
            (source.diagram.dottedCuts.exterior.activeOrder 0) := by
      simpa using
        (standardTwoThreeBirth_oldStateExteriorWord
          𝒞 coordinates coordinateBinding normalForm
          sourceLabeling newLabel
          (0 : Fin
            (source.diagram.dottedCuts.exterior.eventCount + 1)))
    rw [middleWordEq]
    rw [source.diagram.dottedCuts.exterior.initialBoundaryEmpty]
    rfl
  have targetObjectEq :
      (standardTwoThreeBirthTargetTrace 𝒞 normalForm
        (coordinates.mergeLabeling sourceLabeling newLabel)).dropThree.object
          (Fin.last source.diagram.dottedCuts.exterior.eventCount) =
        (compiledExteriorTrace 𝒞 source.diagram sourceLabeling).object
          (Fin.last source.diagram.dottedCuts.exterior.eventCount) :=
    congrArg
      (fun trace =>
        trace.object (Fin.last source.diagram.dottedCuts.exterior.eventCount))
      tracesEq
  exact
    (heq_of_eq
      (FiniteMorphismTrace.composePrefix_add_three
        (eventCount := source.diagram.dottedCuts.exterior.eventCount)
        (standardTwoThreeBirthTargetTrace 𝒞 normalForm
          (coordinates.mergeLabeling sourceLabeling newLabel)))).trans
    (CategoryTheory.heq_comp
      sourceObjectEq middleObjectEq targetObjectEq prefixMorphism suffix)

theorem standardTwoThreeBirth_compiledExteriorMorphism
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    {source target : HomologicallyMarkedDiagram}
    (coordinates : TwoThreeGraphCoordinates source target)
    (coordinateBinding : coordinates.MatchesIsolatedComponent)
    (normalForm :
      IsStandardTwoThreeBirth source.diagram target.diagram)
    (sourceLabeling : TwoHandleLabeling 𝒞 source.diagram)
    (newLabel : 𝒞.simples.Simple) :
    compileCutOpenExteriorMorphism 𝒞 target.diagram
        (coordinates.mergeLabeling sourceLabeling newLabel) =
      (ordinaryKirbyLoopExpression 𝒞 newLabel).interpret ≫
        compileCutOpenExteriorMorphism 𝒞 source.diagram
          sourceLabeling := by
  have targetClosedToRaw :=
    compileCutOpenExteriorMorphism_heq_compiledTrace
      𝒞 target.diagram
      (coordinates.mergeLabeling sourceLabeling newLabel)
  have targetRawToStandard :=
    (standardTwoThreeBirthTargetTrace_composeAll
      𝒞 normalForm
      (coordinates.mergeLabeling sourceLabeling newLabel)).symm
  have standardToExpected :=
    standardTwoThreeBirth_targetTraceMorphism
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel
  have loopLabel :=
    standardTwoThreeBirth_newLoopLabel
      𝒞 coordinates coordinateBinding normalForm
      sourceLabeling newLabel
  have localMorphismEq :
      ribbonTraceMorphism 𝒞
          (exteriorStrandLabel 𝒞 target.diagram
            (coordinates.mergeLabeling sourceLabeling newLabel)
            (twoThreeFirstStrand normalForm))
          (𝟙 (𝒞.simples.simpleObject
            (exteriorStrandLabel 𝒞 target.diagram
              (coordinates.mergeLabeling sourceLabeling newLabel)
              (twoThreeFirstStrand normalForm)))) =
        (ordinaryKirbyLoopExpression 𝒞 newLabel).interpret := by
    rw [loopLabel]
    rfl
  have expectedToPublic :
      HEq
        (ribbonTraceMorphism 𝒞
            (exteriorStrandLabel 𝒞 target.diagram
              (coordinates.mergeLabeling sourceLabeling newLabel)
              (twoThreeFirstStrand normalForm))
            (𝟙 (𝒞.simples.simpleObject
              (exteriorStrandLabel 𝒞 target.diagram
                (coordinates.mergeLabeling sourceLabeling newLabel)
                (twoThreeFirstStrand normalForm)))) ≫
          compiledExteriorTraceFromUnit
            𝒞 source.diagram sourceLabeling)
        ((ordinaryKirbyLoopExpression 𝒞 newLabel).interpret ≫
          compiledExteriorTraceFromUnit
            𝒞 source.diagram sourceLabeling) :=
    CategoryTheory.heq_comp rfl rfl rfl
      (heq_of_eq localMorphismEq) (heq_of_eq rfl)
  have sourceClosedToFromUnit :=
    compileCutOpenExteriorMorphism_heq_fromUnit
      𝒞 source.diagram sourceLabeling
  have sourceFinalObjectEq :
      (compiledExteriorTrace 𝒞 source.diagram sourceLabeling).object
          (Fin.last source.diagram.dottedCuts.exterior.eventCount) =
        𝟙_ 𝒞.C := by
    change ribbonWordObject 𝒞
        (exteriorWord 𝒞 source.diagram sourceLabeling
          (source.diagram.dottedCuts.exterior.activeOrder
            (Fin.last source.diagram.dottedCuts.exterior.eventCount))) =
      𝟙_ 𝒞.C
    rw [source.diagram.dottedCuts.exterior.finalBoundaryEmpty]
    rfl
  have publicFromUnitToClosed :
      HEq
        ((ordinaryKirbyLoopExpression 𝒞 newLabel).interpret ≫
          compiledExteriorTraceFromUnit 𝒞 source.diagram
            sourceLabeling)
        ((ordinaryKirbyLoopExpression 𝒞 newLabel).interpret ≫
          compileCutOpenExteriorMorphism 𝒞 source.diagram
            sourceLabeling) :=
    CategoryTheory.heq_comp rfl rfl sourceFinalObjectEq (heq_of_eq rfl)
      sourceClosedToFromUnit.symm
  exact eq_of_heq
    (targetClosedToRaw.trans
      (targetRawToStandard.trans
        (standardToExpected.trans
          (expectedToPublic.trans publicFromUnitToClosed))))

end

end TwistedYetter.Kirby.Final.Proofs
