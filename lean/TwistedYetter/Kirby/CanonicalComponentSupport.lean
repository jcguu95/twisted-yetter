import TwistedYetter.Kirby.CanonicalModularKirbyEvaluator

/-!
# Registered-component support for canonical ribbon diagrams

This module proves that the canonical trace compiler cannot introduce a
component identifier absent from the serialized Kirby presentation.  The
result is structural: downstream local-move derivations no longer need to
assume component support separately for each move family.
-/

open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

namespace TwistedYetter.Kirby.ComponentRibbonDiagram

open TwistedYetter.Kirby.CanonicalKirbyTrace

universe uH

theorem registered_of_componentSome
    (raw : RawPresentation)
    (componentId : String)
    (component : ComponentSpec)
    (found : raw.component? componentId = some component) :
    component ∈ raw.components ∧ component.componentId = componentId := by
  constructor
  · exact List.mem_of_find?_eq_some found
  · have matching := List.find?_some found
    simpa [RawPresentation.component?] using matching

/-- A component ID is backed by an entry in the serialized registry. -/
def RegisteredComponentId
    (raw : RawPresentation) (componentId : String) : Prop :=
  ∃ component ∈ raw.components, component.componentId = componentId

/-- Every open strand in a state belongs to a registered component. -/
def StateUsesRegisteredComponents
    (raw : RawPresentation) (state : List StrandState) : Prop :=
  ∀ strand ∈ state, RegisteredComponentId raw strand.componentId

theorem birth_component_registered
    (raw : RawPresentation)
    (eventId componentId positiveId negativeId : String)
    (insertAt : Nat)
    (before after : List StrandState)
    (stepSound :
      raw.applyEvent before
          (.birth eventId componentId positiveId negativeId insertAt) =
        Except.ok after) :
    RegisteredComponentId raw componentId := by
  let message := "birth references unknown component: " ++ componentId
  cases required :
      RawPresentation.requireSome message (raw.component? componentId) with
  | error errorMessage =>
      have required' :
          RawPresentation.requireSome
              ("birth references unknown component: " ++ componentId)
              (raw.component? componentId) =
            Except.error errorMessage := by
        simpa [message] using required
      simp only [RawPresentation.applyEvent, required'] at stepSound
      change Except.error errorMessage = Except.ok after at stepSound
      contradiction
  | ok component =>
      cases found : raw.component? componentId with
      | none =>
          simp [RawPresentation.requireSome, found] at required
      | some foundComponent =>
          have componentEq : foundComponent = component := by
            simpa [RawPresentation.requireSome, found] using required
          subst component
          have facts :=
            registered_of_componentSome raw componentId foundComponent found
          exact ⟨foundComponent, facts.1, facts.2⟩

theorem EventWindow.after_uses_registered_components
    {raw : RawPresentation}
    {event : SliceEvent}
    {before after : List StrandState}
    (window : EventWindow event before after)
    (beforeSupported : StateUsesRegisteredComponents raw before)
    (stepSound : raw.applyEvent before event = Except.ok after) :
    StateUsesRegisteredComponents raw after := by
  cases window with
  | birth eventId componentId positiveId negativeId leading suffix =>
      have born :=
        birth_component_registered raw eventId componentId
          positiveId negativeId leading.length
          (leading ++ suffix)
          (leading ++
            ([positiveStrand positiveId componentId,
              negativeStrand negativeId componentId] ++ suffix))
          stepSound
      intro strand membership
      rcases List.mem_append.mp membership with inLeading | inRest
      · exact beforeSupported strand (by
          exact List.mem_append.mpr (Or.inl inLeading))
      · rcases List.mem_append.mp inRest with inNew | inSuffix
        · simp at inNew
          rcases inNew with rfl | rfl
          · exact born
          · exact born
        · exact beforeSupported strand (by
            exact List.mem_append.mpr (Or.inr inSuffix))
  | deathPositiveNegative eventId componentId firstId secondId
      positiveId negativeId listedIds leading suffix =>
      intro strand membership
      apply beforeSupported strand
      rcases List.mem_append.mp membership with inLeading | inSuffix
      · exact List.mem_append.mpr (Or.inl inLeading)
      · exact List.mem_append.mpr
          (Or.inr (List.mem_append.mpr (Or.inr inSuffix)))
  | deathNegativePositive eventId componentId firstId secondId
      negativeId positiveId listedIds leading suffix =>
      intro strand membership
      apply beforeSupported strand
      rcases List.mem_append.mp membership with inLeading | inSuffix
      · exact List.mem_append.mpr (Or.inl inLeading)
      · exact List.mem_append.mpr
          (Or.inr (List.mem_append.mpr (Or.inr inSuffix)))
  | crossing eventId overId underId sign overComponent underComponent
      overOrientation underOrientation leading suffix =>
      intro strand membership
      apply beforeSupported strand
      rcases List.mem_append.mp membership with inLeading | inRest
      · exact List.mem_append.mpr (Or.inl inLeading)
      · rcases List.mem_append.mp inRest with inPair | inSuffix
        · exact List.mem_append.mpr (Or.inr (by
            apply List.mem_append.mpr
            left
            simp only [List.mem_cons] at inPair ⊢
            aesop))
        · exact List.mem_append.mpr
            (Or.inr (List.mem_append.mpr (Or.inr inSuffix)))
  | identityCoupon eventId couponId localWindow leading suffix =>
      exact beforeSupported
  | framingTwist eventId strandId sign strand strandIdSound leading suffix =>
      exact beforeSupported
  | planarIdentity eventId state =>
      exact beforeSupported

theorem ComponentBoundary.componentIds_word
    (state : List StrandState) :
    (ComponentBoundary.word state).componentIds =
      state.map StrandState.componentId := by
  induction state with
  | nil =>
      rfl
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil =>
          rfl
      | cons second tail =>
          change
            first.componentId ::
                (ComponentBoundary.word (second :: tail)).componentIds =
              first.componentId ::
                (second.componentId ::
                  tail.map StrandState.componentId)
          exact congrArg (List.cons first.componentId) inductionHypothesis

theorem ComponentBoundary.word_uses_registered_components
    {raw : RawPresentation}
    {state : List StrandState}
    (supported : StateUsesRegisteredComponents raw state) :
    ∀ componentId ∈ (ComponentBoundary.word state).componentIds,
      RegisteredComponentId raw componentId := by
  intro componentId membership
  rw [componentIds_word] at membership
  obtain ⟨strand, strandMem, rfl⟩ := List.mem_map.mp membership
  exact supported strand strandMem

theorem ComponentDiagram.Context.plug_componentIds
    {holeSource holeTarget wholeSource wholeTarget : ComponentBoundary}
    (context :
      ComponentDiagram.Context
        holeSource holeTarget wholeSource wholeTarget)
    (piece : ComponentDiagram holeSource holeTarget)
    (componentId : String)
    (membership : componentId ∈ (context.plug piece).componentIds) :
    componentId ∈ piece.componentIds ∨
      componentId ∈ context.componentIds := by
  induction context with
  | hole =>
      exact Or.inl membership
  | compLeft before =>
      simp only [ComponentDiagram.Context.plug,
        ComponentDiagram.componentIds, List.mem_append] at membership
      exact membership.elim (fun inBefore => Or.inr inBefore) Or.inl
  | compRight after =>
      simp only [ComponentDiagram.Context.plug,
        ComponentDiagram.componentIds, List.mem_append] at membership
      exact membership.elim Or.inl (fun inAfter => Or.inr inAfter)
  | tensorLeft right =>
      simp only [ComponentDiagram.Context.plug,
        ComponentDiagram.componentIds, List.mem_append] at membership
      exact membership.elim Or.inl (fun inRight => Or.inr inRight)
  | tensorRight left =>
      simp only [ComponentDiagram.Context.plug,
        ComponentDiagram.componentIds, List.mem_append] at membership
      exact membership.elim (fun inLeft => Or.inr inLeft) Or.inl
  | compose inner outer innerIH outerIH =>
      have outerCases := outerIH (inner.plug piece) membership
      rcases outerCases with inMiddle | inOuter
      · have innerCases := innerIH piece inMiddle
        exact innerCases.elim Or.inl
          (fun inInner => Or.inr (by
            simp only [ComponentDiagram.Context.componentIds,
              List.mem_append]
            exact Or.inl inInner))
      · exact Or.inr (by
          simp only [ComponentDiagram.Context.componentIds,
            List.mem_append]
          exact Or.inr inOuter)

theorem ComponentDiagram.splitBoundaryWord_componentIds
    (left right : List StrandState) :
    ∀ componentId ∈
        (ComponentDiagram.Context.splitBoundaryWord left right).componentIds,
      componentId ∈
        left.map StrandState.componentId ++
          right.map StrandState.componentId := by
  induction left with
  | nil =>
      intro componentId membership
      simpa [ComponentDiagram.Context.splitBoundaryWord,
        ComponentDiagram.componentIds,
        ComponentBoundary.componentIds_word] using membership
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil =>
          cases right with
          | nil =>
              intro componentId membership
              simpa [ComponentDiagram.Context.splitBoundaryWord,
                ComponentDiagram.componentIds,
                ComponentBoundary.componentIds_word] using membership
          | cons rightFirst rightRest =>
              intro componentId membership
              change
                componentId ∈
                  (ComponentBoundary.word [first]).componentIds ++
                    (ComponentBoundary.word
                      (rightFirst :: rightRest)).componentIds at membership
              rw [ComponentBoundary.componentIds_word,
                ComponentBoundary.componentIds_word] at membership
              exact membership
      | cons second tail =>
          intro componentId membership
          simp only [ComponentDiagram.Context.splitBoundaryWord,
            ComponentDiagram.componentIds, List.mem_append] at membership
          simp only [List.map_cons, List.mem_cons, List.mem_append]
          rcases membership with (inFirst | inRecursive) | inAssociator
          · have inFirst' :
                componentId = first.componentId := by
              simpa [ComponentDiagram.componentIds,
                ComponentBoundary.componentIds,
                ComponentBoundary.ofStrand] using inFirst
            exact Or.inl (Or.inl inFirst')
          · rcases List.mem_append.mp
                (inductionHypothesis componentId inRecursive) with
              inRest | inRight
            · exact Or.inl (Or.inr (by
                simpa only [List.map_cons, List.mem_cons] using inRest))
            · exact Or.inr inRight
          · simp only [ComponentBoundary.componentIds,
              ComponentBoundary.ofStrand,
              ComponentBoundary.componentIds_word] at inAssociator
            aesop

theorem ComponentDiagram.joinBoundaryWord_componentIds
    (left right : List StrandState) :
    ∀ componentId ∈
        (ComponentDiagram.Context.joinBoundaryWord left right).componentIds,
      componentId ∈
        left.map StrandState.componentId ++
          right.map StrandState.componentId := by
  induction left with
  | nil =>
      intro componentId membership
      simpa [ComponentDiagram.Context.joinBoundaryWord,
        ComponentDiagram.componentIds,
        ComponentBoundary.componentIds_word] using membership
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil =>
          cases right with
          | nil =>
              intro componentId membership
              simpa [ComponentDiagram.Context.joinBoundaryWord,
                ComponentDiagram.componentIds,
                ComponentBoundary.componentIds_word] using membership
          | cons rightFirst rightRest =>
              intro componentId membership
              change
                componentId ∈
                  (ComponentBoundary.word [first]).componentIds ++
                    (ComponentBoundary.word
                      (rightFirst :: rightRest)).componentIds at membership
              rw [ComponentBoundary.componentIds_word,
                ComponentBoundary.componentIds_word] at membership
              exact membership
      | cons second tail =>
          intro componentId membership
          simp only [ComponentDiagram.Context.joinBoundaryWord,
            ComponentDiagram.componentIds, List.mem_append] at membership
          simp only [List.map_cons, List.mem_cons, List.mem_append]
          rcases membership with inAssociator | inTensor
          · simp only [ComponentBoundary.componentIds,
              ComponentBoundary.ofStrand,
              ComponentBoundary.componentIds_word] at inAssociator
            aesop
          · rcases inTensor with inFirst | inRecursive
            · have inFirst' :
                  componentId = first.componentId := by
                simpa [ComponentDiagram.componentIds,
                  ComponentBoundary.componentIds,
                  ComponentBoundary.ofStrand] using inFirst
              exact Or.inl (Or.inl inFirst')
            · rcases List.mem_append.mp
                  (inductionHypothesis componentId inRecursive) with
                inRest | inRight
              · exact Or.inl (Or.inr (by
                  simpa only [List.map_cons, List.mem_cons] using inRest))
              · exact Or.inr inRight

theorem ComponentDiagram.Context.surroundBoundaryWord_componentIds
    (leading localSource localTarget suffix : List StrandState) :
    ∀ componentId ∈
        (ComponentDiagram.Context.surroundBoundaryWord
          leading localSource localTarget suffix).componentIds,
      componentId ∈
          (leading ++ (localSource ++ suffix)).map StrandState.componentId ∨
        componentId ∈
          (leading ++ (localTarget ++ suffix)).map StrandState.componentId := by
  intro componentId membership
  simp only [ComponentDiagram.Context.surroundBoundaryWord,
    ComponentDiagram.Context.componentIds,
    ComponentDiagram.componentIds] at membership
  rcases List.mem_append.mp membership with leftHalf | rightHalf
  · rcases List.mem_append.mp leftHalf with suffixContext | inLeading
    · rcases List.mem_append.mp suffixContext with
        suffixAndSplit | inJoinTarget
      · rcases List.mem_append.mp suffixAndSplit with
          inSuffix | inSplitSource
        · have inSuffix' :
              componentId ∈ suffix.map StrandState.componentId := by
            simpa [ComponentBoundary.componentIds_word] using inSuffix
          left
          simp only [List.map_append, List.mem_append]
          aesop
        · have sourcePart :=
            ComponentDiagram.splitBoundaryWord_componentIds
              localSource suffix componentId inSplitSource
          left
          simp only [List.map_append, List.mem_append]
          aesop
      · have targetPart :=
          ComponentDiagram.joinBoundaryWord_componentIds
            localTarget suffix componentId inJoinTarget
        right
        simp only [List.map_append, List.mem_append]
        aesop
    · have inLeading' :
          componentId ∈ leading.map StrandState.componentId := by
        simpa [ComponentBoundary.componentIds_word] using inLeading
      left
      simp only [List.map_append, List.mem_append]
      aesop
  · rcases List.mem_append.mp rightHalf with
      inSplitWholeSource | inJoinWholeTarget
    · have sourceWhole :=
        ComponentDiagram.splitBoundaryWord_componentIds
          leading (localSource ++ suffix) componentId inSplitWholeSource
      left
      simpa only [List.map_append] using sourceWhole
    · have targetWhole :=
        ComponentDiagram.joinBoundaryWord_componentIds
          leading (localTarget ++ suffix) componentId inJoinWholeTarget
      right
      simpa only [List.map_append] using targetWhole

theorem ComponentDiagram.Context.surroundBoundaryWord_plug_componentIds
    (leading localSource localTarget suffix : List StrandState)
    (piece :
      ComponentDiagram
        (ComponentBoundary.word localSource)
        (ComponentBoundary.word localTarget))
    (pieceSupport :
      ∀ componentId ∈ piece.componentIds,
        componentId ∈ localSource.map StrandState.componentId ∨
          componentId ∈ localTarget.map StrandState.componentId) :
    ∀ componentId ∈
        ((ComponentDiagram.Context.surroundBoundaryWord
          leading localSource localTarget suffix).plug piece).componentIds,
      componentId ∈
          (leading ++ (localSource ++ suffix)).map StrandState.componentId ∨
        componentId ∈
          (leading ++ (localTarget ++ suffix)).map StrandState.componentId := by
  intro componentId membership
  rcases ComponentDiagram.Context.plug_componentIds
      (ComponentDiagram.Context.surroundBoundaryWord
        leading localSource localTarget suffix)
      piece componentId membership with inPiece | inContext
  · rcases pieceSupport componentId inPiece with inSource | inTarget
    · left
      simp only [List.map_append, List.mem_append]
      aesop
    · right
      simp only [List.map_append, List.mem_append]
      aesop
  · exact
      ComponentDiagram.Context.surroundBoundaryWord_componentIds
        leading localSource localTarget suffix componentId inContext

theorem EventWindow.componentPrimitive_componentIds_boundary
    {event : SliceEvent}
    {before after : List StrandState}
    (window : EventWindow event before after) :
    ∀ componentId ∈
        (EventWindow.componentPrimitive window).componentIds,
      componentId ∈ before.map StrandState.componentId ∨
        componentId ∈ after.map StrandState.componentId := by
  cases window with
  | birth eventId componentId positiveId negativeId leading suffix =>
      intro id membership
      let context :=
        ComponentDiagram.Context.surroundBoundaryWord
          leading []
          [
            positiveStrand positiveId componentId,
            negativeStrand negativeId componentId
          ]
          suffix
      let piece := ComponentDiagram.cupPositiveNegative componentId
      have plugMembership :
          id ∈ (context.plug piece).componentIds := by
        simpa only [EventWindow.componentPrimitive] using membership
      rcases ComponentDiagram.Context.plug_componentIds
          context piece id plugMembership with inPiece | inContext
      · right
        simp only [List.map_append, List.mem_append, List.map_cons,
          List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
          or_false]
        have idEq : id = componentId := by
          simpa [piece, ComponentDiagram.componentIds,
            ComponentBoundary.componentIds] using inPiece
        aesop
      · have contextMembership :=
          ComponentDiagram.Context.surroundBoundaryWord_componentIds
            leading []
            [
              positiveStrand positiveId componentId,
              negativeStrand negativeId componentId
            ]
            suffix id inContext
        simpa only [List.nil_append, List.map_append, List.map_nil,
          List.append_nil, List.append_assoc] using contextMembership
  | deathPositiveNegative eventId componentId firstId secondId
      positiveId negativeId listedIds leading suffix =>
      intro id membership
      let localSource :=
        [
          positiveStrand positiveId componentId,
          negativeStrand negativeId componentId
        ]
      let context :=
        ComponentDiagram.Context.surroundBoundaryWord
          leading localSource [] suffix
      let piece := ComponentDiagram.capPositiveNegative componentId
      have plugMembership :
          id ∈ (context.plug piece).componentIds := by
        simpa only [EventWindow.componentPrimitive] using membership
      exact
        ComponentDiagram.Context.surroundBoundaryWord_plug_componentIds
          leading localSource [] suffix piece
          (by
            intro pieceId pieceMembership
            left
            change
              pieceId ∈
                (ComponentDiagram.capPositiveNegative componentId).componentIds
              at pieceMembership
            have pieceIdEq : pieceId = componentId := by
              simpa only [ComponentDiagram.componentIds, List.mem_singleton]
                using pieceMembership
            simp [localSource, positiveStrand, negativeStrand, pieceIdEq])
          id plugMembership
  | deathNegativePositive eventId componentId firstId secondId
      negativeId positiveId listedIds leading suffix =>
      intro id membership
      let localSource :=
        [
          negativeStrand negativeId componentId,
          positiveStrand positiveId componentId
        ]
      let context :=
        ComponentDiagram.Context.surroundBoundaryWord
          leading localSource [] suffix
      let piece := ComponentDiagram.capNegativePositive componentId
      have plugMembership :
          id ∈ (context.plug piece).componentIds := by
        simpa only [EventWindow.componentPrimitive] using membership
      exact
        ComponentDiagram.Context.surroundBoundaryWord_plug_componentIds
          leading localSource [] suffix piece
          (by
            intro pieceId pieceMembership
            left
            change
              pieceId ∈
                (ComponentDiagram.capNegativePositive componentId).componentIds
              at pieceMembership
            have pieceIdEq : pieceId = componentId := by
              simpa only [ComponentDiagram.componentIds, List.mem_singleton]
                using pieceMembership
            simp [localSource, positiveStrand, negativeStrand, pieceIdEq])
          id plugMembership
  | crossing eventId overId underId sign overComponent underComponent
      overOrientation underOrientation leading suffix =>
      intro id membership
      let over : StrandState := {
        strandId := overId
        componentId := overComponent
        orientation := overOrientation
      }
      let under : StrandState := {
        strandId := underId
        componentId := underComponent
        orientation := underOrientation
      }
      let localDiagram :=
        match sign with
        | .positive =>
            ComponentDiagram.crossingPositive
              (.atom (ComponentBoundary.ofStrand over))
              (.atom (ComponentBoundary.ofStrand under))
        | .negative =>
            ComponentDiagram.crossingNegative
              (.atom (ComponentBoundary.ofStrand over))
              (.atom (ComponentBoundary.ofStrand under))
      let context :=
        ComponentDiagram.Context.surroundBoundaryWord
          leading [over, under] [under, over] suffix
      have plugMembership :
          id ∈ (context.plug localDiagram).componentIds := by
        simpa only [EventWindow.componentPrimitive] using membership
      exact
        ComponentDiagram.Context.surroundBoundaryWord_plug_componentIds
          leading [over, under] [under, over] suffix localDiagram
          (by
            intro pieceId pieceMembership
            left
            cases sign <;>
              simpa [localDiagram, over, under,
                ComponentDiagram.componentIds,
                ComponentBoundary.componentIds,
                ComponentBoundary.ofStrand] using pieceMembership)
          id plugMembership
  | identityCoupon eventId couponId localWindow leading suffix =>
      intro id membership
      let piece :=
        ComponentDiagram.identityCoupon couponId
          (ComponentBoundary.word localWindow)
      let context :=
        ComponentDiagram.Context.surroundBoundaryWord
          leading localWindow localWindow suffix
      have plugMembership :
          id ∈ (context.plug piece).componentIds := by
        simpa only [EventWindow.componentPrimitive] using membership
      exact
        ComponentDiagram.Context.surroundBoundaryWord_plug_componentIds
          leading localWindow localWindow suffix piece
          (by
            intro pieceId pieceMembership
            left
            simpa [piece, ComponentDiagram.componentIds,
              ComponentBoundary.componentIds_word] using pieceMembership)
          id plugMembership
  | framingTwist eventId strandId sign strand strandIdSound leading suffix =>
      intro id membership
      let localDiagram :=
        match sign with
        | .positive =>
            ComponentDiagram.twistPositive
              (ComponentBoundary.ofStrand strand)
        | .negative =>
            ComponentDiagram.twistNegative
              (ComponentBoundary.ofStrand strand)
      let context :=
        ComponentDiagram.Context.surroundBoundaryWord
          leading [strand] [strand] suffix
      have plugMembership :
          id ∈ (context.plug localDiagram).componentIds := by
        simpa only [EventWindow.componentPrimitive] using membership
      exact
        ComponentDiagram.Context.surroundBoundaryWord_plug_componentIds
          leading [strand] [strand] suffix localDiagram
          (by
            intro pieceId pieceMembership
            left
            cases sign <;>
              simpa [localDiagram, ComponentDiagram.componentIds,
                ComponentBoundary.componentIds,
                ComponentBoundary.ofStrand] using pieceMembership)
          id plugMembership
  | planarIdentity eventId state =>
      intro id membership
      left
      simpa [EventWindow.componentPrimitive,
        ComponentDiagram.componentIds,
        ComponentBoundary.componentIds_word] using membership

/--
Every component inspected by a canonical trace is backed by the serialized
component registry.
-/
theorem trace_componentDiagram_uses_registered_components
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState}
    (trace : Trace raw events before final)
    (beforeSupported : StateUsesRegisteredComponents raw before) :
    ∀ componentId ∈
        (ComponentRibbonDiagram.Trace.componentDiagram trace).componentIds,
      RegisteredComponentId raw componentId := by
  induction trace with
  | nil state =>
      intro componentId membership
      have stateMembership :
          componentId ∈ state.map StrandState.componentId := by
        simpa only [Trace.componentDiagram, ComponentDiagram.componentIds,
          ComponentBoundary.componentIds_word] using membership
      obtain ⟨strand, strandMembership, componentIdEq⟩ :=
        List.mem_map.mp stateMembership
      subst componentId
      exact beforeSupported strand strandMembership
  | @cons event rest before after final window stepSound tail
      inductionHypothesis =>
      intro componentId membership
      have afterSupported :
          StateUsesRegisteredComponents raw after :=
        EventWindow.after_uses_registered_components
          window beforeSupported stepSound
      simp only [Trace.componentDiagram, ComponentDiagram.componentIds,
        List.mem_append] at membership
      rcases membership with primitiveMembership | tailMembership
      · rcases
          EventWindow.componentPrimitive_componentIds_boundary
            window componentId primitiveMembership with
          beforeMembership | afterMembership
        · obtain ⟨strand, strandMembership, componentIdEq⟩ :=
            List.mem_map.mp beforeMembership
          subst componentId
          exact beforeSupported strand strandMembership
        · obtain ⟨strand, strandMembership, componentIdEq⟩ :=
            List.mem_map.mp afterMembership
          subst componentId
          exact afterSupported strand strandMembership
      · exact inductionHypothesis afterSupported componentId tailMembership

/--
The complete canonical diagram cannot inspect an unindexed component ID.
-/
theorem CanonicalPresentation.componentTermDiagram_component_support
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2) :
    ∀ componentId ∈ presentation.componentTermDiagram.componentIds,
      ∃ index : ComponentIndex presentation.topology.formal,
        componentId =
          (componentAt presentation.topology.formal index).componentId := by
  intro componentId membership
  have initiallySupported :
      StateUsesRegisteredComponents presentation.topology.formal.raw [] := by
    intro strand strandMembership
    simp only [List.not_mem_nil] at strandMembership
  have registered :=
    trace_componentDiagram_uses_registered_components
      presentation.canonicalTrace.trace initiallySupported
      componentId (by
        simpa only [CanonicalPresentation.componentTermDiagram]
          using membership)
  obtain ⟨component, componentMembership, componentIdEq⟩ := registered
  obtain ⟨index, indexEq⟩ := List.get_of_mem componentMembership
  refine ⟨index, ?_⟩
  simp only [componentAt]
  rw [indexEq]
  exact componentIdEq.symm

end TwistedYetter.Kirby.ComponentRibbonDiagram
