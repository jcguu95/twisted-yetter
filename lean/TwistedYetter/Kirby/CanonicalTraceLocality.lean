import TwistedYetter.Kirby.CanonicalKirbyTrace

/-!
# Locality invariants of canonical execution traces

This module derives the small list-theoretic facts needed to prove that a
validated event trace selects a unique local ribbon window.  It contains no
category, diagram evaluation, Kirby-move theorem, or scalar equality.
-/

namespace TwistedYetter.Kirby.CanonicalTraceLocality

open TwistedYetter.Kirby.Presentation

/-- Active strand IDs never occur twice in a valid execution state. -/
def ActiveIdsUnique (state : List StrandState) : Prop :=
  (RawPresentation.activeIds state).Nodup

/-- Looking up no active strand is equivalent to absence from active IDs. -/
theorem strand?_eq_none_iff_not_mem_activeIds
    (state : List StrandState)
    (strandId : String) :
    RawPresentation.strand? state strandId = none ↔
      strandId ∉ RawPresentation.activeIds state := by
  constructor
  · intro lookup membership
    obtain ⟨strand, strandMem, strandIdSound⟩ :=
      List.mem_map.mp membership
    have rejected :=
      (List.find?_eq_none.mp lookup) strand strandMem
    simp only [Bool.not_eq_true] at rejected
    have unequal : strand.strandId ≠ strandId := by
      simpa using rejected
    exact unequal strandIdSound
  · intro absent
    change
      List.find? (fun strand => strand.strandId == strandId) state =
        none
    rw [List.find?_eq_none]
    intro strand strandMem
    by_cases strandIdSound : strand.strandId = strandId
    · subst strandId
      exfalso
      apply absent
      exact List.mem_map_of_mem strandMem
    · simp [strandIdSound]

/--
In a boundary with unique strand IDs, splitting at a strand with one fixed ID
has a unique prefix, strand, and suffix.
-/
theorem unique_strand_split
    (strandId : String)
    (leftLeading rightLeading : List StrandState)
    (leftStrand rightStrand : StrandState)
    (leftSuffix rightSuffix : List StrandState)
    (unique :
      ActiveIdsUnique
        (leftLeading ++ (leftStrand :: leftSuffix)))
    (same :
      leftLeading ++ (leftStrand :: leftSuffix) =
        rightLeading ++ (rightStrand :: rightSuffix))
    (leftId : leftStrand.strandId = strandId)
    (rightId : rightStrand.strandId = strandId) :
    leftLeading = rightLeading ∧
      leftStrand = rightStrand ∧
      leftSuffix = rightSuffix := by
  induction leftLeading generalizing rightLeading with
  | nil =>
      cases rightLeading with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at same
          exact ⟨rfl, same.1, same.2⟩
      | cons rightHead rightTail =>
          simp only [List.nil_append, List.cons_append,
            List.cons.injEq] at same
          have headId : rightHead.strandId = strandId := by
            rw [← same.1, leftId]
          have forbidden :
              leftStrand.strandId ∉
                RawPresentation.activeIds leftSuffix := by
            have unique' :
                (leftStrand.strandId ::
                  RawPresentation.activeIds leftSuffix).Nodup := by
              simpa [ActiveIdsUnique,
                RawPresentation.activeIds] using unique
            exact (List.nodup_cons.mp unique').1
          exfalso
          apply forbidden
          rw [same.2, RawPresentation.activeIds,
            List.map_append]
          simp [leftId, rightId]
  | cons leftHead leftTail inductionHypothesis =>
      cases rightLeading with
      | nil =>
          simp only [List.cons_append, List.nil_append,
            List.cons.injEq] at same
          have headId : leftHead.strandId = strandId := by
            rw [same.1, rightId]
          have forbidden :
              leftHead.strandId ∉
                RawPresentation.activeIds
                  (leftTail ++ (leftStrand :: leftSuffix)) := by
            have unique' :
                (leftHead.strandId ::
                  RawPresentation.activeIds
                    (leftTail ++ (leftStrand :: leftSuffix))).Nodup := by
              simpa [ActiveIdsUnique,
                RawPresentation.activeIds] using unique
            exact (List.nodup_cons.mp unique').1
          exfalso
          apply forbidden
          rw [RawPresentation.activeIds, List.map_append]
          simp [headId, leftId]
      | cons rightHead rightTail =>
          simp only [List.cons_append, List.cons.injEq] at same
          have tailUnique :
              ActiveIdsUnique
                (leftTail ++ (leftStrand :: leftSuffix)) := by
            simpa only [ActiveIdsUnique,
              RawPresentation.activeIds, List.map_cons] using
              unique.tail
          obtain ⟨leadingEq, strandEq, suffixEq⟩ :=
            inductionHypothesis rightTail tailUnique same.2
          exact
            ⟨congrArg (List.cons leftHead) leadingEq |>.trans
                (by rw [same.1]),
              strandEq, suffixEq⟩

/--
Two append decompositions with equal prefix lengths have equal pieces.
-/
theorem append_split_unique_of_length
    {α : Type}
    (leftPrefix leftSuffix rightPrefix rightSuffix : List α)
    (same :
      leftPrefix ++ leftSuffix = rightPrefix ++ rightSuffix)
    (sameLength : leftPrefix.length = rightPrefix.length) :
    leftPrefix = rightPrefix ∧ leftSuffix = rightSuffix := by
  have prefixEq : leftPrefix = rightPrefix := by
    calc
      leftPrefix =
          (leftPrefix ++ leftSuffix).take leftPrefix.length := by
            rw [List.take_left]
      _ = (rightPrefix ++ rightSuffix).take rightPrefix.length := by
            rw [same, sameLength]
      _ = rightPrefix := by
            rw [List.take_left]
  have suffixEq : leftSuffix = rightSuffix := by
    calc
      leftSuffix =
          (leftPrefix ++ leftSuffix).drop leftPrefix.length := by
            rw [List.drop_left]
      _ = (rightPrefix ++ rightSuffix).drop rightPrefix.length := by
            rw [same, sameLength]
      _ = rightSuffix := by
            rw [List.drop_left]
  exact ⟨prefixEq, suffixEq⟩

/--
In a boundary with unique strand IDs, a nonempty contiguous window with a
fixed ordered ID list has a unique prefix, window, and suffix.
-/
theorem unique_nonempty_window_split
    (leftLeading rightLeading leftWindow rightWindow
      leftSuffix rightSuffix : List StrandState)
    (unique :
      ActiveIdsUnique
        (leftLeading ++ (leftWindow ++ leftSuffix)))
    (same :
      leftLeading ++ (leftWindow ++ leftSuffix) =
        rightLeading ++ (rightWindow ++ rightSuffix))
    (sameIds :
      RawPresentation.activeIds leftWindow =
        RawPresentation.activeIds rightWindow)
    (leftNonempty : leftWindow ≠ []) :
    leftLeading = rightLeading ∧
      leftWindow = rightWindow ∧
      leftSuffix = rightSuffix := by
  cases leftWindow with
  | nil =>
      contradiction
  | cons leftHead leftTail =>
      cases rightWindow with
      | nil =>
          simp [RawPresentation.activeIds] at sameIds
      | cons rightHead rightTail =>
          have headId :
              leftHead.strandId = rightHead.strandId := by
            simpa [RawPresentation.activeIds] using
              congrArg List.head? sameIds
          obtain ⟨leadingEq, headEq, tailSame⟩ :=
            unique_strand_split leftHead.strandId
              leftLeading rightLeading leftHead rightHead
              (leftTail ++ leftSuffix)
              (rightTail ++ rightSuffix)
              unique same rfl headId.symm
          have tailIds :
              RawPresentation.activeIds leftTail =
                RawPresentation.activeIds rightTail := by
            simpa [RawPresentation.activeIds] using
              congrArg List.tail sameIds
          have tailLength :
              leftTail.length = rightTail.length := by
            simpa [RawPresentation.activeIds] using
              congrArg List.length tailIds
          obtain ⟨tailEq, suffixEq⟩ :=
            append_split_unique_of_length
              leftTail leftSuffix rightTail rightSuffix
              tailSame tailLength
          exact
            ⟨leadingEq,
              congrArg (List.cons leftHead) tailEq |>.trans
                (by rw [headEq]),
              suffixEq⟩

/--
In a duplicate-free list, deleting one adjacent pair has a unique
prefix/pair/suffix cut once both the source and target lists are fixed.
-/
theorem unique_adjacent_pair_deletion_split
    {α : Type}
    (leftLeading rightLeading : List α)
    (leftFirst leftSecond rightFirst rightSecond : α)
    (leftSuffix rightSuffix : List α)
    (unique :
      (leftLeading ++ (leftFirst :: leftSecond :: leftSuffix)).Nodup)
    (sameBefore :
      leftLeading ++ (leftFirst :: leftSecond :: leftSuffix) =
        rightLeading ++ (rightFirst :: rightSecond :: rightSuffix))
    (sameAfter :
      leftLeading ++ leftSuffix = rightLeading ++ rightSuffix) :
    leftLeading = rightLeading ∧
      leftFirst = rightFirst ∧
      leftSecond = rightSecond ∧
      leftSuffix = rightSuffix := by
  induction leftLeading generalizing rightLeading with
  | nil =>
      cases rightLeading with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at sameBefore
          simp only [List.nil_append] at sameAfter
          exact
            ⟨rfl, sameBefore.1, sameBefore.2.1, sameAfter⟩
      | cons rightHead rightTail =>
          simp only [List.nil_append, List.cons_append,
            List.cons.injEq] at sameBefore
          simp only [List.nil_append, List.cons_append] at sameAfter
          have firstNotIn :
              leftFirst ∉ leftSecond :: leftSuffix :=
            (List.nodup_cons.mp unique).1
          exfalso
          apply firstNotIn
          rw [sameAfter]
          simp [sameBefore.1]
  | cons leftHead leftTail inductionHypothesis =>
      cases rightLeading with
      | nil =>
          simp only [List.cons_append, List.nil_append,
            List.cons.injEq] at sameBefore
          simp only [List.cons_append, List.nil_append] at sameAfter
          have rightUnique :
              (rightFirst :: rightSecond :: rightSuffix).Nodup := by
            rw [← sameBefore.1, ← sameBefore.2]
            simpa only [List.cons_append] using unique
          have firstNotIn :
              rightFirst ∉ rightSecond :: rightSuffix :=
            (List.nodup_cons.mp rightUnique).1
          exfalso
          apply firstNotIn
          rw [← sameAfter]
          simp [sameBefore.1]
      | cons rightHead rightTail =>
          simp only [List.cons_append, List.cons.injEq] at sameBefore
          simp only [List.cons_append, List.cons.injEq] at sameAfter
          have tailUnique :
              (leftTail ++
                (leftFirst :: leftSecond :: leftSuffix)).Nodup := by
            simpa only [List.cons_append] using unique.tail
          obtain ⟨leadingEq, firstEq, secondEq, suffixEq⟩ :=
            inductionHypothesis rightTail tailUnique
              sameBefore.2 sameAfter.2
          exact
            ⟨congrArg (List.cons leftHead) leadingEq |>.trans
                (by rw [sameBefore.1]),
              firstEq, secondEq, suffixEq⟩

/-- A component returned by `component?` has exactly the queried ID. -/
theorem component?_some_componentId
    (raw : RawPresentation)
    (componentId : String)
    (component : ComponentSpec)
    (lookup : raw.component? componentId = some component) :
    component.componentId = componentId := by
  change
    List.find? (fun candidate =>
      candidate.componentId == componentId) raw.components =
        some component at lookup
  have accepted :=
    List.find?_some lookup
  simpa using accepted

/--
The custom insertion function only changes where the inserted block occurs.
-/
theorem insertAt_perm
    {α : Type}
    {values state result : List α}
    {index : Nat}
    (inserted :
      RawPresentation.insertAt? values index state = some result) :
    result.Perm (values ++ state) := by
  induction index generalizing state result with
  | zero =>
      simp only [RawPresentation.insertAt?, Option.some.injEq] at inserted
      subst result
      exact .refl _
  | succ index inductionHypothesis =>
      cases state with
      | nil =>
          simp [RawPresentation.insertAt?] at inserted
      | cons head tail =>
          simp only [RawPresentation.insertAt?] at inserted
          cases recursive :
              RawPresentation.insertAt? values index tail with
          | none =>
              simp [recursive] at inserted
          | some recursiveResult =>
              simp only [recursive, Option.map_some,
                Option.some.injEq] at inserted
              subst result
              exact
                (inductionHypothesis recursive).cons head |>.trans
                  List.perm_middle.symm

/--
Inserting a finite block into a duplicate-free list preserves duplicate
freeness when the block is duplicate-free and disjoint from the old list.
-/
theorem insertAt_nodup
    {α : Type}
    {values state result : List α}
    {index : Nat}
    (inserted :
      RawPresentation.insertAt? values index state = some result)
    (valuesNodup : values.Nodup)
    (stateNodup : state.Nodup)
    (disjoint :
      ∀ value, value ∈ values → ∀ old, old ∈ state → value ≠ old) :
    result.Nodup :=
  (insertAt_perm inserted).symm.nodup
    (List.nodup_append.mpr
      ⟨valuesNodup, stateNodup, disjoint⟩)

/--
The strand-ID form of `insertAt_nodup`, matching the invariant used by
canonical traces.
-/
theorem insertAt_activeIdsUnique
    {values state result : List StrandState}
    {index : Nat}
    (inserted :
      RawPresentation.insertAt? values index state = some result)
    (valuesUnique : ActiveIdsUnique values)
    (stateUnique : ActiveIdsUnique state)
    (disjoint :
      ∀ strandId, strandId ∈ RawPresentation.activeIds values →
        ∀ oldId, oldId ∈ RawPresentation.activeIds state →
          strandId ≠ oldId) :
    ActiveIdsUnique result := by
  have permutation :=
    (insertAt_perm inserted).map StrandState.strandId
  apply permutation.symm.nodup
  simpa only [ActiveIdsUnique, RawPresentation.activeIds,
    List.map_append] using
    List.nodup_append.mpr
      ⟨valuesUnique, stateUnique, disjoint⟩

/-- Inserting at the boundary after a prefix has the expected exact shape. -/
theorem insertAt_length_append
    {α : Type}
    (values leading suffix : List α) :
    RawPresentation.insertAt? values leading.length
        (leading ++ suffix) =
      some (leading ++ values ++ suffix) := by
  induction leading with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      simp only [List.length_cons, List.cons_append,
        RawPresentation.insertAt?, inductionHypothesis, Option.map_some]

/--
A successful birth event uses two distinct strand IDs that were both absent
from the incoming execution state.
-/
theorem birth_step_fresh
    (raw : RawPresentation)
    (before after : List StrandState)
    (eventId componentId positiveId negativeId : String)
    (insertAt : Nat)
    (step :
      raw.applyEvent before
        (.birth eventId componentId positiveId negativeId insertAt) =
          Except.ok after) :
    positiveId ≠ negativeId ∧
      positiveId ∉ RawPresentation.activeIds before ∧
      negativeId ∉ RawPresentation.activeIds before := by
  cases componentLookup : raw.component? componentId with
  | none =>
      have impossible :
          raw.applyEvent before
              (.birth eventId componentId positiveId negativeId insertAt) =
            Except.error
              ("birth references unknown component: " ++ componentId) := by
        simp only [RawPresentation.applyEvent, componentLookup,
          RawPresentation.requireSome]
        rfl
      rw [impossible] at step
      contradiction
  | some component =>
      by_cases emptyIds :
          (positiveId.isEmpty || negativeId.isEmpty) = true
      · have impossible :
            raw.applyEvent before
                (.birth eventId componentId positiveId negativeId insertAt) =
              Except.error "birth strand IDs must be nonempty" := by
          simp only [RawPresentation.applyEvent, componentLookup,
            RawPresentation.requireSome]
          change
            (if
                (positiveId.isEmpty || negativeId.isEmpty) = true then
              Except.error "birth strand IDs must be nonempty"
            else
              _) =
              Except.error "birth strand IDs must be nonempty"
          rw [if_pos emptyIds]
        rw [impossible] at step
        contradiction
      · by_cases idsEqual : (positiveId == negativeId) = true
        · have impossible :
              raw.applyEvent before
                  (.birth eventId componentId positiveId negativeId insertAt) =
                Except.error "birth strand IDs must be distinct" := by
            simp only [RawPresentation.applyEvent, componentLookup,
              RawPresentation.requireSome]
            change
              (if
                  (positiveId.isEmpty || negativeId.isEmpty) = true then
                _
              else if (positiveId == negativeId) = true then
                Except.error "birth strand IDs must be distinct"
              else
                _) =
                Except.error "birth strand IDs must be distinct"
            rw [if_neg emptyIds, if_pos idsEqual]
          rw [impossible] at step
          contradiction
        · by_cases reused :
            ((RawPresentation.strand? before positiveId).isSome ||
              (RawPresentation.strand? before negativeId).isSome) = true
          · have impossible :
                raw.applyEvent before
                    (.birth eventId componentId positiveId negativeId insertAt) =
                  Except.error "birth reuses an active strand ID" := by
              simp only [RawPresentation.applyEvent, componentLookup,
                RawPresentation.requireSome]
              change
                (if
                    (positiveId.isEmpty || negativeId.isEmpty) = true then
                  _
                else if (positiveId == negativeId) = true then
                  _
                else if
                    ((RawPresentation.strand? before positiveId).isSome ||
                      (RawPresentation.strand? before negativeId).isSome) =
                        true then
                  Except.error "birth reuses an active strand ID"
                else
                  _) =
                  Except.error "birth reuses an active strand ID"
              rw [if_neg emptyIds, if_neg idsEqual, if_pos reused]
            rw [impossible] at step
            contradiction
          · have positiveNone :
                RawPresentation.strand? before positiveId = none := by
              cases lookup :
                  RawPresentation.strand? before positiveId <;>
                simp_all
            have negativeNone :
                RawPresentation.strand? before negativeId = none := by
              cases lookup :
                  RawPresentation.strand? before negativeId <;>
                simp_all
            have idsDistinct : positiveId ≠ negativeId := by
              simpa using idsEqual
            exact
              ⟨idsDistinct,
                (strand?_eq_none_iff_not_mem_activeIds
                  before positiveId).mp positiveNone,
                (strand?_eq_none_iff_not_mem_activeIds
                  before negativeId).mp negativeNone⟩

/-- A successfully validated coupon has a nonempty input or output word. -/
theorem coupon_step_words_not_both_empty
    (raw : RawPresentation)
    (before after : List StrandState)
    (eventId couponId label : String)
    (inputStrands : List String)
    (outputStrands : List StrandState)
    (replaceAt : Nat)
    (step :
      raw.applyEvent before
        (.coupon eventId couponId label
          inputStrands outputStrands replaceAt) =
          Except.ok after) :
    inputStrands ≠ [] ∨ outputStrands ≠ [] := by
  by_contra bothEmpty
  push Not at bothEmpty
  rcases bothEmpty with ⟨inputEmpty, outputEmpty⟩
  subst inputStrands
  subst outputStrands
  by_cases headerEmpty : couponId.isEmpty || label.isEmpty
  · have metadataError :
        raw.validateCouponMetadata before couponId label [] [] =
          Except.error "coupon ID and label must be nonempty" := by
      simp only [RawPresentation.validateCouponMetadata]
      rw [if_pos headerEmpty]
      rfl
    rw [RawPresentation.applyEvent, metadataError] at step
    contradiction
  · have metadataError :
        raw.validateCouponMetadata before couponId label [] [] =
          Except.error
            "coupon input and output words cannot both be empty" := by
      simp only [RawPresentation.validateCouponMetadata]
      rw [if_neg headerEmpty]
      simp
      rfl
    rw [RawPresentation.applyEvent, metadataError] at step
    contradiction

/--
A successfully validated planar marker has exactly the current ordered
strand IDs and leaves the active boundary unchanged.
-/
theorem planar_step_order_target
    (raw : RawPresentation)
    (before after : List StrandState)
    (eventId : String)
    (order : List String)
    (step :
      raw.applyEvent before (.planarIsotopy eventId order) =
        Except.ok after) :
    order = RawPresentation.activeIds before ∧ after = before := by
  by_cases orderSound : order = RawPresentation.activeIds before
  · subst order
    have exactStep :
        raw.applyEvent before
            (.planarIsotopy eventId
              (RawPresentation.activeIds before)) =
          Except.ok before := by
      simp [RawPresentation.applyEvent]
      change Except.ok before = Except.ok before
      rfl
    exact
      ⟨rfl, Except.ok.inj (step.symm.trans exactStep)⟩
  · have rejected :
        (order != RawPresentation.activeIds before) = true := by
      simp [orderSound]
    have impossible :
        raw.applyEvent before (.planarIsotopy eventId order) =
          Except.error "planar isotopy has the wrong active boundary" := by
      simp only [RawPresentation.applyEvent]
      change
        (if (order != RawPresentation.activeIds before) = true then
          Except.error "planar isotopy has the wrong active boundary"
        else
          _) =
          Except.error "planar isotopy has the wrong active boundary"
      rw [if_pos rejected]
    rw [impossible] at step
    contradiction

/--
Successful execution of the same serialized event from the same state has a
presentation-independent target state.

The only event branch that reads the component registry is birth.  Its lookup
can affect no output except the returned component ID, and `component?`
guarantees that this ID is exactly the one serialized in the event.
-/
theorem applyEvent_ok_target_eq
    (leftRaw rightRaw : RawPresentation)
    (before leftAfter rightAfter : List StrandState)
    (event : SliceEvent)
    (leftStep :
      leftRaw.applyEvent before event = Except.ok leftAfter)
    (rightStep :
      rightRaw.applyEvent before event = Except.ok rightAfter) :
    leftAfter = rightAfter := by
  cases event with
  | birth eventId componentId positiveId negativeId insertAt =>
      cases leftLookup : leftRaw.component? componentId with
      | none =>
          have impossible :
              leftRaw.applyEvent before
                  (.birth eventId componentId positiveId negativeId insertAt) =
                Except.error
                  ("birth references unknown component: " ++ componentId) := by
            simp only [RawPresentation.applyEvent, leftLookup,
              RawPresentation.requireSome]
            rfl
          rw [impossible] at leftStep
          contradiction
      | some leftComponent =>
          cases rightLookup : rightRaw.component? componentId with
          | none =>
              have impossible :
                  rightRaw.applyEvent before
                      (.birth eventId componentId positiveId negativeId insertAt) =
                    Except.error
                      ("birth references unknown component: " ++ componentId) := by
                simp only [RawPresentation.applyEvent, rightLookup,
                  RawPresentation.requireSome]
                rfl
              rw [impossible] at rightStep
              contradiction
          | some rightComponent =>
              have leftId :=
                component?_some_componentId leftRaw componentId
                  leftComponent leftLookup
              have rightId :=
                component?_some_componentId rightRaw componentId
                  rightComponent rightLookup
              let birthBody (actualComponentId : String) :
                  Except String (List StrandState) := do
                if positiveId.isEmpty || negativeId.isEmpty then
                  throw "birth strand IDs must be nonempty"
                if positiveId == negativeId then
                  throw "birth strand IDs must be distinct"
                if (RawPresentation.strand? before positiveId).isSome ||
                    (RawPresentation.strand? before negativeId).isSome then
                  throw "birth reuses an active strand ID"
                let inserted ←
                  RawPresentation.requireSome
                    "birth insert_at is outside the active boundary"
                    (RawPresentation.insertAt? [
                      {
                        strandId := positiveId
                        componentId := actualComponentId
                        orientation := .positive
                      },
                      {
                        strandId := negativeId
                        componentId := actualComponentId
                        orientation := .negative
                      }
                    ] insertAt before)
                return inserted
              simp only [RawPresentation.applyEvent, leftLookup,
                RawPresentation.requireSome] at leftStep
              simp only [RawPresentation.applyEvent, rightLookup,
                RawPresentation.requireSome] at rightStep
              change
                birthBody leftComponent.componentId =
                  Except.ok leftAfter at leftStep
              change
                birthBody rightComponent.componentId =
                  Except.ok rightAfter at rightStep
              rw [leftId] at leftStep
              rw [rightId] at rightStep
              exact Except.ok.inj (leftStep.symm.trans rightStep)
  | death eventId componentId firstId secondId =>
      simpa only [RawPresentation.applyEvent] using
        Except.ok.inj (leftStep.symm.trans rightStep)
  | crossing eventId overId underId sign =>
      simpa only [RawPresentation.applyEvent] using
        Except.ok.inj (leftStep.symm.trans rightStep)
  | coupon eventId couponId label inputStrands outputStrands replaceAt =>
      cases leftMetadata :
          leftRaw.validateCouponMetadata before
            couponId label inputStrands outputStrands with
      | error message =>
          rw [RawPresentation.applyEvent, leftMetadata] at leftStep
          contradiction
      | ok _metadataUnit =>
          cases rightMetadata :
              rightRaw.validateCouponMetadata before
                couponId label inputStrands outputStrands with
          | error message =>
              rw [RawPresentation.applyEvent, rightMetadata] at rightStep
              contradiction
          | ok _metadataUnit =>
              rw [RawPresentation.applyEvent, leftMetadata] at leftStep
              rw [RawPresentation.applyEvent, rightMetadata] at rightStep
              exact Except.ok.inj (leftStep.symm.trans rightStep)
  | framingTwist eventId strandId sign =>
      simpa only [RawPresentation.applyEvent] using
        Except.ok.inj (leftStep.symm.trans rightStep)
  | planarIsotopy eventId order =>
      simpa only [RawPresentation.applyEvent] using
        Except.ok.inj (leftStep.symm.trans rightStep)

/-- Removing one adjacent pair returns a literal sublist of the old state. -/
theorem removeAdjacentPair_sublist
    {firstId secondId : String}
    {state result : List StrandState}
    (removed :
      RawPresentation.removeAdjacentPair?
        firstId secondId state = some result) :
    result.Sublist state := by
  induction state generalizing result with
  | nil =>
      simp [RawPresentation.removeAdjacentPair?] at removed
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp [RawPresentation.removeAdjacentPair?] at removed
      | cons second rest =>
          simp only [RawPresentation.removeAdjacentPair?] at removed
          split at removed
          · simp only [Option.some.injEq] at removed
            subst result
            exact ((List.Sublist.refl rest).cons second).cons first
          · cases recursive :
                RawPresentation.removeAdjacentPair?
                  firstId secondId (second :: rest) with
            | none =>
                simp [recursive] at removed
            | some recursiveResult =>
                simp only [recursive, Option.map_some,
                  Option.some.injEq] at removed
                subst result
                exact
                  (inductionHypothesis recursive).cons₂ first

/-- Death events cannot introduce duplicate active strand IDs. -/
theorem removeAdjacentPair_activeIdsUnique
    {firstId secondId : String}
    {state result : List StrandState}
    (removed :
      RawPresentation.removeAdjacentPair?
        firstId secondId state = some result)
    (stateUnique : ActiveIdsUnique state) :
    ActiveIdsUnique result := by
  exact
    (removeAdjacentPair_sublist removed).map StrandState.strandId
      |>.nodup stateUnique

/-- Swapping one adjacent pair only permutes the old execution state. -/
theorem swapAdjacentPair_perm
    {firstId secondId : String}
    {state result : List StrandState}
    (swapped :
      RawPresentation.swapAdjacentPair?
        firstId secondId state = some result) :
    result.Perm state := by
  induction state generalizing result with
  | nil =>
      simp [RawPresentation.swapAdjacentPair?] at swapped
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp [RawPresentation.swapAdjacentPair?] at swapped
      | cons second rest =>
          simp only [RawPresentation.swapAdjacentPair?] at swapped
          split at swapped
          · simp only [Option.some.injEq] at swapped
            subst result
            exact List.Perm.swap first second rest
          · cases recursive :
                RawPresentation.swapAdjacentPair?
                  firstId secondId (second :: rest) with
            | none =>
                simp [recursive] at swapped
            | some recursiveResult =>
                simp only [recursive, Option.map_some,
                  Option.some.injEq] at swapped
                subst result
                exact (inductionHypothesis recursive).cons first

/-- Crossing events cannot introduce duplicate active strand IDs. -/
theorem swapAdjacentPair_activeIdsUnique
    {firstId secondId : String}
    {state result : List StrandState}
    (swapped :
      RawPresentation.swapAdjacentPair?
        firstId secondId state = some result)
    (stateUnique : ActiveIdsUnique state) :
    ActiveIdsUnique result := by
  exact
    ((swapAdjacentPair_perm swapped).map StrandState.strandId).symm.nodup
      stateUnique

open TwistedYetter.Kirby.CanonicalKirbyTrace

/--
Every accepted canonical event window preserves active-strand uniqueness.

Only birth needs information from `applyEvent`: the validator proves that its
two new IDs are distinct and fresh.  Death deletes a sublist, crossing
permutes a pair, and the remaining three event kinds preserve the state.
-/
theorem EventWindow.preserves_activeIdsUnique
    {raw : RawPresentation}
    {event : SliceEvent}
    {before after : List StrandState}
    (window : EventWindow event before after)
    (step : raw.applyEvent before event = Except.ok after)
    (beforeUnique : ActiveIdsUnique before) :
    ActiveIdsUnique after := by
  cases window with
  | birth eventId componentId positiveId negativeId leading suffix =>
      obtain ⟨idsDistinct, positiveFresh, negativeFresh⟩ :=
        birth_step_fresh raw _ _ eventId componentId
          positiveId negativeId leading.length step
      rw [← List.append_assoc]
      apply insertAt_activeIdsUnique
        (insertAt_length_append
          [positiveStrand positiveId componentId,
            negativeStrand negativeId componentId]
          leading suffix)
      · simpa [ActiveIdsUnique, RawPresentation.activeIds,
          positiveStrand, negativeStrand] using idsDistinct
      · exact beforeUnique
      · intro strandId strandIdMem oldId oldIdMem
        simp only [RawPresentation.activeIds, List.map_cons,
          List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at strandIdMem
        rcases strandIdMem with rfl | rfl
        · intro equality
          subst oldId
          exact positiveFresh oldIdMem
        · intro equality
          subst oldId
          exact negativeFresh oldIdMem
  | deathPositiveNegative eventId componentId firstId secondId
      positiveId negativeId listedIdsSound leading suffix =>
      have deletion :
          (leading ++ suffix).Sublist
            (leading ++
              ([positiveStrand positiveId componentId,
                negativeStrand negativeId componentId] ++ suffix)) := by
        exact
          (List.sublist_append_right
              [positiveStrand positiveId componentId,
                negativeStrand negativeId componentId]
              suffix).append_left leading
      exact
        (deletion.map StrandState.strandId).nodup beforeUnique
  | deathNegativePositive eventId componentId firstId secondId
      negativeId positiveId listedIdsSound leading suffix =>
      have deletion :
          (leading ++ suffix).Sublist
            (leading ++
              ([negativeStrand negativeId componentId,
                positiveStrand positiveId componentId] ++ suffix)) := by
        exact
          (List.sublist_append_right
              [negativeStrand negativeId componentId,
                positiveStrand positiveId componentId]
              suffix).append_left leading
      exact
        (deletion.map StrandState.strandId).nodup beforeUnique
  | crossing eventId overId underId sign overComponent underComponent
      overOrientation underOrientation leading suffix =>
      let overStrand : StrandState :=
        {
          strandId := overId
          componentId := overComponent
          orientation := overOrientation
        }
      let underStrand : StrandState :=
        {
          strandId := underId
          componentId := underComponent
          orientation := underOrientation
        }
      have permutation :
          (leading ++ ([underStrand, overStrand] ++ suffix)).Perm
            (leading ++ ([overStrand, underStrand] ++ suffix)) := by
        exact
          (List.Perm.swap overStrand underStrand suffix).append_left leading
      exact
        (permutation.map StrandState.strandId).symm.nodup beforeUnique
  | identityCoupon =>
      exact beforeUnique
  | framingTwist =>
      exact beforeUnique
  | planarIdentity =>
      exact beforeUnique

/-- A canonical trace preserves active-strand uniqueness end to end. -/
theorem Trace.preserves_activeIdsUnique
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState}
    (trace : Trace raw events before final)
    (beforeUnique : ActiveIdsUnique before) :
    ActiveIdsUnique final := by
  induction trace with
  | nil =>
      exact beforeUnique
  | cons window step tail inductionHypothesis =>
      exact inductionHypothesis
        (EventWindow.preserves_activeIdsUnique
          window step beforeUnique)

/--
Two canonical traces with the same event list and initial state reach the
same final active boundary, even when they belong to different presentation
records.
-/
theorem Trace.final_eq_of_same_events
    {leftRaw rightRaw : RawPresentation}
    {events : List SliceEvent}
    {before leftFinal rightFinal : List StrandState}
    (left : Trace leftRaw events before leftFinal)
    (right : Trace rightRaw events before rightFinal) :
    leftFinal = rightFinal := by
  induction left generalizing rightFinal with
  | nil =>
      cases right
      rfl
  | cons leftWindow leftStep leftTail inductionHypothesis =>
      cases right with
      | cons rightWindow rightStep rightTail =>
          have middleEq :=
            applyEvent_ok_target_eq _ _ _ _ _ _
              leftStep rightStep
          subst middleEq
          exact inductionHypothesis rightTail

/--
The state selected by a common event prefix is independent of the surrounding
presentation and of the two suffixes that follow it.
-/
theorem Trace.splitPrefix_state_eq
    {leftRaw rightRaw : RawPresentation}
    (prefixEvents leftSuffixEvents rightSuffixEvents : List SliceEvent)
    {before leftFinal rightFinal : List StrandState}
    (left :
      Trace leftRaw (prefixEvents ++ leftSuffixEvents)
        before leftFinal)
    (right :
      Trace rightRaw (prefixEvents ++ rightSuffixEvents)
        before rightFinal) :
    (left.splitAppend prefixEvents leftSuffixEvents).1 =
      (right.splitAppend prefixEvents rightSuffixEvents).1 := by
  exact
    Trace.final_eq_of_same_events
      (left.splitAppend prefixEvents leftSuffixEvents).2.1
      (right.splitAppend prefixEvents rightSuffixEvents).2.1

/-- Every closed canonical trace has unique active IDs at every prefix cut. -/
theorem Trace.splitPrefix_activeIdsUnique
    {raw : RawPresentation}
    (prefixEvents suffixEvents : List SliceEvent)
    (trace : Trace raw (prefixEvents ++ suffixEvents) [] []) :
    ActiveIdsUnique
      (trace.splitAppend prefixEvents suffixEvents).1 := by
  exact
    Trace.preserves_activeIdsUnique
      (trace.splitAppend prefixEvents suffixEvents).2.1
      (by simp [ActiveIdsUnique, RawPresentation.activeIds])

end TwistedYetter.Kirby.CanonicalTraceLocality
