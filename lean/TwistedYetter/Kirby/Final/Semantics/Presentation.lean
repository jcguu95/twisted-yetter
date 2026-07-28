import TwistedYetter.Kirby.Final.Semantics.HandleChain

/-!
# Semantic presentation data

Exact component roles, explicit handle-chain data, common exteriors, and
literal local replacements. This file contains no Kirby move algebra.
-/

namespace TwistedYetter.Kirby.Final.SemanticEightMoves

open TwistedYetter.Kirby.Final.SemanticHandleChain
open TwistedYetter.Kirby.Presentation

universe uH

/-! ## Presentations and exact component roles -/

/-- Literal indices of all and only dotted components in one presentation. -/
abbrev DottedComponentIndex (formal : FormalPresentation) :=
  { index : Fin formal.raw.components.length //
    (formal.raw.components.get index).role = .dotted }

/-- Literal indices of all and only primal two-handle components. -/
abbrev TwoHandleComponentIndex (formal : FormalPresentation) :=
  { index : Fin formal.raw.components.length //
    (formal.raw.components.get index).role ≠ .dotted }

/--
Trusted topology boundary: this explicit integral complex, with these bases,
is the handle-chain complex computed from this admitted special Kirby
presentation using the stated upside-down convention.

The complex and bases remain actual data.  This proposition only certifies
their geometric interpretation.  The two equivalences also pin the ordering
of primal one- and two-handle basis vectors to literal diagram components.
It contains no category or evaluator.
-/
axiom IsHandleChainOfPresentation
    (formal : FormalPresentation)
    (counts : HandleCounts)
    (oneHandleComponent :
      Fin counts.h1 ≃ DottedComponentIndex formal)
    (twoHandleComponent :
      Fin counts.h2 ≃ TwoHandleComponentIndex formal)
    (handleChain : HandleChainModel counts.turnedOver) :
    Prop

/--
The independent presentation datum used by the semantic move language.

The admitted link payload and the handle-chain complex are both explicit.
The two counting equalities prevent a presentation from silently declaring a
dotted component to be a two-handle, or an ordinary/specially-dotted
component to be a one-handle.
-/
structure Presentation (H₂ : Type uH) [AddCommGroup H₂] where
  formal : FormalPresentation
  counts : HandleCounts
  one_zero_handle : counts.h0 = 1
  one_four_handle : counts.h4 = 1
  dotted_component_count :
    (formal.raw.components.filter (fun component =>
      component.role == .dotted)).length = counts.h1
  two_handle_component_count :
    (formal.raw.components.filter (fun component =>
      component.role != .dotted)).length = counts.h2
  /--
  Exact indexing of primal one-handles by the literal dotted components.
  This is stronger than a count: no dotted component may disappear from the
  handle basis, and no non-dotted component may enter it.
  -/
  oneHandleComponent :
    Fin counts.h1 ≃ DottedComponentIndex formal
  /--
  Exact indexing of primal two-handles by all and only non-dotted
  components.  `speciallyDotted` is intentionally included here.
  -/
  twoHandleComponent :
    Fin counts.h2 ≃ TwoHandleComponentIndex formal
  /--
  THAM's Kirby formula reads the displayed decomposition upside down:
  primal three-handles are the one-handles of the chain model and primal
  one-handles are its three-handles.  Degree two is unchanged.
  -/
  handleChain : HandleChainModel counts.turnedOver
  handleChain_sound :
    IsHandleChainOfPresentation formal counts oneHandleComponent
      twoHandleComponent handleChain
  handleH₂Equiv : handleChain.SecondHomology ≃+ H₂

/-- Finite index of one component in an admitted presentation. -/
abbrev ComponentIndex
    {H₂ : Type uH} [AddCommGroup H₂]
    (presentation : Presentation H₂) :=
  Fin presentation.formal.raw.components.length

/-- The exact component at a proved finite index. -/
def componentAt
    {H₂ : Type uH} [AddCommGroup H₂]
    (presentation : Presentation H₂)
    (index : ComponentIndex presentation) : ComponentSpec :=
  presentation.formal.raw.components.get index

/-- A resolved dotted one-handle, selected by index rather than by name alone. -/
structure DottedOneHandle
    {H₂ : Type uH} [AddCommGroup H₂]
    (presentation : Presentation H₂) where
  index : ComponentIndex presentation
  role_sound : (componentAt presentation index).role = .dotted

/--
A resolved two-handle component.  `speciallyDotted` remains a two-handle role:
only the literal `dotted` role denotes a one-handle in this specification.
-/
structure TwoHandle
    {H₂ : Type uH} [AddCommGroup H₂]
    (presentation : Presentation H₂) where
  index : ComponentIndex presentation
  role_sound : (componentAt presentation index).role ≠ .dotted

/-! ## Common exterior and exact local replacement -/

/--
One literal local replacement inside two admitted serialized presentations.

The source and target are reconstructed from the same component and event
prefixes and suffixes.  Consequently no move can alter data outside the
declared local window.
-/
structure LocalReplacement
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  commonComponentPrefix : List ComponentSpec
  sourceComponentWindow : List ComponentSpec
  targetComponentWindow : List ComponentSpec
  commonComponentSuffix : List ComponentSpec
  source_components_exact :
    source.formal.raw.components =
      commonComponentPrefix ++ sourceComponentWindow ++
        commonComponentSuffix
  target_components_exact :
    target.formal.raw.components =
      commonComponentPrefix ++ targetComponentWindow ++
        commonComponentSuffix
  commonEventPrefix : List SliceEvent
  sourceEventWindow : List SliceEvent
  targetEventWindow : List SliceEvent
  commonEventSuffix : List SliceEvent
  source_events_exact :
    source.formal.raw.events =
      commonEventPrefix ++ sourceEventWindow ++ commonEventSuffix
  target_events_exact :
    target.formal.raw.events =
      commonEventPrefix ++ targetEventWindow ++ commonEventSuffix
  source_window_nonempty : sourceEventWindow ≠ []
  target_window_nonempty : targetEventWindow ≠ []

/--
Exact lineage for moves that create or delete no link component.

IDs and roles must agree.  Framing is deliberately not required to agree:
the moving two-handle's framing may change under a genuine band sum.
-/
structure SameComponentLineage
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  targetToSource : ComponentIndex target ≃ ComponentIndex source
  id_sound :
    (targetIndex : ComponentIndex target) →
      (componentAt target targetIndex).componentId =
        (componentAt source (targetToSource targetIndex)).componentId
  role_sound :
    (targetIndex : ComponentIndex target) →
      (componentAt target targetIndex).role =
        (componentAt source (targetToSource targetIndex)).role
  orientation_sound :
    (targetIndex : ComponentIndex target) →
      (componentAt target targetIndex).orientation =
        (componentAt source (targetToSource targetIndex)).orientation


end TwistedYetter.Kirby.Final.SemanticEightMoves

