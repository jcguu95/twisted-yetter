import TwistedYetter.Kirby.Final.Semantics.Independent.Entry

/-!
# Kernel checks for the frozen combinatorial semantic distinctions

These checks do not establish downstream conformance.  They ensure that
several dangerous semantic mutations cannot be made by definitional equality.
-/

namespace TwistedYetter.Kirby.Final.CombinatorialSemanticMutationAudit

open TwistedYetter.Semantics.Independent

theorem dotted_ne_speciallyDotted :
    ComponentRole.dotted ≠ ComponentRole.speciallyDotted := by
  decide

theorem ordinary_ne_dotted :
    ComponentRole.ordinary ≠ ComponentRole.dotted := by
  decide

theorem positive_crossing_ne_negative_crossing :
    CrossingSign.positive ≠ CrossingSign.negative := by
  decide

theorem puncture_dotted_component_cannot_be_speciallyDotted
    {trace : CombinatorialLinkTrace}
    (puncture : DottedPuncture trace) :
    (trace.components puncture.dottedComponent).role ≠
      ComponentRole.speciallyDotted := by
  rw [puncture.dotted_role]
  decide

theorem puncture_two_handle_cannot_be_dotted
    {trace : CombinatorialLinkTrace}
    (puncture : DottedPuncture trace) :
    (trace.components puncture.twoHandleComponent).role ≠
      ComponentRole.dotted :=
  puncture.two_handle_role

theorem puncture_exponent_matches_direction
    {trace : CombinatorialLinkTrace}
    (puncture : DottedPuncture trace) :
    puncture.characterExponentSign =
      puncture.direction.characterExponentSign :=
  puncture.exponent_matches_direction

theorem puncture_exponent_is_signed
    {trace : CombinatorialLinkTrace}
    (puncture : DottedPuncture trace) :
    puncture.characterExponentSign = 1 ∨
      puncture.characterExponentSign = -1 := by
  rw [puncture.exponent_matches_direction]
  cases puncture.direction <;> simp [PunctureDirection.characterExponentSign]

theorem handle_counts_are_exact_equivalences
    (diagram : CombinatorialSpecialKirbyDiagram) :
    Nonempty
        (Fin diagram.handles.hOne ≃
          {component : diagram.trace.ComponentId //
            (diagram.trace.components component).role = .dotted}) ∧
      Nonempty
        (Fin diagram.handles.hTwo ≃
          {component : diagram.trace.ComponentId //
            (diagram.trace.components component).role ≠ .dotted}) :=
  ⟨⟨diagram.handles.oneHandleIndex⟩,
    ⟨diagram.handles.twoHandleIndex⟩⟩

theorem kirbyH₂_is_primal_kernel_modulo_image
    {diagram : CombinatorialSpecialKirbyDiagram}
    (degreeThree : DegreeThreeBoundaryData diagram) :
    KirbyH₂ degreeThree =
      (TwoCycles diagram ⧸ (boundaryAsCycle degreeThree).range) :=
  rfl

theorem event_transition_has_one_common_exterior
    {strandCount : ℕ}
    {event : DiagramEvent strandCount}
    {before after : List (Fin strandCount)}
    (transition : EventTransition event before after) :
    ∃ leftContext rightContext,
      before = leftContext ++ event.beforeWord ++ rightContext ∧
      after = leftContext ++ event.afterWord ++ rightContext :=
  transition

end TwistedYetter.Kirby.Final.CombinatorialSemanticMutationAudit
