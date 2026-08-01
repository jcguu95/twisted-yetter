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

theorem puncture_intersection_sign_is_signed
    {trace : CombinatorialLinkTrace}
    (puncture : DottedPuncture trace) :
    puncture.direction.intersectionSign = 1 ∨
      puncture.direction.intersectionSign = -1 := by
  cases puncture.direction <;> simp [PunctureDirection.intersectionSign]

theorem cut_boundary_ribbon_direction_comes_from_the_strand
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (puncture : DottedPuncture diagram.trace) :
    (orientedCutBoundaryPuncture 𝒞 diagram labeling puncture).direction =
      ribbonDirectionOfStrandOrientation
        (diagram.trace.strands puncture.inputStrand).orientation :=
  rfl

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
    (degreeThree : PrimalDegreeThreeBoundaryData diagram) :
    PrimalKirbyH₂ degreeThree =
      (PrimalTwoCycles diagram ⧸
        (primalBoundaryAsCycle degreeThree).range) :=
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
