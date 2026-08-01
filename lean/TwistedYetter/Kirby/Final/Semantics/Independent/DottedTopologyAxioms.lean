import TwistedYetter.Kirby.Final.Semantics.Independent.IntrinsicDottedCut

/-!
# Independent semantics: dotted-incidence topology boundaries

These are the two explicit, category-neutral topology inputs needed before
the role-aware evaluator can interpret a dotted component.  They are
separated from the higher-level entrance axioms only to avoid an import
cycle; the unique public semantic entry still re-exports them transitively.
-/

namespace TwistedYetter.Semantics.Independent

/-!
## Intrinsic cut realization

The witness below is primitive topology vocabulary: it means that regluing
the displayed intrinsic oriented ribbon tangle along its input/output
boundary recovers the exact original Kirby ribbon graph at the selected
dotted handle.  It carries no category, colouring, character, exponent,
morphism, or evaluation equality.
-/

axiom IntrinsicDottedCutRegluingWitness
    (diagram : CombinatorialSpecialKirbyDiagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted)
    (cut : IntrinsicDottedCutTangle diagram
      (diagram.dottedCuts.punctureWord dotted role)) : Type

abbrev IntrinsicDottedCutRegluesToDiagram
    (diagram : CombinatorialSpecialKirbyDiagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted)
    (cut : IntrinsicDottedCutTangle diagram
      (diagram.dottedCuts.punctureWord dotted role)) : Prop :=
  Nonempty (IntrinsicDottedCutRegluingWitness diagram dotted role cut)

/--
Every literal dotted handle admits an intrinsic oriented cut-tangle
realization whose regluing is the original Kirby diagram.

This is the sole new external topology assertion for the intrinsic route.
It does not assert any categorical or numerical equality.
-/
axiom standardIntrinsicDottedCutRealization
    (diagram : CombinatorialSpecialKirbyDiagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted) :
    ∃ cut : IntrinsicDottedCutTangle diagram
        (diagram.dottedCuts.punctureWord dotted role),
      IntrinsicDottedCutRegluesToDiagram diagram dotted role cut

/--
Every oriented dotted handle admits a finite local movie whose source is
exactly its inbound incidence word, whose target is exactly its outbound
incidence word, and whose unique distinguished interior event is its recorded
all-strand projector waist.

The witness contains only finite strand words and standard cut-open events.
Puncture direction is used only to put an occurrence in the source or target;
it does not choose `X` versus `X*` and does not create a character exponent.
The witness contains no category, character, morphism, or evaluation
equality.
-/
axiom standardDottedIncidenceNormalForm
    (diagram : CombinatorialSpecialKirbyDiagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted) :
    ∃ movie : DottedIncidenceMovie diagram.trace dotted
        (diagram.dottedCuts.punctureWord dotted role),
      movie.HasExactIncidenceBoundary

/--
In the simultaneous cut-open diagram, projector markers are exactly the
markers produced by literal dotted components.  Thus every dotted component
has its one distinguished marker and there are no extra projector markers.

This axiom mentions no category, projector morphism, character, or evaluation
equality.
-/
axiom standardDottedProjectorEventCompleteness
    (diagram : CombinatorialSpecialKirbyDiagram) :
    diagram.dottedCuts.ProjectorEventsExactlyMatchDottedComponents

end TwistedYetter.Semantics.Independent
