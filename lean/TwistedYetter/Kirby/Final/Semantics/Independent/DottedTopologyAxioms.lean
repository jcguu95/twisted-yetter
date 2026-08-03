import TwistedYetter.Kirby.Final.Semantics.Independent.IntrinsicDottedCut

/-!
# Independent semantics: dotted-incidence topology boundaries

These are the explicit, category-neutral topology inputs needed before the
role-aware evaluator can interpret a dotted component.  They are separated
from the higher-level entrance axioms only to avoid an import cycle; the unique
public semantic entry still re-exports them transitively.
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
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted)
    (cut : IntrinsicDottedCutTangle diagram
      (presentation.cut.punctureWord dotted role)) : Type

abbrev IntrinsicDottedCutRegluesToDiagram
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted)
    (cut : IntrinsicDottedCutTangle diagram
      (presentation.cut.punctureWord dotted role)) : Prop :=
  Nonempty (IntrinsicDottedCutRegluingWitness
    diagram presentation dotted role cut)

/--
Every literal dotted handle admits an intrinsic oriented cut-tangle
realization whose regluing is the original Kirby diagram.

This is the sole new external topology assertion for the intrinsic route.
It does not assert any categorical or numerical equality.
-/
axiom standardIntrinsicDottedCutRealization
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted) :
    ∃ cut : IntrinsicDottedCutTangle diagram
        (presentation.cut.punctureWord dotted role),
      IntrinsicDottedCutRegluesToDiagram
        diagram presentation dotted role cut

/--
In the simultaneous cut-open diagram:

* every dotted component has exactly one projector marker carrying its exact
  ordered puncture word;
* every projector marker comes from such a dotted component; and
* every puncture occurrence agrees with its recorded position in that word.

The complete left-to-right placement and unchanged exterior context are then
theorems derived from the cut-open trace's transparent transition law; they
are not additional assumptions.

This axiom mentions no category, projector morphism, character, or evaluation
equality.
-/
axiom standardDottedProjectorEventCompleteness
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram) :
    presentation.cut.ProjectorEventsExactlyMatchDottedComponents

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 703
