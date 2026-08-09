import TwistedYetter.Kirby.Final.Semantics.Independent.CutOpen

/-!
# Independent semantics: dotted-incidence topology boundaries

This is the explicit, category-neutral completeness input needed before the
role-aware evaluator can compile the projector events of a dotted cut.  It is
separated from the higher-level entrance axioms only to avoid an import cycle;
the unique public semantic entry still re-exports it transitively.
-/

namespace TwistedYetter.Semantics.Independent

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
