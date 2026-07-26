import TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry
import TwistedYetter.Kirby.RoleAwareComponentDiagram

/-!
# Simultaneous dotted-cut geometry

This file defines the certificate language required by the role-aware
premodular evaluator.  The certificate contains no category, character,
projector, morphism, scalar, or evaluator equality.

No global existence axiom is declared here.  A downstream theorem must either
construct this geometry from an existing certified presentation or take one
as an explicit, visible topology input.
-/

namespace TwistedYetter.Kirby.SimultaneousDottedCutGeometry

open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.ComponentRibbonIsotopy
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry
open TwistedYetter.Kirby.RoleAwareComponentDiagram

universe uH

/--
A simultaneous, category-neutral exposure of all special dotted disks.

The four exactness fields prevent a role error from being hidden in the
topology certificate:

* each raw dotted component occurs as exactly one special-cut node;
* every special-cut node comes from a raw dotted component;
* no raw dotted component remains inside an ordinary diagram node; and
* every puncture belongs to an ordinary two-handle component.
-/
structure Geometry
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2) where
  cutDiagram :
    RoleAwareDiagram .unit .unit
  erase_isotopy :
    GeneratedIsotopy presentation.componentTermDiagram cutDiagram.erase
  every_dotted_cut_exactly_once :
    (componentIndex :
      Fin presentation.topology.formal.raw.components.length) →
    (presentation.topology.formal.raw.components.get componentIndex).role =
        .dotted →
      cutDiagram.specialDottedIds.count
          (presentation.topology.formal.raw.components.get
            componentIndex).componentId = 1
  every_special_cut_is_dotted :
    (componentId : String) →
      componentId ∈ cutDiagram.specialDottedIds →
        ∃ componentIndex,
          presentation.componentIndexing.indexOf componentId =
              some componentIndex ∧
            (presentation.topology.formal.raw.components.get
              componentIndex).role = .dotted
  dotted_absent_from_ordinary_nodes :
    (componentIndex :
      Fin presentation.topology.formal.raw.components.length) →
    (presentation.topology.formal.raw.components.get componentIndex).role =
        .dotted →
      (presentation.topology.formal.raw.components.get
        componentIndex).componentId ∉ cutDiagram.ordinaryComponentIds
  punctures_are_two_handles :
    (componentId : String) →
      componentId ∈ cutDiagram.punctureIds →
        ∃ twoHandle,
          presentation.topology.twoHandleIndex? componentId = some twoHandle

/-- Stable references supporting only the simultaneous local topology fact. -/
def sourceRefs : List String :=
  LiteratureBackedDottedBoundaryGeometry.sourceRefs

end TwistedYetter.Kirby.SimultaneousDottedCutGeometry
