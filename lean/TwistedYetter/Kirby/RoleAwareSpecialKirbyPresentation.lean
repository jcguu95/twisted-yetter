import TwistedYetter.Kirby.DottedBoundaryGeometry
import TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry
import TwistedYetter.Kirby.SimultaneousDottedCutGeometry

/-!
# Role-aware certified special Kirby presentations

This module contains topology certificate data only.  It connects the
per-generator dotted-disk system used by the handle-chain model with the
simultaneous special-cut diagram used by the premodular evaluator.

No field mentions a category, character, scalar, or evaluator equality.
-/

namespace TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation

open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.DottedBoundaryGeometry
open TwistedYetter.Kirby.RoleAwareComponentDiagram
open TwistedYetter.Kirby.SimultaneousDottedCutGeometry

universe uH

/--
The occurrence of one handle-chain degree-three generator inside the
simultaneous role-aware cut diagram.

The factorization says only where the corresponding special cut occurs.  It
does not assert anything about categorical interpretation or evaluation.
-/
structure GeneratorCutWindow
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    (dottedGeometry : GeometrySystem presentation)
    (simultaneousGeometry : Geometry presentation)
    (generator : Fin presentation.topology.counts.turnedOver.h3) where
  context :
    RoleAwareDiagram.Context
      (dottedGeometry.geometry generator).punctureBoundary
      (dottedGeometry.geometry generator).punctureBoundary
      .unit .unit
  factorization :
    simultaneousGeometry.cutDiagram =
      context.plug
        (.specialDottedCut
          (dottedGeometry.geometry generator).dottedComponent.componentId
          (dottedGeometry.geometry generator).punctureBoundary)

/--
The internal presentation domain of the premodular main line.

The old `GeometrySystem` records the handle-chain generator incidence.  The
new simultaneous geometry records the actual role-aware evaluator diagram.
`generatorCutWindow` binds these two topology certificates without importing
any evaluator statement.
-/
structure Presentation
    (H2 : Type uH) [AddCommGroup H2] where
  canonicalPresentation : CanonicalPresentation H2
  dottedGeometry : GeometrySystem canonicalPresentation
  simultaneousGeometry : Geometry canonicalPresentation
  generatorCutWindow :
    (generator :
      Fin canonicalPresentation.topology.counts.turnedOver.h3) →
      GeneratorCutWindow canonicalPresentation dottedGeometry
        simultaneousGeometry generator

/-- Forget the simultaneous role-aware certificate. -/
def toStandardDottedCanonicalPresentation
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : Presentation H2) :
    LiteratureBackedDottedBoundaryGeometry.StandardDottedCanonicalPresentation
      H2 where
  canonicalPresentation := presentation.canonicalPresentation
  dottedGeometry := presentation.dottedGeometry

end TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation
