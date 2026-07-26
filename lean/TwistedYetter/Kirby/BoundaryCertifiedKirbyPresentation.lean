import TwistedYetter.Kirby.BoundaryDerivedHandleChainModel
import TwistedYetter.Kirby.DualHandleConvention
import TwistedYetter.Kirby.KirbyCompleteness

/-!
# Special Kirby presentations with boundary-derived handle chains

The legacy evaluator consumes `SpecialKirbyPresentation`.  That structure
contains a `handleChain` field, so accepting an arbitrary legacy value would
leave the most important topology input unchecked.

This module defines a stricter source type.  Its lower Kirby diagram and
boundary standardization certificate determine the primal handle counts and
boundary maps.  A proof-carrying transpose certificate then determines the
dual/upside-down middle complex used by the Tham 5.11 evaluator.
`toSpecialKirbyPresentation` keeps the primal counts needed by the link
normalization and fills `handleChain` with the certified dual complex; it
never reads a caller-supplied chain model.

The additive equivalence to the fixed marked-homology coordinate type remains
visible.  It is the explicit marking identification, not an identification
between two independently supplied handle complexes.
-/

namespace TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation

open TwistedYetter.Kirby.BoundaryDerivedHandleChain
open TwistedYetter.Kirby.BoundaryDerivedHandleChain.CertifiedClosedPresentation
open TwistedYetter.Kirby.BoundaryDerivedHandleChainModel
open TwistedYetter.Kirby.BoundaryDerivedHandleChainModel.CertifiedClosedPresentation
open TwistedYetter.Kirby.BoundaryStandardization
open TwistedYetter.Kirby.DualHandleConvention
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.PresentationExecutionTrace

universe uD uIso uSlide uP uSphere uH

/--
Diagrammatic semantics for every lower presentation in one theory.

The exact equality `boundary_diagram_sound` binds the serialized evaluator
input to the surgery diagram standardized by the boundary movie.
-/
structure LowerKirbyDiagramSemantics
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    (lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus) where
  formalSurgeryDiagram : FormalPresentation → calculus.Diagram
  formal : lowerTheory.Presentation → FormalPresentation
  boundary_diagram_sound :
    (lower : lowerTheory.Presentation) →
      formalSurgeryDiagram (formal lower) =
        lowerTheory.boundarySurgeryDiagram lower
  execution :
    (lower : lowerTheory.Presentation) →
      ClosedExecutionCertificate (formal lower)
  twoHandleComponent :
    (lower : lowerTheory.Presentation) →
    Fin (lowerTheory.twoHandleCount lower) → ComponentSpec
  two_handle_component_mem :
    (lower : lowerTheory.Presentation) →
    (index : Fin (lowerTheory.twoHandleCount lower)) →
      twoHandleComponent lower index ∈ (formal lower).raw.components
  two_handle_component_role :
    (lower : lowerTheory.Presentation) →
    (index : Fin (lowerTheory.twoHandleCount lower)) →
      (twoHandleComponent lower index).role ≠ .dotted
  twoHandleIndex? :
    (lower : lowerTheory.Presentation) →
      String → Option (Fin (lowerTheory.twoHandleCount lower))
  two_handle_index_roundtrip :
    (lower : lowerTheory.Presentation) →
    (index : Fin (lowerTheory.twoHandleCount lower)) →
      twoHandleIndex? lower
          (twoHandleComponent lower index).componentId =
        some index
  two_handle_index_sound :
    (lower : lowerTheory.Presentation) →
    (componentId : String) →
    (index : Fin (lowerTheory.twoHandleCount lower)) →
      twoHandleIndex? lower componentId = some index →
        componentId = (twoHandleComponent lower index).componentId
  every_two_handle_component_indexed :
    (lower : lowerTheory.Presentation) →
    (component : ComponentSpec) →
      component ∈ (formal lower).raw.components →
      component.role ≠ .dotted →
        ∃ index, twoHandleIndex? lower component.componentId = some index
  dotted_component_unindexed :
    (lower : lowerTheory.Presentation) →
    (component : ComponentSpec) →
      component.role = .dotted →
        twoHandleIndex? lower component.componentId = none
  componentIndexCertificateHash :
    lowerTheory.Presentation → String
  component_index_certificate_hash_shape :
    (lower : lowerTheory.Presentation) →
      RawPresentation.sha256Shape
        (componentIndexCertificateHash lower) = true
  orderedByIncreasingIndex : lowerTheory.Presentation → Prop
  ordering_witness :
    (lower : lowerTheory.Presentation) →
      orderedByIncreasingIndex lower

/--
A special Kirby presentation whose evaluator-side dual handle chain is
forced by its certified boundary completion.

There is deliberately no `handleChain` field.
-/
structure BoundaryCertifiedPresentation
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (lowerBoundary : LowerHandleBoundaryData lowerTheory)
    (sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus)
    (intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport)
    (H2 : Type uH) [AddCommGroup H2] where
  closure : CertifiedClosedPresentation lowerTheory
  /--
  The two displayed adjointness identities certify the transpose maps used
  after turning the primal decomposition upside down.  They determine the
  evaluator's `d2` and `d3`; this is not an independently supplied chain.
  -/
  dualBoundaryCertificate :
    DualBoundaryCertificate
      (derivedHandleBoundaryData
        lowerBoundary sphereTransport intersection closure)
  chainProvenance : DerivationProvenance
  h2ModelCertificateHash : String
  h2_model_certificate_hash_shape :
    RawPresentation.sha256Shape h2ModelCertificateHash = true
  h2ModelEquiv :
    (BoundaryDerivedHandleChainModel.derivedHandleChainModel
      (dualCounts closure.handleCounts)
      dualBoundaryCertificate.dualBoundaryData
      chainProvenance).SecondHomology ≃+ H2

namespace BoundaryCertifiedPresentation

/-- The dual/upside-down handle chain forced by the boundary certificate. -/
def handleChain
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {lowerBoundary : LowerHandleBoundaryData lowerTheory}
    {sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus}
    {intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation :
      BoundaryCertifiedPresentation lowerBoundary sphereTransport
        intersection H2) :
    HandleChainModel (dualCounts presentation.closure.handleCounts) :=
  BoundaryDerivedHandleChainModel.derivedHandleChainModel
    (dualCounts presentation.closure.handleCounts)
    presentation.dualBoundaryCertificate.dualBoundaryData
    presentation.chainProvenance

/--
Convert to the legacy evaluator input.

All legacy diagram fields come from one global semantics object.  The primal
counts and boundary data come from `closure`; the handle chain is their
certified dual.  No independent chain model is caller-supplied here.
-/
def toSpecialKirbyPresentation
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    {lowerBoundary : LowerHandleBoundaryData lowerTheory}
    {sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus}
    {intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation :
      BoundaryCertifiedPresentation lowerBoundary sphereTransport
        intersection H2) :
    SpecialKirbyPresentation H2 where
  formal := semantics.formal presentation.closure.lower
  execution := semantics.execution presentation.closure.lower
  counts := presentation.closure.handleCounts
  twoHandleComponent :=
    semantics.twoHandleComponent presentation.closure.lower
  two_handle_component_mem :=
    semantics.two_handle_component_mem presentation.closure.lower
  two_handle_component_role :=
    semantics.two_handle_component_role presentation.closure.lower
  twoHandleIndex? :=
    semantics.twoHandleIndex? presentation.closure.lower
  two_handle_index_roundtrip :=
    semantics.two_handle_index_roundtrip presentation.closure.lower
  two_handle_index_sound :=
    semantics.two_handle_index_sound presentation.closure.lower
  every_two_handle_component_indexed :=
    semantics.every_two_handle_component_indexed presentation.closure.lower
  dotted_component_unindexed :=
    semantics.dotted_component_unindexed presentation.closure.lower
  componentIndexCertificateHash :=
    semantics.componentIndexCertificateHash presentation.closure.lower
  component_index_certificate_hash_shape :=
    semantics.component_index_certificate_hash_shape
      presentation.closure.lower
  uniqueZeroHandle := presentation.closure.h0_eq_one
  uniqueFourHandle := presentation.closure.h4_eq_one
  orderedByIncreasingIndex :=
    semantics.orderedByIncreasingIndex presentation.closure.lower
  ordering_witness :=
    semantics.ordering_witness presentation.closure.lower
  h2ModelCertificateHash := presentation.h2ModelCertificateHash
  h2_model_certificate_hash_shape :=
    presentation.h2_model_certificate_hash_shape
  handleChain := presentation.handleChain
  h2ModelEquiv := presentation.h2ModelEquiv

/-- The adapter's legacy handle chain is definitionally the certified dual. -/
theorem toSpecialKirbyPresentation_handleChain
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    {lowerBoundary : LowerHandleBoundaryData lowerTheory}
    {sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus}
    {intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation :
      BoundaryCertifiedPresentation lowerBoundary sphereTransport
        intersection H2) :
    (presentation.toSpecialKirbyPresentation semantics).handleChain =
      presentation.handleChain :=
  rfl

/-- The adapter keeps the primal counts used by link normalization. -/
theorem toSpecialKirbyPresentation_counts
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    {lowerBoundary : LowerHandleBoundaryData lowerTheory}
    {sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus}
    {intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation :
      BoundaryCertifiedPresentation lowerBoundary sphereTransport
        intersection H2) :
    (presentation.toSpecialKirbyPresentation semantics).counts =
      presentation.closure.handleCounts :=
  rfl

/-- The serialized link and the standardized surgery boundary are bound. -/
theorem formal_boundary_diagram_sound
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    {lowerBoundary : LowerHandleBoundaryData lowerTheory}
    {sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus}
    {intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation :
      BoundaryCertifiedPresentation lowerBoundary sphereTransport
        intersection H2) :
    semantics.formalSurgeryDiagram
        (presentation.toSpecialKirbyPresentation semantics).formal =
      lowerTheory.boundarySurgeryDiagram presentation.closure.lower :=
  semantics.boundary_diagram_sound presentation.closure.lower

end BoundaryCertifiedPresentation

end TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation
