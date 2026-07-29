import TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation
import TwistedYetter.Kirby.Final.Semantics.DottedCutImplementationBridge

/-!
# Proof-bearing bridge for the closing three-handles

The frozen combinatorial semantics stores only the number of three-handles
and a closing witness.  This module derives both from the already formalized
boundary-standardization movie.  In particular, there is no independently
supplied `hThree` field and no hash is treated as a topology proof.
-/

namespace TwistedYetter.Kirby.Final.ClosingHandleImplementationBridge

open TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation
open TwistedYetter.Kirby.BoundaryStandardization
open TwistedYetter.Kirby.Final.DottedCutImplementationBridge
open TwistedYetter.Semantics.Independent

universe uD uIso uSlide uP

/--
Universe-erased statement that the exact boundary diagram standardizes to a
zero-framed unlink of the stated genus.

The existential still contains the full typed movie.  Packaging it as a
proposition is necessary because the frozen semantic field intentionally
stores a small `Type`, independent of the implementation universes.
-/
def HasClosingCertificateAtGenus
    (calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide})
    (boundaryDiagram : calculus.Diagram)
    (genus : Nat) : Prop :=
  ∃ certificate :
      BoundaryStandardizationCertificate calculus boundaryDiagram,
    certificate.genus = genus

/--
A dotted presentation and a closed completion bound to the same serialized
presentation.

The exact equality below is the critical anti-rebinding condition.  Together
with `LowerKirbyDiagramSemantics.boundary_diagram_sound`, it forces the
boundary movie to start at the boundary surgery diagram of this exact formal
presentation.
-/
structure CertifiedClosedDottedPresentation
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory) where
  dotted : CertifiedDottedPresentation
  closure : CertifiedClosedPresentation lowerTheory
  formal_eq :
    semantics.formal closure.lower = dotted.formal

namespace CertifiedClosedDottedPresentation

/--
The boundary surgery diagram computed from the serialized presentation is
definitionally tied to the source of the supplied standardization movie.
-/
theorem formal_boundary_diagram_eq
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    (certified : CertifiedClosedDottedPresentation semantics) :
    semantics.formalSurgeryDiagram certified.dotted.formal =
      lowerTheory.boundarySurgeryDiagram certified.closure.lower := by
  rw [← certified.formal_eq]
  exact semantics.boundary_diagram_sound certified.closure.lower

/--
The exact closing certificate, transported only along the proved equality of
boundary diagrams.
-/
def closingCertificate
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    (certified : CertifiedClosedDottedPresentation semantics) :
    BoundaryStandardizationCertificate calculus
      (semantics.formalSurgeryDiagram certified.dotted.formal) :=
  certified.formal_boundary_diagram_eq.symm ▸
    certified.closure.boundaryCertificate

/-- All and only literal dotted components of the frozen trace. -/
abbrev OneHandleId
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    (certified : CertifiedClosedDottedPresentation semantics) :=
  {component : certified.dotted.trace.ComponentId //
    (certified.dotted.trace.components component).role = .dotted}

/-- All and only non-dotted components of the frozen trace. -/
abbrev TwoHandleId
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    (certified : CertifiedClosedDottedPresentation semantics) :=
  {component : certified.dotted.trace.ComponentId //
    (certified.dotted.trace.components component).role ≠ .dotted}

/--
Build the frozen handle datum without caller-supplied handle counts.

The one- and two-handle counts are finite-cardinality definitions.  The
three-handle count is the genus certified by the actual boundary movie.
-/
noncomputable def toSpecialHandleData
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    (certified : CertifiedClosedDottedPresentation semantics) :
    SpecialHandleData certified.dotted.trace := by
  classical
  letI : Fintype certified.dotted.trace.ComponentId := by
    dsimp [CombinatorialLinkTrace.ComponentId]
    infer_instance
  exact {
  hOne := Fintype.card certified.OneHandleId
  hTwo := Fintype.card certified.TwoHandleId
  hThree := certified.closingCertificate.genus
  oneHandleIndex := (Fintype.equivFin certified.OneHandleId).symm
  twoHandleIndex := (Fintype.equivFin certified.TwoHandleId).symm
  closingBoundaryCertificate :=
    PLift
      (HasClosingCertificateAtGenus calculus
        (semantics.formalSurgeryDiagram certified.dotted.formal)
        certified.closingCertificate.genus)
  closingBoundaryWitness := ⟨⟨certified.closingCertificate, rfl⟩⟩
  }

/-- The frozen three-handle count is exactly the certified boundary genus. -/
theorem toSpecialHandleData_hThree
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    (certified : CertifiedClosedDottedPresentation semantics) :
    certified.toSpecialHandleData.hThree =
      certified.closingCertificate.genus :=
  rfl

/-- Complete the frozen combinatorial diagram from one proof-bearing source. -/
noncomputable def toCombinatorialSpecialKirbyDiagram
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    (certified : CertifiedClosedDottedPresentation semantics) :
    CombinatorialSpecialKirbyDiagram where
  trace := certified.dotted.trace
  dottedCuts := certified.dotted.toDottedCutData
  handles := certified.toSpecialHandleData

end CertifiedClosedDottedPresentation

end TwistedYetter.Kirby.Final.ClosingHandleImplementationBridge
