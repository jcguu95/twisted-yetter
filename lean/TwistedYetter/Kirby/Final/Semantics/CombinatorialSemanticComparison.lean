import TwistedYetter.Kirby.Final.Semantics.Independent.Entry
import TwistedYetter.Kirby.Final.Semantics.DottedCutImplementationBridge
import TwistedYetter.Kirby.Final.Semantics.ClosingHandleImplementationBridge
import TwistedYetter.Kirby.Presentation

/-!
# One-way comparison with the frozen combinatorial semantics

The normative files under `Semantics/Independent/` are read-only here.
This module records the part of the current serialized presentation that
really can be converted without an axiom, and names the data gaps that prevent
a total bridge.
-/

namespace TwistedYetter.Kirby.Final.CombinatorialSemanticComparison

def componentRole :
    TwistedYetter.Kirby.Presentation.ComponentRole →
      TwistedYetter.Semantics.Independent.ComponentRole
  | .ordinary => .ordinary
  | .dotted => .dotted
  | .speciallyDotted => .speciallyDotted

def orientation :
    TwistedYetter.Kirby.Presentation.Orientation →
      TwistedYetter.Semantics.Independent.StrandOrientation
  | .positive => .positive
  | .negative => .negative

def crossingSign :
    TwistedYetter.Kirby.Presentation.CrossingSign →
      TwistedYetter.Semantics.Independent.CrossingSign
  | .positive => .positive
  | .negative => .negative

/--
The component-level part of the bridge is total and contains no assumption.
Provenance strings, blackboard writhe, and cached framing correction are not
normative semantic fields; the resulting integer framing is.
-/
def component
    (input : TwistedYetter.Kirby.Presentation.ComponentSpec) :
    TwistedYetter.Semantics.Independent.Component where
  role := componentRole input.role
  orientation := orientation input.orientation
  integerFraming := input.integerFraming

def componentTable
    (formal : TwistedYetter.Kirby.Presentation.FormalPresentation) :
    Fin formal.raw.components.length →
      TwistedYetter.Semantics.Independent.Component :=
  fun index => component (formal.raw.components.get index)

inductive CurrentBridgeBlocker
  | primalDualHomologyConventionMismatch
  deriving DecidableEq, Repr

def currentBridgeBlockers : List CurrentBridgeBlocker :=
  [
    .primalDualHomologyConventionMismatch
  ]

theorem currentBridgeBlockers_completeList :
    currentBridgeBlockers.length = 1 :=
  rfl

inductive CurrentSemanticWarning
  | punctureDirectionSignRelationNotNormative
  deriving DecidableEq, Repr

def currentSemanticWarnings : List CurrentSemanticWarning :=
  [.punctureDirectionSignRelationNotNormative]

theorem currentSemanticWarnings_completeList :
    currentSemanticWarnings.length = 1 :=
  rfl

/--
The v3 implementation supplies the exact ordered words.  The remaining sign
blocker is narrower: the frozen semantics only requires `±1`, whereas the v3
validator fixes which sign belongs to each disk orientation.
-/
abbrev CertifiedDottedPresentation :=
  DottedCutImplementationBridge.CertifiedDottedPresentation

def dottedCutData
    (certified : CertifiedDottedPresentation) :
    TwistedYetter.Semantics.Independent.DottedCutData certified.trace :=
  certified.toDottedCutData

/--
The total diagram bridge has a proof-bearing closed domain.  A bare
`FormalPresentation` is intentionally insufficient: it has no evidence that
its lower boundary can be capped by three- and four-handles.
-/
abbrev CertifiedClosedDottedPresentation
    {calculus :
      BoundaryStandardization.FramedSurgeryDiagramTheory}
    {lowerTheory :
      BoundaryStandardization.LowerHandlebodyTheory calculus}
    (semantics :
      BoundaryCertifiedKirbyPresentation.LowerKirbyDiagramSemantics
        lowerTheory) :=
  ClosingHandleImplementationBridge.CertifiedClosedDottedPresentation
    semantics

abbrev RequiredTotalBridge
    {calculus :
      BoundaryStandardization.FramedSurgeryDiagramTheory}
    {lowerTheory :
      BoundaryStandardization.LowerHandlebodyTheory calculus}
    (semantics :
      BoundaryCertifiedKirbyPresentation.LowerKirbyDiagramSemantics
        lowerTheory) :=
  CertifiedClosedDottedPresentation semantics →
    TwistedYetter.Semantics.Independent.CombinatorialSpecialKirbyDiagram

/-- The required bridge is now an explicit construction, not an assumption. -/
noncomputable def certifiedClosedDottedBridge
    {calculus :
      BoundaryStandardization.FramedSurgeryDiagramTheory}
    {lowerTheory :
      BoundaryStandardization.LowerHandlebodyTheory calculus}
    (semantics :
      BoundaryCertifiedKirbyPresentation.LowerKirbyDiagramSemantics
        lowerTheory) :
    RequiredTotalBridge semantics :=
  fun certified =>
    ClosingHandleImplementationBridge.CertifiedClosedDottedPresentation.toCombinatorialSpecialKirbyDiagram
      certified

/--
The first comparison gap is closed by the v2 raw syntax itself: every coupon
stores separate ordered input and typed output words plus the exact
replacement index. No semantic assumption is needed to recover these fields.
-/
def couponBoundaryWords :
    TwistedYetter.Kirby.Presentation.SliceEvent →
      Option
        (List String ×
          List TwistedYetter.Kirby.Presentation.StrandState × Nat)
  | .coupon _ _ _ inputs outputs replaceAt =>
      some (inputs, outputs, replaceAt)
  | _ => none

theorem couponBoundaryWords_of_coupon
    (eventId couponId label : String)
    (inputs : List String)
    (outputs : List TwistedYetter.Kirby.Presentation.StrandState)
    (replaceAt : Nat) :
    couponBoundaryWords
        (.coupon eventId couponId label inputs outputs replaceAt) =
      some (inputs, outputs, replaceAt) :=
  rfl

end TwistedYetter.Kirby.Final.CombinatorialSemanticComparison
