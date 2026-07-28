import TwistedYetter.Kirby.Final.Semantics.Independent.Entry
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

/--
The type of the bridge required by the frozen specification.  No inhabitant
is declared here: the current implementation does not contain enough data.
-/
abbrev RequiredTotalBridge :=
  TwistedYetter.Kirby.Presentation.FormalPresentation →
    TwistedYetter.Semantics.Independent.CombinatorialSpecialKirbyDiagram

inductive CurrentBridgeBlocker
  | couponInputOutputWordsMissing
  | dottedPunctureWordsMissing
  | closingThreeHandleDataMissing
  | primalDualHomologyConventionMismatch
  deriving DecidableEq, Repr

def currentBridgeBlockers : List CurrentBridgeBlocker :=
  [
    .couponInputOutputWordsMissing,
    .dottedPunctureWordsMissing,
    .closingThreeHandleDataMissing,
    .primalDualHomologyConventionMismatch
  ]

theorem currentBridgeBlockers_completeList :
    currentBridgeBlockers.length = 4 :=
  rfl

end TwistedYetter.Kirby.Final.CombinatorialSemanticComparison
