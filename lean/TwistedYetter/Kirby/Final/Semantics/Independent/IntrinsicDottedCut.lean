import TwistedYetter.Kirby.Final.Semantics.Independent.Diagram

/-!
# Independent semantics: intrinsic dotted cut tangles

This proof-oriented syntax separates three notions that must never be
identified:

* a Kirby component;
* the forward/dual polarity used internally by rigid graphical syntax;
* whether an intrinsic cut incidence belongs to the input or output boundary.

The public boundary of an intrinsic dotted cut contains only ordinary
two-handle component indices.  It contains no planar strand orientation,
category object, character, exponent, morphism, or evaluation equality.
-/

namespace TwistedYetter.Semantics.Independent

/-- Internal polarity in the free rigid ribbon-tangle grammar. -/
inductive IntrinsicRibbonPolarity
  | forward
  | dual
  deriving DecidableEq, Repr

/--
One internally oriented atom.  `dual` is graphical rigidity syntax; it is not
a different colouring of the underlying Kirby component.
-/
structure IntrinsicRibbonAtom (Component : Type*) where
  component : Component
  polarity : IntrinsicRibbonPolarity
  deriving DecidableEq, Repr

def IntrinsicRibbonAtom.forward
    {Component : Type*} (component : Component) :
    IntrinsicRibbonAtom Component :=
  ⟨component, .forward⟩

def IntrinsicRibbonAtom.dual
    {Component : Type*} (component : Component) :
    IntrinsicRibbonAtom Component :=
  ⟨component, .dual⟩

/-- Reverse the graphical polarity without changing the component colour. -/
def IntrinsicRibbonAtom.reverse
    {Component : Type*} :
    IntrinsicRibbonAtom Component → IntrinsicRibbonAtom Component
  | ⟨component, .forward⟩ => .dual component
  | ⟨component, .dual⟩ => .forward component

/--
The free, category-neutral grammar used to describe an intrinsic oriented
ribbon tangle.  Invalid composition is unrepresentable because the middle
word must agree definitionally.

The grammar is intentionally proof-oriented.  It need not be an efficient
diagram evaluator.
-/
inductive IntrinsicRibbonTangle (Component : Type*) :
    List (IntrinsicRibbonAtom Component) →
      List (IntrinsicRibbonAtom Component) → Type _
  | identity (word : List (IntrinsicRibbonAtom Component)) :
      IntrinsicRibbonTangle Component word word
  | compose {source middle target}
      (first : IntrinsicRibbonTangle Component source middle)
      (second : IntrinsicRibbonTangle Component middle target) :
      IntrinsicRibbonTangle Component source target
  | tensor {leftSource leftTarget rightSource rightTarget}
      (left : IntrinsicRibbonTangle Component leftSource leftTarget)
      (right : IntrinsicRibbonTangle Component rightSource rightTarget) :
      IntrinsicRibbonTangle Component
        (leftSource ++ rightSource) (leftTarget ++ rightTarget)
  | coevaluation (component : Component) :
      IntrinsicRibbonTangle Component []
        [.forward component, .dual component]
  | evaluation (component : Component) :
      IntrinsicRibbonTangle Component
        [.dual component, .forward component] []
  | positiveCrossing (left right : IntrinsicRibbonAtom Component) :
      IntrinsicRibbonTangle Component [left, right] [right, left]
  | negativeCrossing (left right : IntrinsicRibbonAtom Component) :
      IntrinsicRibbonTangle Component [left, right] [right, left]
  | positiveTwist (strand : IntrinsicRibbonAtom Component) :
      IntrinsicRibbonTangle Component [strand] [strand]
  | negativeTwist (strand : IntrinsicRibbonAtom Component) :
      IntrinsicRibbonTangle Component [strand] [strand]

/-- Public boundary words contain component colours only, always forward. -/
def intrinsicBoundaryWord {Component : Type*} :
    List Component → List (IntrinsicRibbonAtom Component) :=
  List.map IntrinsicRibbonAtom.forward

/-- The ordinary two-handle component met by one intrinsic cut occurrence. -/
def intrinsicCutTwoHandle
    (diagram : CombinatorialSpecialKirbyDiagram)
    (puncture : DottedPuncture diagram.trace) :
    Fin diagram.handles.hTwo :=
  diagram.handles.twoHandleIndex.symm
    ⟨puncture.twoHandleComponent, puncture.two_handle_role⟩

/-- Input component word of one intrinsic dotted cut. -/
def intrinsicDottedCutInputWord
    (diagram : CombinatorialSpecialKirbyDiagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    List (Fin diagram.handles.hTwo) :=
  (dottedInboundPunctures punctures).map
    (intrinsicCutTwoHandle diagram)

/-- Output component word of one intrinsic dotted cut. -/
def intrinsicDottedCutOutputWord
    (diagram : CombinatorialSpecialKirbyDiagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    List (Fin diagram.handles.hTwo) :=
  (dottedOutboundPunctures punctures).map
    (intrinsicCutTwoHandle diagram)

/--
Category-neutral syntax for the intrinsic tangle obtained by cutting at one
dotted handle.  Its public endpoints are fixed component-colour words.  No
physical vertical-sweep strand word occurs in this type.

This structure is syntax only.  The external topology statement that a
particular Kirby diagram admits a term which reglues to that diagram is a
separate obligation and is deliberately not hidden here as a proof field.
-/
structure IntrinsicDottedCutTangle
    (diagram : CombinatorialSpecialKirbyDiagram)
    (punctures : List (DottedPuncture diagram.trace)) where
  term : IntrinsicRibbonTangle (Fin diagram.handles.hTwo)
    (intrinsicBoundaryWord
      (intrinsicDottedCutInputWord diagram punctures))
    (intrinsicBoundaryWord
      (intrinsicDottedCutOutputWord diagram punctures))

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 3615
