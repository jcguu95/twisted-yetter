/-!
# Coupon-aware typed tangle kernel

This module is the strict diagrammatic bootstrap. It does not claim that the
syntax presents framed tangles or that its future Kirby moves are complete.
-/

namespace TwistedYetter.Kirby

/-- A boundary word is the ordered list of wires cut by a horizontal slice. -/
abbrev Boundary (Wire : Type) := List Wire

/-- Wire labels carry a chosen involutive duality. -/
class WireDuality (Wire : Type) where
  dual : Wire → Wire
  dual_dual : (wire : Wire) → dual (dual wire) = wire

/-- Positive and negative generators are distinct syntax. -/
inductive CrossingSign
  | positive
  | negative
deriving DecidableEq, Repr

/--
Primitive coupons are deliberately separate from crossings and extrema.
Their source and target boundary words are part of their type.
-/
class CouponSignature (Wire : Type) where
  Coupon : Boundary Wire → Boundary Wire → Type

/--
Raw typed framed diagrams in Morse form. Ill-typed composition, tensor
gluing, and non-dual extrema cannot be constructed.
-/
inductive Tangle (Wire : Type) [WireDuality Wire] [CouponSignature Wire] :
    Boundary Wire → Boundary Wire → Type
  | identity (boundary : Boundary Wire) : Tangle Wire boundary boundary
  | coupon {input output : Boundary Wire} :
      CouponSignature.Coupon input output → Tangle Wire input output
  | crossing (sign : CrossingSign) (left right : Wire) :
      Tangle Wire [left, right] [right, left]
  | cup (wire : Wire) :
      Tangle Wire [] [wire, WireDuality.dual wire]
  | cap (wire : Wire) :
      Tangle Wire [WireDuality.dual wire, wire] []
  | twist (sign : CrossingSign) (wire : Wire) :
      Tangle Wire [wire] [wire]
  | tensor {a b c d : Boundary Wire} :
      Tangle Wire a b → Tangle Wire c d → Tangle Wire (a ++ c) (b ++ d)
  | comp {a b c : Boundary Wire} :
      Tangle Wire a b → Tangle Wire b c → Tangle Wire a c

namespace Tangle

infixr:70 " ⊗ₜ " => tensor
infixr:60 " ≫ₜ " => comp

/-- Number of primitive diagram nodes, used by audit artifacts and tests. -/
def nodeCount {Wire : Type} [WireDuality Wire] [CouponSignature Wire]
    {a b : Boundary Wire} :
    Tangle Wire a b → Nat
  | .identity _ => 1
  | .coupon _ => 1
  | .crossing _ _ _ => 1
  | .cup _ => 1
  | .cap _ => 1
  | .twist _ _ => 1
  | .tensor f g => 1 + nodeCount f + nodeCount g
  | .comp f g => 1 + nodeCount f + nodeCount g

end Tangle

/--
A typed one-hole context. The first boundary pair describes the hole; the
second describes the complete diagram after plugging the hole.
-/
inductive Context (Wire : Type) [WireDuality Wire] [CouponSignature Wire] :
    Boundary Wire → Boundary Wire → Boundary Wire → Boundary Wire → Type
  | hole (a b : Boundary Wire) : Context Wire a b a b
  | compLeft {holeIn holeOut wholeIn : Boundary Wire} :
      Tangle Wire wholeIn holeIn →
      Context Wire holeIn holeOut wholeIn holeOut
  | compRight {holeIn holeOut wholeOut : Boundary Wire} :
      Tangle Wire holeOut wholeOut →
      Context Wire holeIn holeOut holeIn wholeOut
  | tensorLeft {holeIn holeOut rightIn rightOut : Boundary Wire} :
      Tangle Wire rightIn rightOut →
      Context Wire holeIn holeOut (holeIn ++ rightIn) (holeOut ++ rightOut)
  | tensorRight {leftIn leftOut holeIn holeOut : Boundary Wire} :
      Tangle Wire leftIn leftOut →
      Context Wire holeIn holeOut (leftIn ++ holeIn) (leftOut ++ holeOut)
  | compose {holeIn holeOut middleIn middleOut wholeIn wholeOut : Boundary Wire} :
      Context Wire holeIn holeOut middleIn middleOut →
      Context Wire middleIn middleOut wholeIn wholeOut →
      Context Wire holeIn holeOut wholeIn wholeOut

namespace Context

/-- Fill the unique typed hole in a context. -/
def plug {Wire : Type} [WireDuality Wire] [CouponSignature Wire]
    {holeIn holeOut wholeIn wholeOut : Boundary Wire}
    (context : Context Wire holeIn holeOut wholeIn wholeOut)
    (piece : Tangle Wire holeIn holeOut) :
    Tangle Wire wholeIn wholeOut :=
  match context with
  | .hole _ _ => piece
  | .compLeft before => before ≫ₜ piece
  | .compRight after => piece ≫ₜ after
  | .tensorLeft right => piece ⊗ₜ right
  | .tensorRight left => left ⊗ₜ piece
  | .compose inner outer => outer.plug (inner.plug piece)

end Context

/--
An equality model for interpreting strict diagrams. Its laws are the ordinary
category and bifunctor laws; no coupon-sliding law is included.
-/
class StrictMonoidalModel (Wire : Type) where
  Hom : Boundary Wire → Boundary Wire → Type
  equiv : {a b : Boundary Wire} → Hom a b → Hom a b → Prop
  equiv_refl : {a b : Boundary Wire} → (f : Hom a b) → equiv f f
  equiv_symm : {a b : Boundary Wire} → {f g : Hom a b} →
    equiv f g → equiv g f
  equiv_trans : {a b : Boundary Wire} → {f g h : Hom a b} →
    equiv f g → equiv g h → equiv f h
  id : (a : Boundary Wire) → Hom a a
  comp : {a b c : Boundary Wire} → Hom a b → Hom b c → Hom a c
  tensor : {a b c d : Boundary Wire} →
    Hom a b → Hom c d → Hom (a ++ c) (b ++ d)
  comp_congr : {a b c : Boundary Wire} → {f f' : Hom a b} →
    {g g' : Hom b c} → equiv f f' → equiv g g' →
    equiv (comp f g) (comp f' g')
  tensor_congr : {a b c d : Boundary Wire} → {f f' : Hom a b} →
    {g g' : Hom c d} → equiv f f' → equiv g g' →
    equiv (tensor f g) (tensor f' g')

namespace StrictMonoidalModel

infix:50 " ≈ₘ " => StrictMonoidalModel.equiv

end StrictMonoidalModel

/-- Interpretation of every primitive generator in a strict monoidal model. -/
structure Interpretation (Wire : Type) [CouponSignature Wire]
    [WireDuality Wire] (Model : StrictMonoidalModel Wire) where
  coupon : {a b : Boundary Wire} →
    CouponSignature.Coupon a b → Model.Hom a b
  crossing : CrossingSign → (left right : Wire) →
    Model.Hom [left, right] [right, left]
  cup : (wire : Wire) →
    Model.Hom [] [wire, WireDuality.dual wire]
  cap : (wire : Wire) →
    Model.Hom [WireDuality.dual wire, wire] []
  twist : CrossingSign → (wire : Wire) → Model.Hom [wire] [wire]

namespace Interpretation

/-- Structural evaluator for typed tangle syntax. -/
def eval {Wire : Type} [WireDuality Wire] [CouponSignature Wire]
    {Model : StrictMonoidalModel Wire}
    (interpretation : Interpretation Wire Model)
    {a b : Boundary Wire} :
    Tangle Wire a b → Model.Hom a b
  | .identity boundary => Model.id boundary
  | .coupon coupon => interpretation.coupon coupon
  | .crossing sign left right => interpretation.crossing sign left right
  | .cup wire => interpretation.cup wire
  | .cap wire => interpretation.cap wire
  | .twist sign wire => interpretation.twist sign wire
  | .tensor f g => Model.tensor (eval interpretation f) (eval interpretation g)
  | .comp f g => Model.comp (eval interpretation f) (eval interpretation g)

/--
The central locality theorem: equality of two local evaluations remains true
after either is plugged into any well-typed surrounding diagram.
-/
theorem eval_plug_congr {Wire : Type} [WireDuality Wire] [CouponSignature Wire]
    {Model : StrictMonoidalModel Wire}
    (interpretation : Interpretation Wire Model)
    {holeIn holeOut wholeIn wholeOut : Boundary Wire}
    (context : Context Wire holeIn holeOut wholeIn wholeOut)
    {left right : Tangle Wire holeIn holeOut}
    (localEquality : Model.equiv
      (eval interpretation left) (eval interpretation right)) :
    Model.equiv
      (eval interpretation (context.plug left))
      (eval interpretation (context.plug right)) := by
  induction context with
  | hole =>
      exact localEquality
  | compLeft before =>
      exact Model.comp_congr (Model.equiv_refl _) localEquality
  | compRight after =>
      exact Model.comp_congr localEquality (Model.equiv_refl _)
  | tensorLeft rightPiece =>
      exact Model.tensor_congr localEquality (Model.equiv_refl _)
  | tensorRight leftPiece =>
      exact Model.tensor_congr (Model.equiv_refl _) localEquality
  | compose inner outer innerIH outerIH =>
      exact outerIH (innerIH localEquality)

end Interpretation

end TwistedYetter.Kirby
