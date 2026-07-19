import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Categorical tangle syntax with visible coupons

Tensor bracketing is retained in the boundary syntax. Consequently the
evaluator lands directly in an arbitrary braided monoidal category and does
not rely on an unrecorded strictification.
-/

namespace TwistedYetter.Kirby.CategoricalTangle

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.ExactPairing
open CategoryTheory.HasRightDual

universe u v

/-- A parenthesized tensor word. -/
inductive Boundary (C : Type u)
  | unit
  | atom (object : C)
  | tensor (left right : Boundary C)

namespace Boundary

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- Interpret a parenthesized boundary as an object of the category. -/
def denote : Boundary C → C
  | .unit => 𝟙_ C
  | .atom object => object
  | .tensor left right => denote left ⊗ denote right

end Boundary

/--
Typed diagram syntax. A coupon stores both a human-auditable name and its
actual categorical morphism.
-/
inductive Diagram (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] :
    (source target : Boundary C) → Type (max u v)
  | identity (boundary : Boundary C) : Diagram C boundary boundary
  | coupon {source target : Boundary C} (name : String)
      (morphism : source.denote ⟶ target.denote) :
      Diagram C source target
  | crossing (left right : Boundary C) :
      Diagram C (.tensor left right) (.tensor right left)
  | crossingInv (left right : Boundary C) :
      Diagram C (.tensor left right) (.tensor right left)
  | cup (object : C) [HasRightDual object] :
      Diagram C .unit (.tensor (.atom object) (.atom objectᘁ))
  | cap (object : C) [HasRightDual object] :
      Diagram C (.tensor (.atom objectᘁ) (.atom object)) .unit
  | exactCup (object dual : C) (pairing : ExactPairing object dual) :
      Diagram C .unit (.tensor (.atom object) (.atom dual))
  | exactCap (object dual : C) (pairing : ExactPairing object dual) :
      Diagram C (.tensor (.atom dual) (.atom object)) .unit
  | leftCup (object : C) [HasLeftDual object] :
      Diagram C .unit (.tensor (.atom (ᘁobject)) (.atom object))
  | leftCap (object : C) [HasLeftDual object] :
      Diagram C (.tensor (.atom object) (.atom (ᘁobject))) .unit
  | tensor {a b c d : Boundary C} :
      Diagram C a b → Diagram C c d →
      Diagram C (.tensor a c) (.tensor b d)
  | comp {a b c : Boundary C} :
      Diagram C a b → Diagram C b c → Diagram C a c

namespace Diagram

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

infixr:70 " ⊗ᵈ " => tensor
infixr:60 " ≫ᵈ " => comp

/-- Evaluate the syntax as a categorical morphism. -/
def eval {source target : Boundary C} :
    Diagram C source target → (source.denote ⟶ target.denote)
  | .identity boundary => 𝟙 boundary.denote
  | .coupon _ morphism => morphism
  | .crossing left right =>
      (β_ left.denote right.denote).hom
  | .crossingInv left right =>
      (β_ right.denote left.denote).inv
  | @cup _ _ _ _ object dualWitness =>
      letI : HasRightDual object := dualWitness
      η_ object objectᘁ
  | @cap _ _ _ _ object dualWitness =>
      letI : HasRightDual object := dualWitness
      ε_ object objectᘁ
  | .exactCup object dual pairing =>
      @ExactPairing.coevaluation _ _ _ object dual pairing
  | .exactCap object dual pairing =>
      @ExactPairing.evaluation _ _ _ object dual pairing
  | @leftCup _ _ _ _ object dualWitness =>
      letI : HasLeftDual object := dualWitness
      η_ (ᘁobject) object
  | @leftCap _ _ _ _ object dualWitness =>
      letI : HasLeftDual object := dualWitness
      ε_ (ᘁobject) object
  | .tensor left right => eval left ⊗ₘ eval right
  | .comp first second => eval first ≫ eval second

end Diagram

/--
A typed one-hole context over parenthesized categorical boundaries.
-/
inductive Context (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] :
    (holeSource holeTarget wholeSource wholeTarget : Boundary C) →
    Type (max u v)
  | hole (source target : Boundary C) :
      Context C source target source target
  | compLeft {holeSource holeTarget wholeSource : Boundary C}
      (before : Diagram C wholeSource holeSource) :
      Context C holeSource holeTarget wholeSource holeTarget
  | compRight {holeSource holeTarget wholeTarget : Boundary C}
      (after : Diagram C holeTarget wholeTarget) :
      Context C holeSource holeTarget holeSource wholeTarget
  | tensorLeft {holeSource holeTarget rightSource rightTarget : Boundary C}
      (right : Diagram C rightSource rightTarget) :
      Context C holeSource holeTarget
        (.tensor holeSource rightSource) (.tensor holeTarget rightTarget)
  | tensorRight {leftSource leftTarget holeSource holeTarget : Boundary C}
      (left : Diagram C leftSource leftTarget) :
      Context C holeSource holeTarget
        (.tensor leftSource holeSource) (.tensor leftTarget holeTarget)
  | compose
      {holeSource holeTarget middleSource middleTarget wholeSource wholeTarget :
        Boundary C}
      (inner : Context C holeSource holeTarget middleSource middleTarget)
      (outer : Context C middleSource middleTarget wholeSource wholeTarget) :
      Context C holeSource holeTarget wholeSource wholeTarget

namespace Context

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/-- Fill the sole hole with a boundary-compatible diagram. -/
def plug
    {holeSource holeTarget wholeSource wholeTarget : Boundary C}
    (context : Context C holeSource holeTarget wholeSource wholeTarget)
    (piece : Diagram C holeSource holeTarget) :
    Diagram C wholeSource wholeTarget :=
  match context with
  | .hole _ _ => piece
  | .compLeft before => before ≫ᵈ piece
  | .compRight after => piece ≫ᵈ after
  | .tensorLeft right => piece ⊗ᵈ right
  | .tensorRight left => left ⊗ᵈ piece
  | .compose inner outer => plug outer (plug inner piece)

/--
Local categorical equality is preserved when a diagram is placed in any
well-typed context.
-/
theorem eval_plug_congr
    {holeSource holeTarget wholeSource wholeTarget : Boundary C}
    (context : Context C holeSource holeTarget wholeSource wholeTarget)
    {left right : Diagram C holeSource holeTarget}
    (localEquality : Diagram.eval C left = Diagram.eval C right) :
    Diagram.eval C (plug C context left) =
      Diagram.eval C (plug C context right) := by
  induction context with
  | hole =>
      exact localEquality
  | compLeft before =>
      simpa [plug, Diagram.eval] using
        congrArg (fun morphism => Diagram.eval C before ≫ morphism) localEquality
  | compRight after =>
      simpa [plug, Diagram.eval] using
        congrArg (fun morphism => morphism ≫ Diagram.eval C after) localEquality
  | tensorLeft rightPiece =>
      simpa [plug, Diagram.eval] using
        congrArg
          (fun morphism => morphism ⊗ₘ Diagram.eval C rightPiece) localEquality
  | tensorRight leftPiece =>
      simpa [plug, Diagram.eval] using
        congrArg
          (fun morphism => Diagram.eval C leftPiece ⊗ₘ morphism) localEquality
  | compose inner outer innerIH outerIH =>
      exact outerIH (innerIH localEquality)

end Context

section CouponMoves

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/-- A named coupon between two atomic boundary objects. -/
def atomicCoupon {X Y : C} (name : String) (f : X ⟶ Y) :
    Diagram C (.atom X) (.atom Y) :=
  Diagram.coupon name f

/-- Local diagram before sliding two coupons through a positive crossing. -/
def positiveCrossingBefore {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    Diagram C
      (.tensor (.atom X) (.atom X'))
      (.tensor (.atom Y') (.atom Y)) :=
  (atomicCoupon "f" f ⊗ᵈ atomicCoupon "g" g) ≫ᵈ
    Diagram.crossing (.atom Y) (.atom Y')

/-- Local diagram after sliding two coupons through a positive crossing. -/
def positiveCrossingAfter {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    Diagram C
      (.tensor (.atom X) (.atom X'))
      (.tensor (.atom Y') (.atom Y)) :=
  Diagram.crossing (.atom X) (.atom X') ≫ᵈ
    (atomicCoupon "g" g ⊗ᵈ atomicCoupon "f" f)

/-- The positive-crossing coupon move is sound in every braided category. -/
theorem positiveCrossingMove_sound {X X' Y Y' : C}
    (f : X ⟶ Y) (g : X' ⟶ Y') :
    Diagram.eval C (positiveCrossingBefore f g) =
      Diagram.eval C (positiveCrossingAfter f g) := by
  simpa only [positiveCrossingBefore, positiveCrossingAfter, atomicCoupon,
    Diagram.eval, Boundary.denote] using
    BraidedCategory.braiding_naturality f g

/-- Local diagram before sliding two coupons through a negative crossing. -/
def negativeCrossingBefore {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    Diagram C
      (.tensor (.atom X) (.atom X'))
      (.tensor (.atom Y') (.atom Y)) :=
  (atomicCoupon "f" f ⊗ᵈ atomicCoupon "g" g) ≫ᵈ
    Diagram.crossingInv (.atom Y) (.atom Y')

/-- Local diagram after sliding two coupons through a negative crossing. -/
def negativeCrossingAfter {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    Diagram C
      (.tensor (.atom X) (.atom X'))
      (.tensor (.atom Y') (.atom Y)) :=
  Diagram.crossingInv (.atom X) (.atom X') ≫ᵈ
    (atomicCoupon "g" g ⊗ᵈ atomicCoupon "f" f)

/-- The negative-crossing coupon move is sound in every braided category. -/
theorem negativeCrossingMove_sound {X X' Y Y' : C}
    (f : X ⟶ Y) (g : X' ⟶ Y') :
    Diagram.eval C (negativeCrossingBefore f g) =
      Diagram.eval C (negativeCrossingAfter f g) := by
  simpa only [negativeCrossingBefore, negativeCrossingAfter, atomicCoupon,
    Diagram.eval, Boundary.denote] using
    BraidedCategory.braiding_inv_naturality f g

variable {X Y : C} [HasRightDual X] [HasRightDual Y]

/-- Coupon transported around a right-dual cup, mate on the left side. -/
def rightCupMateSide (f : X ⟶ Y) :
    Diagram C .unit
      (.tensor (.atom Y) (.atom Xᘁ)) :=
  Diagram.cup Y ≫ᵈ
    (Diagram.identity (.atom Y) ⊗ᵈ
      atomicCoupon "right-adjoint-mate(f)" (rightAdjointMate f))

/-- Coupon transported around a right-dual cup, original on the right side. -/
def rightCupOriginalSide (f : X ⟶ Y) :
    Diagram C .unit
      (.tensor (.atom Y) (.atom Xᘁ)) :=
  Diagram.cup X ≫ᵈ
    (atomicCoupon "f" f ⊗ᵈ Diagram.identity (.atom Xᘁ))

/-- Cup transport follows from the exact-pairing triangle identities. -/
theorem rightCupMove_sound (f : X ⟶ Y) :
    Diagram.eval C (rightCupMateSide f) =
      Diagram.eval C (rightCupOriginalSide f) := by
  simpa [rightCupMateSide, rightCupOriginalSide, Diagram.eval] using
    coevaluation_comp_rightAdjointMate f

/-- Coupon transported around a right-dual cap, mate on the left side. -/
def rightCapMateSide (f : X ⟶ Y) :
    Diagram C
      (.tensor (.atom Yᘁ) (.atom X)) .unit :=
  (atomicCoupon "right-adjoint-mate(f)" (rightAdjointMate f) ⊗ᵈ
      Diagram.identity (.atom X)) ≫ᵈ
    Diagram.cap X

/-- Coupon transported around a right-dual cap, original on the right side. -/
def rightCapOriginalSide (f : X ⟶ Y) :
    Diagram C
      (.tensor (.atom Yᘁ) (.atom X)) .unit :=
  (Diagram.identity (.atom Yᘁ) ⊗ᵈ atomicCoupon "f" f) ≫ᵈ
    Diagram.cap Y

/-- Cap transport follows from the exact-pairing triangle identities. -/
theorem rightCapMove_sound (f : X ⟶ Y) :
    Diagram.eval C (rightCapMateSide f) =
      Diagram.eval C (rightCapOriginalSide f) := by
  simpa [rightCapMateSide, rightCapOriginalSide, Diagram.eval] using
    rightAdjointMate_comp_evaluation f

variable {X Y : C} [HasLeftDual X] [HasLeftDual Y]

/-- Coupon transported around a left-dual cup, mate on the left side. -/
def leftCupMateSide (f : X ⟶ Y) :
    Diagram C .unit
      (.tensor (.atom (ᘁX)) (.atom Y)) :=
  Diagram.leftCup Y ≫ᵈ
    (atomicCoupon "left-adjoint-mate(f)" (ᘁf) ⊗ᵈ
      Diagram.identity (.atom Y))

/-- Coupon transported around a left-dual cup, original on the right side. -/
def leftCupOriginalSide (f : X ⟶ Y) :
    Diagram C .unit
      (.tensor (.atom (ᘁX)) (.atom Y)) :=
  Diagram.leftCup X ≫ᵈ
    (Diagram.identity (.atom (ᘁX)) ⊗ᵈ atomicCoupon "f" f)

/-- Left-cup transport follows from the exact-pairing triangle identities. -/
theorem leftCupMove_sound (f : X ⟶ Y) :
    Diagram.eval C (leftCupMateSide f) =
      Diagram.eval C (leftCupOriginalSide f) := by
  simpa [leftCupMateSide, leftCupOriginalSide, Diagram.eval] using
    coevaluation_comp_leftAdjointMate f

/-- Coupon transported around a left-dual cap, mate on the right side. -/
def leftCapMateSide (f : X ⟶ Y) :
    Diagram C
      (.tensor (.atom X) (.atom (ᘁY))) .unit :=
  (Diagram.identity (.atom X) ⊗ᵈ
      atomicCoupon "left-adjoint-mate(f)" (ᘁf)) ≫ᵈ
    Diagram.leftCap X

/-- Coupon transported around a left-dual cap, original on the left side. -/
def leftCapOriginalSide (f : X ⟶ Y) :
    Diagram C
      (.tensor (.atom X) (.atom (ᘁY))) .unit :=
  (atomicCoupon "f" f ⊗ᵈ Diagram.identity (.atom (ᘁY))) ≫ᵈ
    Diagram.leftCap Y

/-- Left-cap transport follows from the exact-pairing triangle identities. -/
theorem leftCapMove_sound (f : X ⟶ Y) :
    Diagram.eval C (leftCapMateSide f) =
      Diagram.eval C (leftCapOriginalSide f) := by
  simpa [leftCapMateSide, leftCapOriginalSide, Diagram.eval] using
    leftAdjointMate_comp_evaluation f

end CouponMoves

end TwistedYetter.Kirby.CategoricalTangle
