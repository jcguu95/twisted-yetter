import TwistedYetter.Kirby.CategoricalTangle

/-!
# Certified movies of coupon-decorated tangles

Every movie frame has the same typed boundary. Every elementary move carries
its own categorical soundness proof, and the soundness of a complete movie is
derived by transitivity.
-/

namespace TwistedYetter.Kirby.CategoricalMovie

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/-- One named, evaluator-preserving rewrite between typed diagram frames. -/
structure CertifiedMove
    {source target : Boundary C}
    (before after : Diagram C source target) : Type (max u v) where
  label : String
  sound : Diagram.eval C before = Diagram.eval C after

namespace CertifiedMove

/-- The empty local rewrite. -/
def refl {source target : Boundary C} (frame : Diagram C source target) :
    CertifiedMove frame frame where
  label := "reflexivity"
  sound := rfl

/-- Reverse a certified rewrite without introducing a new diagrammatic axiom. -/
def symm {source target : Boundary C}
    {before after : Diagram C source target}
    (move : CertifiedMove before after) :
    CertifiedMove after before where
  label := move.label ++ " (reverse)"
  sound := move.sound.symm

/-- Compose two adjacent certified rewrites. -/
def trans {source target : Boundary C}
    {first middle last : Diagram C source target}
    (left : CertifiedMove first middle)
    (right : CertifiedMove middle last) :
    CertifiedMove first last where
  label := left.label ++ " ; " ++ right.label
  sound := left.sound.trans right.sound

/--
Put a local move into an arbitrary typed surrounding diagram. Soundness is
derived from the context locality theorem.
-/
def inContext
    {holeSource holeTarget wholeSource wholeTarget : Boundary C}
    {before after : Diagram C holeSource holeTarget}
    (move : CertifiedMove before after)
    (context : Context C holeSource holeTarget wholeSource wholeTarget) :
    CertifiedMove (Context.plug C context before) (Context.plug C context after) where
  label := "context(" ++ move.label ++ ")"
  sound := Context.eval_plug_congr C context move.sound

end CertifiedMove

/--
A movie is a typed chain of certified frames. There is no constructor for an
uncertified step.
-/
inductive Movie {source target : Boundary C} :
    Diagram C source target → Diagram C source target → Type (max u v)
  | refl (frame : Diagram C source target) : Movie frame frame
  | step {first middle last : Diagram C source target} :
      CertifiedMove first middle → Movie middle last → Movie first last

namespace Movie

/-- A one-step movie. -/
def one {source target : Boundary C}
    {before after : Diagram C source target}
    (move : CertifiedMove before after) :
    Movie before after :=
  .step move (.refl after)

/-- Append movies whose meeting frame is definitionally the same diagram. -/
def append {source target : Boundary C}
    {first middle last : Diagram C source target} :
    Movie first middle → Movie middle last → Movie first last
  | .refl _, suffix => suffix
  | .step move rest, suffix => .step move (append rest suffix)

/-- Number of non-reflexive certified steps. -/
def stepCount {source target : Boundary C}
    {first last : Diagram C source target} :
    Movie first last → Nat
  | .refl _ => 0
  | .step _ rest => 1 + stepCount rest

/-- Ordered human-auditable labels of all certified steps. -/
def labels {source target : Boundary C}
    {first last : Diagram C source target} :
    Movie first last → List String
  | .refl _ => []
  | .step move rest => move.label :: labels rest

/-- Evaluator equality of a movie is derived from its elementary move proofs. -/
theorem sound {source target : Boundary C}
    {first last : Diagram C source target}
    (movie : Movie first last) :
    Diagram.eval C first = Diagram.eval C last := by
  induction movie with
  | refl =>
      rfl
  | step move rest restSound =>
      exact move.sound.trans restSound

/-- Apply one fixed surrounding context to every frame of a movie. -/
def inContext
    {holeSource holeTarget wholeSource wholeTarget : Boundary C}
    {first last : Diagram C holeSource holeTarget}
    (context : Context C holeSource holeTarget wholeSource wholeTarget) :
    Movie first last →
      Movie (Context.plug C context first) (Context.plug C context last)
  | .refl frame => .refl (Context.plug C context frame)
  | .step move rest =>
      .step (CertifiedMove.inContext move context) (inContext context rest)

end Movie

section PrimitiveCouponMovies

variable {X X' Y Y' : C}

/-- Certified positive-crossing coupon transport. -/
def positiveCrossingMove (f : X ⟶ Y) (g : X' ⟶ Y') :
    CertifiedMove
      (positiveCrossingBefore f g)
      (positiveCrossingAfter f g) where
  label := "coupon-through-positive-crossing"
  sound := positiveCrossingMove_sound f g

/-- Certified negative-crossing coupon transport. -/
def negativeCrossingMove (f : X ⟶ Y) (g : X' ⟶ Y') :
    CertifiedMove
      (negativeCrossingBefore f g)
      (negativeCrossingAfter f g) where
  label := "coupon-through-negative-crossing"
  sound := negativeCrossingMove_sound f g

variable {X Y : C} [HasRightDual X] [HasRightDual Y]

/-- Certified coupon transport through a right-dual cup. -/
def rightCupMove (f : X ⟶ Y) :
    CertifiedMove (rightCupMateSide f) (rightCupOriginalSide f) where
  label := "coupon-through-right-dual-cup"
  sound := rightCupMove_sound f

/-- Certified coupon transport through a right-dual cap. -/
def rightCapMove (f : X ⟶ Y) :
    CertifiedMove (rightCapMateSide f) (rightCapOriginalSide f) where
  label := "coupon-through-right-dual-cap"
  sound := rightCapMove_sound f

variable {X Y : C} [HasLeftDual X] [HasLeftDual Y]

/-- Certified coupon transport through a left-dual cup. -/
def leftCupMove (f : X ⟶ Y) :
    CertifiedMove (leftCupMateSide f) (leftCupOriginalSide f) where
  label := "coupon-through-left-dual-cup"
  sound := leftCupMove_sound f

/-- Certified coupon transport through a left-dual cap. -/
def leftCapMove (f : X ⟶ Y) :
    CertifiedMove (leftCapMateSide f) (leftCapOriginalSide f) where
  label := "coupon-through-left-dual-cap"
  sound := leftCapMove_sound f

end PrimitiveCouponMovies

end TwistedYetter.Kirby.CategoricalMovie
