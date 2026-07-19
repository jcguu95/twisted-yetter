import TwistedYetter.Kirby.FramedSliding
import TwistedYetter.Kirby.Presentation

/-!
# Presentation independence for coupon-decorated framed links

The algebraic move generators are explicit typed diagrams. Reidemeister II
and III, duality snakes, critical-point interchange, and coupon transport are
proved from Mathlib's braided and rigid category laws. Framed Reidemeister I
is tied to an EGNO ribbon structure through two explicit convention equations.
Cut independence is tied to an EGNO spherical structure through the
source-labelled spherical trace theorem.

The final theorem also keeps regular-diagram completeness as a separate
source-backed topology input.  It is not hidden inside the evaluator.
-/

namespace TwistedYetter.Kirby.PresentationIsotopy

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.CategoricalMovie
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.FramingNaturality

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

def atom (X : C) : Boundary C := .atom X

def leftAssociated (X Y Z : C) : Boundary C :=
  .tensor (.tensor (atom X) (atom Y)) (atom Z)

def rightAssociated (X Y Z : C) : Boundary C :=
  .tensor (atom X) (.tensor (atom Y) (atom Z))

/-- Associator as a visible structural coupon. -/
def associatorHomDiagram (X Y Z : C) :
    Diagram C (leftAssociated X Y Z) (rightAssociated X Y Z) :=
  Diagram.coupon "associator-hom" (α_ X Y Z).hom

/-- Inverse associator as a visible structural coupon. -/
def associatorInvDiagram (X Y Z : C) :
    Diagram C (rightAssociated X Y Z) (leftAssociated X Y Z) :=
  Diagram.coupon "associator-inv" (α_ X Y Z).inv

def leftUnitorHomDiagram (X : C) :
    Diagram C (.tensor .unit (atom X)) (atom X) :=
  Diagram.coupon "left-unitor-hom" (λ_ X).hom

def leftUnitorInvDiagram (X : C) :
    Diagram C (atom X) (.tensor .unit (atom X)) :=
  Diagram.coupon "left-unitor-inv" (λ_ X).inv

def rightUnitorHomDiagram (X : C) :
    Diagram C (.tensor (atom X) .unit) (atom X) :=
  Diagram.coupon "right-unitor-hom" (ρ_ X).hom

def rightUnitorInvDiagram (X : C) :
    Diagram C (atom X) (.tensor (atom X) .unit) :=
  Diagram.coupon "right-unitor-inv" (ρ_ X).inv

section Planar

/-- Inserting an identity frame before a diagram is planar isotopy. -/
def identityBefore
    {source target : Boundary C}
    (diagram : Diagram C source target) :
    Diagram C source target :=
  Diagram.identity source ≫ᵈ diagram

theorem identityBefore_sound
    {source target : Boundary C}
    (diagram : Diagram C source target) :
    Diagram.eval C (identityBefore diagram) = Diagram.eval C diagram := by
  simp [identityBefore, Diagram.eval]

/-- Inserting an identity frame after a diagram is planar isotopy. -/
def identityAfter
    {source target : Boundary C}
    (diagram : Diagram C source target) :
    Diagram C source target :=
  diagram ≫ᵈ Diagram.identity target

theorem identityAfter_sound
    {source target : Boundary C}
    (diagram : Diagram C source target) :
    Diagram.eval C (identityAfter diagram) = Diagram.eval C diagram := by
  simp [identityAfter, Diagram.eval]

def compAssocBefore
    {a b c d : Boundary C}
    (first : Diagram C a b)
    (second : Diagram C b c)
    (third : Diagram C c d) :
    Diagram C a d :=
  (first ≫ᵈ second) ≫ᵈ third

def compAssocAfter
    {a b c d : Boundary C}
    (first : Diagram C a b)
    (second : Diagram C b c)
    (third : Diagram C c d) :
    Diagram C a d :=
  first ≫ᵈ (second ≫ᵈ third)

/-- Vertical reassociation does not change evaluation. -/
theorem compAssoc_sound
    {a b c d : Boundary C}
    (first : Diagram C a b)
    (second : Diagram C b c)
    (third : Diagram C c d) :
    Diagram.eval C (compAssocBefore first second third) =
      Diagram.eval C (compAssocAfter first second third) := by
  simp [compAssocBefore, compAssocAfter, Diagram.eval, Category.assoc]

def tensorInterchangeBefore
    {a b c e f g : Boundary C}
    (leftFirst : Diagram C a b)
    (leftSecond : Diagram C b c)
    (rightFirst : Diagram C e f)
    (rightSecond : Diagram C f g) :
    Diagram C (.tensor a e) (.tensor c g) :=
  (leftFirst ⊗ᵈ rightFirst) ≫ᵈ (leftSecond ⊗ᵈ rightSecond)

def tensorInterchangeAfter
    {a b c e f g : Boundary C}
    (leftFirst : Diagram C a b)
    (leftSecond : Diagram C b c)
    (rightFirst : Diagram C e f)
    (rightSecond : Diagram C f g) :
    Diagram C (.tensor a e) (.tensor c g) :=
  (leftFirst ≫ᵈ leftSecond) ⊗ᵈ (rightFirst ≫ᵈ rightSecond)

/--
Disjoint critical events may interchange.  This is exactly functoriality of
the tensor product, not an extra movie axiom.
-/
theorem tensorInterchange_sound
    {a b c e f g : Boundary C}
    (leftFirst : Diagram C a b)
    (leftSecond : Diagram C b c)
    (rightFirst : Diagram C e f)
    (rightSecond : Diagram C f g) :
    Diagram.eval C
        (tensorInterchangeBefore leftFirst leftSecond rightFirst rightSecond) =
      Diagram.eval C
        (tensorInterchangeAfter leftFirst leftSecond rightFirst rightSecond) := by
  exact MonoidalCategory.tensorHom_comp_tensorHom
    (Diagram.eval C leftFirst)
    (Diagram.eval C rightFirst)
    (Diagram.eval C leftSecond)
    (Diagram.eval C rightSecond)

end Planar

section Reidemeister

def reidemeisterIIPositiveBefore (X Y : C) :
    Diagram C (.tensor (atom X) (atom Y)) (.tensor (atom X) (atom Y)) :=
  Diagram.crossing (atom X) (atom Y) ≫ᵈ
    Diagram.crossingInv (atom Y) (atom X)

def reidemeisterIINegativeBefore (X Y : C) :
    Diagram C (.tensor (atom X) (atom Y)) (.tensor (atom X) (atom Y)) :=
  Diagram.crossingInv (atom X) (atom Y) ≫ᵈ
    Diagram.crossing (atom Y) (atom X)

def reidemeisterIIAfter (X Y : C) :
    Diagram C (.tensor (atom X) (atom Y)) (.tensor (atom X) (atom Y)) :=
  Diagram.identity _

theorem reidemeisterIIPositive_sound (X Y : C) :
    Diagram.eval C (reidemeisterIIPositiveBefore X Y) =
      Diagram.eval C (reidemeisterIIAfter X Y) := by
  simp [reidemeisterIIPositiveBefore, reidemeisterIIAfter, Diagram.eval]

theorem reidemeisterIINegative_sound (X Y : C) :
    Diagram.eval C (reidemeisterIINegativeBefore X Y) =
      Diagram.eval C (reidemeisterIIAfter X Y) := by
  simp [reidemeisterIINegativeBefore, reidemeisterIIAfter, Diagram.eval]

/-- Left side of Reidemeister III with every associator visible. -/
def reidemeisterIIIBefore (X Y Z : C) :
    Diagram C (rightAssociated X Y Z) (rightAssociated Z Y X) :=
  associatorInvDiagram X Y Z ≫ᵈ
    (Diagram.crossing (atom X) (atom Y) ⊗ᵈ
      Diagram.identity (atom Z)) ≫ᵈ
    associatorHomDiagram Y X Z ≫ᵈ
    (Diagram.identity (atom Y) ⊗ᵈ
      Diagram.crossing (atom X) (atom Z)) ≫ᵈ
    associatorInvDiagram Y Z X ≫ᵈ
    (Diagram.crossing (atom Y) (atom Z) ⊗ᵈ
      Diagram.identity (atom X)) ≫ᵈ
    associatorHomDiagram Z Y X

/-- Right side of Reidemeister III with every associator visible. -/
def reidemeisterIIIAfter (X Y Z : C) :
    Diagram C (rightAssociated X Y Z) (rightAssociated Z Y X) :=
  (Diagram.identity (atom X) ⊗ᵈ
      Diagram.crossing (atom Y) (atom Z)) ≫ᵈ
    associatorInvDiagram X Z Y ≫ᵈ
    (Diagram.crossing (atom X) (atom Z) ⊗ᵈ
      Diagram.identity (atom Y)) ≫ᵈ
    associatorHomDiagram Z X Y ≫ᵈ
    (Diagram.identity (atom Z) ⊗ᵈ
      Diagram.crossing (atom X) (atom Y))

/-- Reidemeister III is Mathlib's Yang--Baxter theorem. -/
theorem reidemeisterIII_sound (X Y Z : C) :
    Diagram.eval C (reidemeisterIIIBefore X Y Z) =
      Diagram.eval C (reidemeisterIIIAfter X Y Z) := by
  simpa [reidemeisterIIIBefore, reidemeisterIIIAfter,
    associatorHomDiagram, associatorInvDiagram, Diagram.eval,
    Boundary.denote, leftAssociated, rightAssociated, atom] using
    BraidedCategory.yang_baxter X Y Z

def reidemeisterIIPositiveMove (X Y : C) :
    CertifiedMove
      (reidemeisterIIPositiveBefore X Y)
      (reidemeisterIIAfter X Y) where
  label := "framed-Reidemeister-II-positive-negative"
  sound := reidemeisterIIPositive_sound X Y

def reidemeisterIINegativeMove (X Y : C) :
    CertifiedMove
      (reidemeisterIINegativeBefore X Y)
      (reidemeisterIIAfter X Y) where
  label := "framed-Reidemeister-II-negative-positive"
  sound := reidemeisterIINegative_sound X Y

def reidemeisterIIIMove (X Y Z : C) :
    CertifiedMove
      (reidemeisterIIIBefore X Y Z)
      (reidemeisterIIIAfter X Y Z) where
  label := "framed-Reidemeister-III"
  sound := reidemeisterIII_sound X Y Z

end Reidemeister

section Snakes

variable {X : C}

/-- Cup-cap birth/death on an object with a chosen right dual. -/
def rightPrimalSnakeBefore (X : C) [HasRightDual X] :
    Diagram C (atom X) (atom X) :=
  leftUnitorInvDiagram X ≫ᵈ
    (Diagram.cup X ⊗ᵈ Diagram.identity (atom X)) ≫ᵈ
    associatorHomDiagram X Xᘁ X ≫ᵈ
    (Diagram.identity (atom X) ⊗ᵈ Diagram.cap X) ≫ᵈ
    rightUnitorHomDiagram X

theorem rightPrimalSnake_sound (X : C) [HasRightDual X] :
    Diagram.eval C (rightPrimalSnakeBefore X) =
      Diagram.eval C (Diagram.identity (atom X)) := by
  simp only [rightPrimalSnakeBefore, leftUnitorInvDiagram,
    rightUnitorHomDiagram, associatorHomDiagram, Diagram.eval,
    atom, Boundary.denote, tensorHom_id, id_tensorHom]
  slice_lhs 2 4 =>
    exact ExactPairing.evaluation_coevaluation X Xᘁ
  simp

/-- The opposite snake on the chosen right-dual object. -/
def rightDualSnakeBefore (X : C) [HasRightDual X] :
    Diagram C (atom Xᘁ) (atom Xᘁ) :=
  rightUnitorInvDiagram Xᘁ ≫ᵈ
    (Diagram.identity (atom Xᘁ) ⊗ᵈ Diagram.cup X) ≫ᵈ
    associatorInvDiagram Xᘁ X Xᘁ ≫ᵈ
    (Diagram.cap X ⊗ᵈ Diagram.identity (atom Xᘁ)) ≫ᵈ
    leftUnitorHomDiagram Xᘁ

theorem rightDualSnake_sound (X : C) [HasRightDual X] :
    Diagram.eval C (rightDualSnakeBefore X) =
      Diagram.eval C (Diagram.identity (atom Xᘁ)) := by
  simp only [rightDualSnakeBefore, rightUnitorInvDiagram,
    leftUnitorHomDiagram, associatorInvDiagram, Diagram.eval,
    atom, Boundary.denote, tensorHom_id, id_tensorHom]
  slice_lhs 2 4 =>
    exact ExactPairing.coevaluation_evaluation X Xᘁ
  simp

/-- Cup-cap birth/death on an object with a chosen left dual. -/
def leftPrimalSnakeBefore (X : C) [HasLeftDual X] :
    Diagram C (atom X) (atom X) :=
  rightUnitorInvDiagram X ≫ᵈ
    (Diagram.identity (atom X) ⊗ᵈ Diagram.leftCup X) ≫ᵈ
    associatorInvDiagram X (ᘁX) X ≫ᵈ
    (Diagram.leftCap X ⊗ᵈ Diagram.identity (atom X)) ≫ᵈ
    leftUnitorHomDiagram X

theorem leftPrimalSnake_sound (X : C) [HasLeftDual X] :
    Diagram.eval C (leftPrimalSnakeBefore X) =
      Diagram.eval C (Diagram.identity (atom X)) := by
  simp only [leftPrimalSnakeBefore, rightUnitorInvDiagram,
    leftUnitorHomDiagram, associatorInvDiagram, Diagram.eval,
    atom, Boundary.denote, tensorHom_id, id_tensorHom]
  slice_lhs 2 4 =>
    exact ExactPairing.coevaluation_evaluation (ᘁX) X
  simp

/-- The opposite snake on the chosen left-dual object. -/
def leftDualSnakeBefore (X : C) [HasLeftDual X] :
    Diagram C (atom (ᘁX)) (atom (ᘁX)) :=
  leftUnitorInvDiagram (ᘁX) ≫ᵈ
    (Diagram.leftCup X ⊗ᵈ Diagram.identity (atom (ᘁX))) ≫ᵈ
    associatorHomDiagram (ᘁX) X (ᘁX) ≫ᵈ
    (Diagram.identity (atom (ᘁX)) ⊗ᵈ Diagram.leftCap X) ≫ᵈ
    rightUnitorHomDiagram (ᘁX)

theorem leftDualSnake_sound (X : C) [HasLeftDual X] :
    Diagram.eval C (leftDualSnakeBefore X) =
      Diagram.eval C (Diagram.identity (atom (ᘁX))) := by
  simp only [leftDualSnakeBefore, leftUnitorInvDiagram,
    rightUnitorHomDiagram, associatorHomDiagram, Diagram.eval,
    atom, Boundary.denote, tensorHom_id, id_tensorHom]
  slice_lhs 2 4 =>
    exact ExactPairing.evaluation_coevaluation (ᘁX) X
  simp

end Snakes

section Framing

variable [RigidCategory C]

/-- Positive blackboard kink expanded into cup, crossing, and cap. -/
def positiveKink (X : C) : Diagram C (atom X) (atom X) :=
  leftUnitorInvDiagram X ≫ᵈ
    (Diagram.cup X ⊗ᵈ Diagram.identity (atom X)) ≫ᵈ
    (Diagram.crossing (atom X) (atom Xᘁ) ⊗ᵈ
      Diagram.identity (atom X)) ≫ᵈ
    (Diagram.cap X ⊗ᵈ Diagram.identity (atom X)) ≫ᵈ
    leftUnitorHomDiagram X

/-- Negative blackboard kink with inverse crossing. -/
def negativeKink (X : C) : Diagram C (atom X) (atom X) :=
  leftUnitorInvDiagram X ≫ᵈ
    (Diagram.cup X ⊗ᵈ Diagram.identity (atom X)) ≫ᵈ
    (Diagram.crossingInv (atom X) (atom Xᘁ) ⊗ᵈ
      Diagram.identity (atom X)) ≫ᵈ
    (Diagram.cap X ⊗ᵈ Diagram.identity (atom X)) ≫ᵈ
    leftUnitorHomDiagram X

/--
The standard ribbon graphical input identifying blackboard kinks with the
positive and negative twist.  The repository's EGNO ribbon interface supplies
the twist and its balancing/duality laws; these two diagrammatic evaluation
equations remain explicit and source-backed.
-/
structure FramedKinkCompatibility where
  ribbon : RibbonStructure C
  positive_sound : (X : C) →
    Diagram.eval C (positiveKink X) =
      (NaturalTwist.ofRibbon ribbon).iso.hom.app X
  negative_sound : (X : C) →
    Diagram.eval C (negativeKink X) =
      (NaturalTwist.ofRibbon ribbon).iso.inv.app X
  source_ref : String
  source_locator : String

namespace FramedKinkCompatibility

/-- The ribbon twist, viewed through the smaller coupon-transport interface. -/
def twist (data : FramedKinkCompatibility (C := C)) : NaturalTwist C :=
  NaturalTwist.ofRibbon data.ribbon

def positiveTwistDiagram (data : FramedKinkCompatibility (C := C)) (X : C) :
    Diagram C (atom X) (atom X) :=
  atomicCoupon "positive-ribbon-twist" (data.twist.iso.hom.app X)

def negativeTwistDiagram (data : FramedKinkCompatibility (C := C)) (X : C) :
    Diagram C (atom X) (atom X) :=
  atomicCoupon "negative-ribbon-twist" (data.twist.iso.inv.app X)

/-- Framed Reidemeister I transfers a positive kink into framing data. -/
def positiveMove (data : FramedKinkCompatibility (C := C)) (X : C) :
    CertifiedMove (positiveKink X) (data.positiveTwistDiagram X) where
  label := "framed-Reidemeister-I-positive-to-twist"
  sound := data.positive_sound X

/-- Framed Reidemeister I transfers a negative kink into framing data. -/
def negativeMove (data : FramedKinkCompatibility (C := C)) (X : C) :
    CertifiedMove (negativeKink X) (data.negativeTwistDiagram X) where
  label := "framed-Reidemeister-I-negative-to-inverse-twist"
  sound := data.negative_sound X

end FramedKinkCompatibility

end Framing

section Closure

variable [RigidCategory C]

/--
The spherical trace input needed to move a cut around a closed component.
Its cyclicity equation is exactly the algebraic content of cut independence.
-/
structure SphericalCutTrace where
  spherical : SphericalStructure (C := C)
  traceLaws : SphericalTraceLaws spherical

namespace SphericalCutTrace

/-- The closure is the EGNO pivotal trace, not an arbitrary scalar function. -/
def close
    (trace : SphericalCutTrace (C := C))
    (X : C)
    (f : X ⟶ X) :
    𝟙_ C ⟶ 𝟙_ C :=
  pivotalTrace trace.spherical.toPivotalStructure f

/-- Cyclicity is exactly the source-backed spherical trace theorem. -/
theorem cyclic
    (trace : SphericalCutTrace (C := C))
    {X Y : C}
    (f : X ⟶ Y)
    (g : Y ⟶ X) :
    trace.close X (f ≫ g) = trace.close Y (g ≫ f) :=
  trace.traceLaws.cyclic f g

def cutBefore
    (trace : SphericalCutTrace (C := C))
    {X Y : C}
    (f : X ⟶ Y)
    (g : Y ⟶ X) :
    Diagram C .unit .unit :=
  Diagram.coupon "closure-cut-at-X" (trace.close X (f ≫ g))

def cutAfter
    (trace : SphericalCutTrace (C := C))
    {X Y : C}
    (f : X ⟶ Y)
    (g : Y ⟶ X) :
    Diagram C .unit .unit :=
  Diagram.coupon "closure-cut-at-Y" (trace.close Y (g ≫ f))

theorem cut_independence_sound
    (trace : SphericalCutTrace (C := C))
    {X Y : C}
    (f : X ⟶ Y)
    (g : Y ⟶ X) :
    Diagram.eval C (trace.cutBefore f g) =
      Diagram.eval C (trace.cutAfter f g) :=
  trace.cyclic f g

def cutMove
    (trace : SphericalCutTrace (C := C))
    {X Y : C}
    (f : X ⟶ Y)
    (g : Y ⟶ X) :
    CertifiedMove (trace.cutBefore f g) (trace.cutAfter f g) where
  label := "spherical-closure-cut-independence"
  sound := trace.cut_independence_sound f g

end SphericalCutTrace

end Closure

variable [RigidCategory C]

/--
The closed whitelist of evaluator-preserving presentation moves.

There is deliberately no constructor accepting an arbitrary `CertifiedMove`.
Consequently the topological completeness input below cannot smuggle the
desired evaluator equality into a move carrying a misleading tag.
-/
inductive TaggedMove :
    {source target : Boundary C} →
    Diagram C source target → Diagram C source target → Type (max u v)
  | planarIdentityBefore
      {source target : Boundary C}
      (diagram : Diagram C source target) :
      TaggedMove (identityBefore diagram) diagram
  | planarIdentityAfter
      {source target : Boundary C}
      (diagram : Diagram C source target) :
      TaggedMove (identityAfter diagram) diagram
  | planarCompAssoc
      {a b c d : Boundary C}
      (first : Diagram C a b)
      (second : Diagram C b c)
      (third : Diagram C c d) :
      TaggedMove
        (compAssocBefore first second third)
        (compAssocAfter first second third)
  | criticalInterchange
      {a b c e f g : Boundary C}
      (leftFirst : Diagram C a b)
      (leftSecond : Diagram C b c)
      (rightFirst : Diagram C e f)
      (rightSecond : Diagram C f g) :
      TaggedMove
        (tensorInterchangeBefore
          leftFirst leftSecond rightFirst rightSecond)
        (tensorInterchangeAfter
          leftFirst leftSecond rightFirst rightSecond)
  | reidemeisterIIPositive (X Y : C) :
      TaggedMove
        (reidemeisterIIPositiveBefore X Y)
        (reidemeisterIIAfter X Y)
  | reidemeisterIINegative (X Y : C) :
      TaggedMove
        (reidemeisterIINegativeBefore X Y)
        (reidemeisterIIAfter X Y)
  | reidemeisterIII (X Y Z : C) :
      TaggedMove
        (reidemeisterIIIBefore X Y Z)
        (reidemeisterIIIAfter X Y Z)
  | rightPrimalSnake (X : C) [HasRightDual X] :
      TaggedMove
        (rightPrimalSnakeBefore X)
        (Diagram.identity (atom X))
  | rightDualSnake (X : C) [HasRightDual X] :
      TaggedMove
        (rightDualSnakeBefore X)
        (Diagram.identity (atom Xᘁ))
  | leftPrimalSnake (X : C) [HasLeftDual X] :
      TaggedMove
        (leftPrimalSnakeBefore X)
        (Diagram.identity (atom X))
  | leftDualSnake (X : C) [HasLeftDual X] :
      TaggedMove
        (leftDualSnakeBefore X)
        (Diagram.identity (atom (ᘁX)))
  | framedPositive [RigidCategory C]
      (data : FramedKinkCompatibility (C := C))
      (X : C) :
      TaggedMove (positiveKink X) (data.positiveTwistDiagram X)
  | framedNegative [RigidCategory C]
      (data : FramedKinkCompatibility (C := C))
      (X : C) :
      TaggedMove (negativeKink X) (data.negativeTwistDiagram X)
  | couponPositiveCrossing
      {X X' Y Y' : C}
      (f : X ⟶ Y)
      (g : X' ⟶ Y') :
      TaggedMove
        (positiveCrossingBefore f g)
        (positiveCrossingAfter f g)
  | couponNegativeCrossing
      {X X' Y Y' : C}
      (f : X ⟶ Y)
      (g : X' ⟶ Y') :
      TaggedMove
        (negativeCrossingBefore f g)
        (negativeCrossingAfter f g)
  | couponRightCup
      {X Y : C} [HasRightDual X] [HasRightDual Y]
      (f : X ⟶ Y) :
      TaggedMove (rightCupMateSide f) (rightCupOriginalSide f)
  | couponRightCap
      {X Y : C} [HasRightDual X] [HasRightDual Y]
      (f : X ⟶ Y) :
      TaggedMove (rightCapMateSide f) (rightCapOriginalSide f)
  | couponLeftCup
      {X Y : C} [HasLeftDual X] [HasLeftDual Y]
      (f : X ⟶ Y) :
      TaggedMove (leftCupMateSide f) (leftCupOriginalSide f)
  | couponLeftCap
      {X Y : C} [HasLeftDual X] [HasLeftDual Y]
      (f : X ⟶ Y) :
      TaggedMove (leftCapMateSide f) (leftCapOriginalSide f)
  | couponPositiveTwist
      (twist : NaturalTwist C)
      {X Y : C}
      (name : String)
      (f : X ⟶ Y) :
      TaggedMove
        (twist.positiveBefore name f)
        (twist.positiveAfter name f)
  | couponNegativeTwist
      (twist : NaturalTwist C)
      {X Y : C}
      (name : String)
      (f : X ⟶ Y) :
      TaggedMove
        (twist.negativeBefore name f)
        (twist.negativeAfter name f)
  | closureCut
      (trace : SphericalCutTrace (C := C))
      {X Y : C}
      (f : X ⟶ Y)
      (g : Y ⟶ X) :
      TaggedMove (trace.cutBefore f g) (trace.cutAfter f g)

namespace TaggedMove

/-- Every whitelisted move preserves the categorical evaluator. -/
theorem sound
    {source target : Boundary C}
    {before after : Diagram C source target}
    (move : TaggedMove before after) :
    Diagram.eval C before = Diagram.eval C after := by
  cases move with
  | planarIdentityBefore =>
      simp [identityBefore, Diagram.eval]
  | planarIdentityAfter =>
      simp [identityAfter, Diagram.eval]
  | planarCompAssoc first second third =>
      exact compAssoc_sound first second third
  | criticalInterchange leftFirst leftSecond rightFirst rightSecond =>
      exact tensorInterchange_sound
        leftFirst leftSecond rightFirst rightSecond
  | reidemeisterIIPositive X Y =>
      exact reidemeisterIIPositive_sound X Y
  | reidemeisterIINegative X Y =>
      exact reidemeisterIINegative_sound X Y
  | reidemeisterIII X Y Z =>
      exact reidemeisterIII_sound X Y Z
  | rightPrimalSnake X =>
      exact rightPrimalSnake_sound X
  | rightDualSnake X =>
      exact rightDualSnake_sound X
  | leftPrimalSnake X =>
      exact leftPrimalSnake_sound X
  | leftDualSnake X =>
      exact leftDualSnake_sound X
  | framedPositive data X =>
      exact (data.positiveMove X).sound
  | framedNegative data X =>
      exact (data.negativeMove X).sound
  | couponPositiveCrossing f g =>
      exact positiveCrossingMove_sound f g
  | couponNegativeCrossing f g =>
      exact negativeCrossingMove_sound f g
  | couponRightCup f =>
      exact rightCupMove_sound f
  | couponRightCap f =>
      exact rightCapMove_sound f
  | couponLeftCup f =>
      exact leftCupMove_sound f
  | couponLeftCap f =>
      exact leftCapMove_sound f
  | couponPositiveTwist twist name f =>
      exact twist.positive_transport_sound name f
  | couponNegativeTwist twist name f =>
      exact twist.negative_transport_sound name f
  | closureCut trace f g =>
      exact trace.cut_independence_sound f g

end TaggedMove

/--
Reflexive, symmetric, transitive, and context-closed equivalence generated by
tagged evaluator-preserving moves.
-/
inductive GeneratedIsotopy :
    {source target : Boundary C} →
    Diagram C source target → Diagram C source target → Prop
  | refl {source target : Boundary C}
      (frame : Diagram C source target) :
      GeneratedIsotopy frame frame
  | step
      {source target : Boundary C}
      {before after : Diagram C source target}
      (move : TaggedMove before after) :
      GeneratedIsotopy before after
  | symm
      {source target : Boundary C}
      {before after : Diagram C source target} :
      GeneratedIsotopy before after → GeneratedIsotopy after before
  | trans
      {source target : Boundary C}
      {first middle last : Diagram C source target} :
      GeneratedIsotopy first middle →
      GeneratedIsotopy middle last →
      GeneratedIsotopy first last
  | inContext
      {holeSource holeTarget wholeSource wholeTarget : Boundary C}
      {before after : Diagram C holeSource holeTarget}
      (context :
        Context C holeSource holeTarget wholeSource wholeTarget) :
      GeneratedIsotopy before after →
      GeneratedIsotopy
        (Context.plug C context before)
        (Context.plug C context after)

namespace GeneratedIsotopy

/-- Every generated isotopy preserves the categorical evaluator. -/
theorem eval_eq
    {source target : Boundary C}
    {before after : Diagram C source target}
    (isotopy : GeneratedIsotopy before after) :
    Diagram.eval C before = Diagram.eval C after := by
  induction isotopy with
  | refl =>
      rfl
  | step move =>
      exact move.sound
  | symm _ inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans _ _ leftSound rightSound =>
      exact leftSound.trans rightSound
  | inContext context _ inductionHypothesis =>
      exact Context.eval_plug_congr C context inductionHypothesis

end GeneratedIsotopy

section TaggedGenerators

def planarIdentityBeforeIsotopy
    {source target : Boundary C}
    (diagram : Diagram C source target) :
    GeneratedIsotopy (identityBefore diagram) diagram :=
  .step (.planarIdentityBefore diagram)

def planarIdentityAfterIsotopy
    {source target : Boundary C}
    (diagram : Diagram C source target) :
    GeneratedIsotopy (identityAfter diagram) diagram :=
  .step (.planarIdentityAfter diagram)

def planarCompAssocIsotopy
    {a b c d : Boundary C}
    (first : Diagram C a b)
    (second : Diagram C b c)
    (third : Diagram C c d) :
    GeneratedIsotopy
      (compAssocBefore first second third)
      (compAssocAfter first second third) :=
  .step (.planarCompAssoc first second third)

def reidemeisterIIPositiveIsotopy (X Y : C) :
    GeneratedIsotopy
      (reidemeisterIIPositiveBefore X Y)
      (reidemeisterIIAfter X Y) :=
  .step (.reidemeisterIIPositive X Y)

def reidemeisterIINegativeIsotopy (X Y : C) :
    GeneratedIsotopy
      (reidemeisterIINegativeBefore X Y)
      (reidemeisterIIAfter X Y) :=
  .step (.reidemeisterIINegative X Y)

def reidemeisterIIIIsotopy (X Y Z : C) :
    GeneratedIsotopy
      (reidemeisterIIIBefore X Y Z)
      (reidemeisterIIIAfter X Y Z) :=
  .step (.reidemeisterIII X Y Z)

def criticalInterchangeIsotopy
    {a b c e f g : Boundary C}
    (leftFirst : Diagram C a b)
    (leftSecond : Diagram C b c)
    (rightFirst : Diagram C e f)
    (rightSecond : Diagram C f g) :
    GeneratedIsotopy
      (tensorInterchangeBefore
        leftFirst leftSecond rightFirst rightSecond)
      (tensorInterchangeAfter
        leftFirst leftSecond rightFirst rightSecond) :=
  .step (.criticalInterchange
    leftFirst leftSecond rightFirst rightSecond)

def rightPrimalSnakeIsotopy (X : C) [HasRightDual X] :
    GeneratedIsotopy
      (rightPrimalSnakeBefore X)
      (Diagram.identity (atom X)) :=
  .step (.rightPrimalSnake X)

def rightDualSnakeIsotopy (X : C) [HasRightDual X] :
    GeneratedIsotopy
      (rightDualSnakeBefore X)
      (Diagram.identity (atom Xᘁ)) :=
  .step (.rightDualSnake X)

def leftPrimalSnakeIsotopy (X : C) [HasLeftDual X] :
    GeneratedIsotopy
      (leftPrimalSnakeBefore X)
      (Diagram.identity (atom X)) :=
  .step (.leftPrimalSnake X)

def leftDualSnakeIsotopy (X : C) [HasLeftDual X] :
    GeneratedIsotopy
      (leftDualSnakeBefore X)
      (Diagram.identity (atom (ᘁX))) :=
  .step (.leftDualSnake X)

def framedPositiveIsotopy [RigidCategory C]
    (data : FramedKinkCompatibility (C := C))
    (X : C) :
    GeneratedIsotopy (positiveKink X) (data.positiveTwistDiagram X) :=
  .step (.framedPositive data X)

def framedNegativeIsotopy [RigidCategory C]
    (data : FramedKinkCompatibility (C := C))
    (X : C) :
    GeneratedIsotopy (negativeKink X) (data.negativeTwistDiagram X) :=
  .step (.framedNegative data X)

def positiveCouponIsotopy
    {X X' Y Y' : C}
    (f : X ⟶ Y)
    (g : X' ⟶ Y') :
    GeneratedIsotopy
      (positiveCrossingBefore f g)
      (positiveCrossingAfter f g) :=
  .step (.couponPositiveCrossing f g)

def negativeCouponIsotopy
    {X X' Y Y' : C}
    (f : X ⟶ Y)
    (g : X' ⟶ Y') :
    GeneratedIsotopy
      (negativeCrossingBefore f g)
      (negativeCrossingAfter f g) :=
  .step (.couponNegativeCrossing f g)

def rightCupCouponIsotopy
    {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) :
    GeneratedIsotopy (rightCupMateSide f) (rightCupOriginalSide f) :=
  .step (.couponRightCup f)

def rightCapCouponIsotopy
    {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) :
    GeneratedIsotopy (rightCapMateSide f) (rightCapOriginalSide f) :=
  .step (.couponRightCap f)

def leftCupCouponIsotopy
    {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) :
    GeneratedIsotopy (leftCupMateSide f) (leftCupOriginalSide f) :=
  .step (.couponLeftCup f)

def leftCapCouponIsotopy
    {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) :
    GeneratedIsotopy (leftCapMateSide f) (leftCapOriginalSide f) :=
  .step (.couponLeftCap f)

def positiveTwistCouponIsotopy
    (twist : NaturalTwist C)
    {X Y : C}
    (name : String)
    (f : X ⟶ Y) :
    GeneratedIsotopy
      (twist.positiveBefore name f)
      (twist.positiveAfter name f) :=
  .step (.couponPositiveTwist twist name f)

def negativeTwistCouponIsotopy
    (twist : NaturalTwist C)
    {X Y : C}
    (name : String)
    (f : X ⟶ Y) :
    GeneratedIsotopy
      (twist.negativeBefore name f)
      (twist.negativeAfter name f) :=
  .step (.couponNegativeTwist twist name f)

def closureCutIsotopy
    (trace : SphericalCutTrace (C := C))
    {X Y : C}
    (f : X ⟶ Y)
    (g : Y ⟶ X) :
    GeneratedIsotopy (trace.cutBefore f g) (trace.cutAfter f g) :=
  .step (.closureCut trace f g)

end TaggedGenerators

/--
External topology input: regular diagrams representing one framed link are
connected by the generated planar, Reidemeister, framing, snake, coupon, and
cut moves.  This is the standard Reidemeister completeness theorem, not a
categorical evaluator equation.
-/
structure FramedLinkPresentationCompleteness (Link : Type w) where
  represents : Diagram C .unit .unit → Link → Prop
  connected :
    {left right : Diagram C .unit .unit} → {link : Link} →
    represents left link → represents right link →
    GeneratedIsotopy left right
  source_ref : String
  source_locator : String
  source_scope_caveat : String

namespace FramedLinkPresentationCompleteness

/--
The framed-link evaluator is independent of the chosen regular presentation,
relative only to the separately visible topological completeness witness.
-/
theorem presentation_independent
    {Link : Type w}
    (completeness :
      FramedLinkPresentationCompleteness (C := C) Link)
    {left right : Diagram C .unit .unit}
    {link : Link}
    (leftRepresents : completeness.represents left link)
    (rightRepresents : completeness.represents right link) :
    Diagram.eval C left = Diagram.eval C right :=
  (completeness.connected leftRepresents rightRepresents).eval_eq

end FramedLinkPresentationCompleteness

end TwistedYetter.Kirby.PresentationIsotopy
