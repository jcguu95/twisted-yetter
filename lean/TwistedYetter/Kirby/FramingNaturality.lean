import TwistedYetter.Fusion.EGNORibbon
import TwistedYetter.Kirby.CategoricalMovie

/-!
# Coupon transport through framing twists

This module records only a natural automorphism of the identity functor. It is
not, by itself, a balanced or ribbon structure. The balancing and duality
compatibility laws belong to the later category-theory layer.
-/

namespace TwistedYetter.Kirby.FramingNaturality

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.CategoricalMovie

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/--
The part of a ribbon twist needed solely for coupon transport through a local
framing twist.
-/
structure NaturalTwist (C : Type u) [Category.{v} C] where
  iso : 𝟭 C ≅ 𝟭 C

namespace NaturalTwist

/-- Forget the balancing law while retaining the underlying natural twist. -/
def ofBalanced [RightRigidCategory C]
    (twist : BalancedTwist C) : NaturalTwist C where
  iso := twist.iso

/-- Every ribbon structure supplies the natural twist used for coupon transport. -/
def ofRibbon [RightRigidCategory C]
    (ribbon : RibbonStructure C) : NaturalTwist C :=
  ofBalanced ribbon.toBalancedTwist

/-- Coupon followed by a positive framing twist. -/
def positiveBefore (twist : NaturalTwist C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram C (.atom X) (.atom Y) :=
  atomicCoupon name f ≫ᵈ
    atomicCoupon "positive-framing-twist" (twist.iso.hom.app Y)

/-- Positive framing twist followed by the transported coupon. -/
def positiveAfter (twist : NaturalTwist C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram C (.atom X) (.atom Y) :=
  atomicCoupon "positive-framing-twist" (twist.iso.hom.app X) ≫ᵈ
    atomicCoupon name f

/-- Positive-twist transport is exactly naturality of the twist. -/
theorem positive_transport_sound (twist : NaturalTwist C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram.eval C (twist.positiveBefore name f) =
      Diagram.eval C (twist.positiveAfter name f) := by
  simpa only [positiveBefore, positiveAfter, atomicCoupon, Diagram.eval] using
    twist.iso.hom.naturality f

/-- Coupon followed by a negative framing twist. -/
def negativeBefore (twist : NaturalTwist C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram C (.atom X) (.atom Y) :=
  atomicCoupon name f ≫ᵈ
    atomicCoupon "negative-framing-twist" (twist.iso.inv.app Y)

/-- Negative framing twist followed by the transported coupon. -/
def negativeAfter (twist : NaturalTwist C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram C (.atom X) (.atom Y) :=
  atomicCoupon "negative-framing-twist" (twist.iso.inv.app X) ≫ᵈ
    atomicCoupon name f

/-- Negative-twist transport is naturality of the inverse twist. -/
theorem negative_transport_sound (twist : NaturalTwist C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram.eval C (twist.negativeBefore name f) =
      Diagram.eval C (twist.negativeAfter name f) := by
  simpa only [negativeBefore, negativeAfter, atomicCoupon, Diagram.eval] using
    twist.iso.inv.naturality f

/-- Positive twist transport packaged as a certified movie step. -/
def positiveMove (twist : NaturalTwist C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    CertifiedMove
      (twist.positiveBefore name f)
      (twist.positiveAfter name f) where
  label := "coupon-through-positive-framing-twist:" ++ name
  sound := twist.positive_transport_sound name f

/-- Negative twist transport packaged as a certified movie step. -/
def negativeMove (twist : NaturalTwist C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    CertifiedMove
      (twist.negativeBefore name f)
      (twist.negativeAfter name f) where
  label := "coupon-through-negative-framing-twist:" ++ name
  sound := twist.negative_transport_sound name f

end NaturalTwist

end TwistedYetter.Kirby.FramingNaturality
