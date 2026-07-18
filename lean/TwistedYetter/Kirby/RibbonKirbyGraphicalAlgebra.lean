import TwistedYetter.Kirby.HomologicallyTwistedInvariant
import TwistedYetter.Kirby.PresentationIsotopy

/-!
# Transparent algebraic boundary for the Kirby evaluator

This module collects the standard category-level inputs needed by the
graphical compiler. It deliberately does not contain:

* a whole-presentation evaluator;
* an equality for any Table 2 move;
* a cancellation result;
* a source-bound eight-case compiler.

Coupon transport through crossings and extrema is proved directly from
braiding and rigidity. Coupon transport through a framing twist follows from
naturality of the recorded twist. The two sliding inputs remain visible: the
ordinary sliding law and the `SlidingFamily` whose core equality is derived
from the finite Bärenz--Barrett calculation.
-/

namespace TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.FramedSliding
open TwistedYetter.Kirby.GeneralizedSliding
open TwistedYetter.Kirby.HandleSlide
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.PresentationIsotopy

universe uK uC vC uS uI

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [RightRigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]
variable {categoryData :
  AdmissibleKirbyCategory
    (K := K) (C := C) (S := S) (I := I)}

/--
Exactly the standard graphical algebra accepted by the local compiler.

The package is indexed by the same `categoryData` used by normalization and
generalized sliding, so a sliding family from another snapshot cannot be
substituted by type alone.
-/
structure Input
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)) where
  framedKink : FramedKinkCompatibility (C := C)
  sphericalCut : SphericalCutTrace (C := C)
  ordinarySliding : SourcedSlidingLaw C
  generalizedSliding : SlidingFamily categoryData.slidingData
  categorySnapshotHash : String
  category_snapshot_hash_sound :
    categorySnapshotHash = categoryData.categorySnapshotHash
  algebraCertificateHash : String
  algebra_certificate_hash_shape :
    RawPresentation.sha256Shape algebraCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace Input

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Positive-crossing coupon transport needs no custom graphical axiom. -/
theorem coupon_positive_crossing
    (_input : Input categoryData)
    {X X' Y Y' : C}
    (f : X ⟶ Y)
    (g : X' ⟶ Y') :
    Diagram.eval C (positiveCrossingBefore f g) =
      Diagram.eval C (positiveCrossingAfter f g) :=
  positiveCrossingMove_sound f g

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Negative-crossing coupon transport needs no custom graphical axiom. -/
theorem coupon_negative_crossing
    (_input : Input categoryData)
    {X X' Y Y' : C}
    (f : X ⟶ Y)
    (g : X' ⟶ Y') :
    Diagram.eval C (negativeCrossingBefore f g) =
      Diagram.eval C (negativeCrossingAfter f g) :=
  negativeCrossingMove_sound f g

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Right-cup transport is derived from the rigid triangle identities. -/
theorem coupon_right_cup
    (_input : Input categoryData)
    {X Y : C}
    (f : X ⟶ Y) :
    Diagram.eval C (rightCupMateSide f) =
      Diagram.eval C (rightCupOriginalSide f) :=
  rightCupMove_sound f

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Right-cap transport is derived from the rigid triangle identities. -/
theorem coupon_right_cap
    (_input : Input categoryData)
    {X Y : C}
    (f : X ⟶ Y) :
    Diagram.eval C (rightCapMateSide f) =
      Diagram.eval C (rightCapOriginalSide f) :=
  rightCapMove_sound f

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/--
Left-cup transport uses the left dual induced from right rigidity by the
braiding; no second duality axiom is stored in `Input`.
-/
theorem coupon_left_cup
    (_input : Input categoryData)
    {X Y : C}
    (f : X ⟶ Y) :
    Diagram.eval C (leftCupMateSide f) =
      Diagram.eval C (leftCupOriginalSide f) :=
  leftCupMove_sound f

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Left-cap transport is derived from the same rigid structure. -/
theorem coupon_left_cap
    (_input : Input categoryData)
    {X Y : C}
    (f : X ⟶ Y) :
    Diagram.eval C (leftCapMateSide f) =
      Diagram.eval C (leftCapOriginalSide f) :=
  leftCapMove_sound f

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Positive framing transport is naturality of the ribbon twist. -/
theorem coupon_positive_twist
    (input : Input categoryData)
    {X Y : C}
    (name : String)
    (f : X ⟶ Y) :
    Diagram.eval C
        (input.framedKink.twist.positiveBefore name f) =
      Diagram.eval C
        (input.framedKink.twist.positiveAfter name f) :=
  input.framedKink.twist.positive_transport_sound name f

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Negative framing transport is naturality of the inverse twist. -/
theorem coupon_negative_twist
    (input : Input categoryData)
    {X Y : C}
    (name : String)
    (f : X ⟶ Y) :
    Diagram.eval C
        (input.framedKink.twist.negativeBefore name f) =
      Diagram.eval C
        (input.framedKink.twist.negativeAfter name f) :=
  input.framedKink.twist.negative_transport_sound name f

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Ordinary sliding transports every typed exterior by naturality. -/
theorem ordinary_exterior
    (input : Input categoryData)
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Diagram.eval C
        (ordinaryBefore input.ordinarySliding exterior) =
      Diagram.eval C
        (ordinaryAfter input.ordinarySliding exterior) :=
  ordinary_exterior_transport_sound input.ordinarySliding exterior

/--
Generalized sliding in an arbitrary framed context is derived from the
recorded `SlidingFamily`; no whole-knot equality is an input field.
-/
theorem generalized_framed_exterior
    (input : Input categoryData)
    {source target wholeSource wholeTarget : Boundary C}
    (exterior : Diagram C source target)
    (context :
      Context C
        (.atom (categoryData.slidingData.fixed ⊗ source.denote))
        (.atom (categoryData.slidingData.fixed ⊗ target.denote))
        wholeSource wholeTarget) :
    Diagram.eval C
        (Context.plug C context
          (beforeExterior
            input.generalizedSliding.sourcedFunctorSlidingLaw exterior)) =
      Diagram.eval C
        (Context.plug C context
          (afterExterior
            input.generalizedSliding.sourcedFunctorSlidingLaw exterior)) :=
  SlidingFamily.lemma34Movie_sound
    input.generalizedSliding exterior context

end Input

end TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra
