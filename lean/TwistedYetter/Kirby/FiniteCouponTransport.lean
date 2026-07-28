import TwistedYetter.Kirby.ModularVacuumProjector

/-!
# Finite transport of a tensor-identity coupon

A Kirby topology certificate will only be asked to provide a finite path of
local events.  This file proves the categorical part: at every event the
coupon crosses one morphism by naturality, and a finite sequence preserves
evaluation by induction.

There is no topology axiom and no evaluator-equality axiom in this file.
-/

namespace TwistedYetter.Kirby.FiniteCouponTransport

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ModularVacuumProjector

universe uK uC vC

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [RightRigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]

/--
Integral powers of a tensor-identity automorphism remain natural.

This general lemma is duplicated here at the lower dependency level needed
by finite transport; the legacy two-over-two module currently contains the
same proof above an unrelated encircling dependency.
-/
theorem automorphismPower_naturality
    (η : TensorIdentityAutomorphism C)
    {X Y : C}
    (f : X ⟶ Y)
    (exponent : ℤ) :
    automorphismObjectPower η X exponent ≫ f =
      f ≫ automorphismObjectPower η Y exponent := by
  let componentX : Aut X := η.iso.app X
  let componentY : Aut Y := η.iso.app Y
  change (componentX ^ exponent).hom ≫ f =
    f ≫ (componentY ^ exponent).hom
  induction exponent using Int.induction_on with
  | zero =>
      change 𝟙 X ≫ f = f ≫ 𝟙 Y
      simp
  | @succ n ih =>
      have hx :
          componentX ^ ((n : ℤ) + 1) =
            componentX ^ (n : ℤ) * componentX := by
        rw [zpow_add, zpow_one]
      have hy :
          componentY ^ ((n : ℤ) + 1) =
            componentY ^ (n : ℤ) * componentY := by
        rw [zpow_add, zpow_one]
      rw [hx, hy, CategoryTheory.Aut.Aut_mul_def,
        CategoryTheory.Aut.Aut_mul_def, Iso.trans_hom, Iso.trans_hom]
      calc
        (componentX.hom ≫ (componentX ^ (n : ℤ)).hom) ≫ f =
            componentX.hom ≫
              ((componentX ^ (n : ℤ)).hom ≫ f) :=
          Category.assoc _ _ _
        _ = componentX.hom ≫
              (f ≫ (componentY ^ (n : ℤ)).hom) := by rw [ih]
        _ = (componentX.hom ≫ f) ≫
              (componentY ^ (n : ℤ)).hom :=
          (Category.assoc _ _ _).symm
        _ = (f ≫ componentY.hom) ≫
              (componentY ^ (n : ℤ)).hom := by
          rw [show componentX.hom ≫ f = f ≫ componentY.hom by
            exact (η.iso.hom.naturality f).symm]
        _ = f ≫
              (componentY.hom ≫ (componentY ^ (n : ℤ)).hom) :=
          Category.assoc _ _ _
  | @pred n ih =>
      have hx :
          componentX ^ (-(n : ℤ) - 1) =
            componentX ^ (-(n : ℤ)) * componentX ^ (-1 : ℤ) := by
        exact zpow_add componentX (-(n : ℤ)) (-1)
      have hy :
          componentY ^ (-(n : ℤ) - 1) =
            componentY ^ (-(n : ℤ)) * componentY ^ (-1 : ℤ) := by
        exact zpow_add componentY (-(n : ℤ)) (-1)
      rw [hx, hy, zpow_neg_one, CategoryTheory.Aut.Aut_mul_def,
        CategoryTheory.Aut.Aut_mul_def, Iso.trans_hom, Iso.trans_hom]
      calc
        ((componentX⁻¹).hom ≫
            (componentX ^ (-(n : ℤ))).hom) ≫ f =
            (componentX⁻¹).hom ≫
              ((componentX ^ (-(n : ℤ))).hom ≫ f) :=
          Category.assoc _ _ _
        _ = (componentX⁻¹).hom ≫
              (f ≫ (componentY ^ (-(n : ℤ))).hom) := by rw [ih]
        _ = ((componentX⁻¹).hom ≫ f) ≫
              (componentY ^ (-(n : ℤ))).hom :=
          (Category.assoc _ _ _).symm
        _ = (f ≫ (componentY⁻¹).hom) ≫
              (componentY ^ (-(n : ℤ))).hom := by
          rw [show (componentX⁻¹).hom ≫ f =
              f ≫ (componentY⁻¹).hom by
            exact (η.iso.inv.naturality f).symm]
        _ = f ≫
              ((componentY ^ (-1 : ℤ)).hom ≫
                (componentY ^ (-(n : ℤ))).hom) := by
          rw [zpow_neg_one]
          exact Category.assoc _ _ _

/-- Human-auditable kinds of local events met along a stationary component. -/
inductive EventKind where
  | positiveCrossing
  | negativeCrossing
  | rightCup
  | rightCap
  | leftCup
  | leftCap
  | positiveTwist
  | negativeTwist
  | coupon
  deriving DecidableEq, Repr

/--
One exact local event in which `η^exponent` crosses a morphism.

The two endpoint equations bind the event to the surrounding closed diagram.
They are equations of explicit diagram syntax, not equations of evaluations.
The event kind is retained for topology auditing; categorical soundness uses
the naturality theorem valid for every morphism.
-/
structure Event
    (η : TensorIdentityAutomorphism C)
    (exponent : ℤ)
    (kind : EventKind)
    (before after : Diagram C .unit .unit) where
  sourceObject : C
  targetObject : C
  crossedMorphism : sourceObject ⟶ targetObject
  context :
    Context C
      (.atom sourceObject) (.atom targetObject) .unit .unit
  before_eq :
    Context.plug C context
        (atomicCoupon "character-before-event"
          (automorphismObjectPower η sourceObject exponent) ≫ᵈ
        atomicCoupon "crossed-event" crossedMorphism) =
      before
  after_eq :
    Context.plug C context
        (atomicCoupon "crossed-event" crossedMorphism ≫ᵈ
        atomicCoupon "character-after-event"
          (automorphismObjectPower η targetObject exponent)) =
      after

namespace Event

/-- One event preserves evaluation solely by naturality of `η^exponent`. -/
theorem eval_eq
    {η : TensorIdentityAutomorphism C}
    {exponent : ℤ}
    {kind : EventKind}
    {before after : Diagram C .unit .unit}
    (event : Event η exponent kind before after) :
    Diagram.eval C before = Diagram.eval C after := by
  calc
    Diagram.eval C before =
        Diagram.eval C
          (Context.plug C event.context
            (atomicCoupon "character-before-event"
                (automorphismObjectPower
                  η event.sourceObject exponent) ≫ᵈ
              atomicCoupon "crossed-event" event.crossedMorphism)) :=
      congrArg (Diagram.eval C) event.before_eq.symm
    _ =
        Diagram.eval C
          (Context.plug C event.context
            (atomicCoupon "crossed-event" event.crossedMorphism ≫ᵈ
              atomicCoupon "character-after-event"
                (automorphismObjectPower
                  η event.targetObject exponent))) := by
      apply Context.eval_plug_congr C event.context
      simpa only [Diagram.eval, Category.assoc] using
        automorphismPower_naturality
          η event.crossedMorphism exponent
    _ = Diagram.eval C after :=
      congrArg (Diagram.eval C) event.after_eq

end Event

/--
A finite, ordered coupon-transport path.

The list index makes the number and order of topology events visible.  The
constructors force consecutive endpoints to agree.
-/
inductive Path
    (η : TensorIdentityAutomorphism C)
    (exponent : ℤ) :
    List EventKind →
      Diagram C .unit .unit → Diagram C .unit .unit →
        Type (max uC vC)
  | nil (frame : Diagram C .unit .unit) :
      Path η exponent [] frame frame
  | cons
      {kind : EventKind}
      {rest : List EventKind}
      {first middle last : Diagram C .unit .unit}
      (head : Event η exponent kind first middle)
      (tail : Path η exponent rest middle last) :
      Path η exponent (kind :: rest) first last

namespace Path

/-- A finite coupon path preserves evaluation by induction over its events. -/
theorem eval_eq
    {η : TensorIdentityAutomorphism C}
    {exponent : ℤ}
    {events : List EventKind}
    {before after : Diagram C .unit .unit}
    (path : Path η exponent events before after) :
    Diagram.eval C before = Diagram.eval C after := by
  induction path with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      exact head.eval_eq.trans inductionHypothesis

/-- The number of categorical induction steps is the topology event count. -/
def eventCount
    {η : TensorIdentityAutomorphism C}
    {exponent : ℤ}
    {events : List EventKind}
    {before after : Diagram C .unit .unit}
    (_path : Path η exponent events before after) : Nat :=
  events.length

end Path

end TwistedYetter.Kirby.FiniteCouponTransport
