import TwistedYetter.Fusion.EGNOTensorAutomorphism
import TwistedYetter.Kirby.CategoricalTangle
import TwistedYetter.Kirby.LinearContext
import TwistedYetter.Kirby.LinearDiagram

/-!
# Tensor-automorphism coupon calculus

This module formalizes the local categorical calculation used when a
degree-two cycle representative is changed by a degree-three boundary.

The input is only a monoidal natural automorphism of the identity functor.
Lean derives that its coupons:

* commute with every morphism by naturality;
* split over tensor products and disappear on the tensor unit;
* pass through positive and negative crossings;
* pass through left and right cups and caps as the corresponding mates; and
* cancel against inverse coupons, before or after taking a mate.

`GeneratedCalculation` is a deliberately small proof grammar closed under
symmetry, composition, and insertion into an arbitrary typed diagram
context.  It has no constructor accepting an equality of final invariant
values.

This is the category-theoretic part of Yetter's representative-independence
argument.  It does not by itself identify a degree-three handle boundary
with a particular coupon movie in a serialized Kirby presentation.
-/

namespace TwistedYetter.Kirby.TensorAutomorphismCouponCalculus

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.LinearContext

universe uK u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [RigidCategory C] [BraidedCategory C]

local instance selectedRigidRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

namespace CouponLaws

variable (automorphism : TensorIdentityAutomorphism C)

/-- The positive components satisfy the tensor law by monoidality. -/
theorem tensor_hom (X Y : C) :
    automorphism.iso.hom.app (X ⊗ Y) =
      automorphism.iso.hom.app X ⊗ₘ
        automorphism.iso.hom.app Y := by
  letI : NatTrans.IsMonoidal automorphism.iso.hom :=
    automorphism.monoidal
  simpa using
    (NatTrans.IsMonoidal.tensor
      (τ := automorphism.iso.hom) X Y)

/-- The positive component on the tensor unit is the identity. -/
theorem unit_hom :
    automorphism.iso.hom.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
  letI : NatTrans.IsMonoidal automorphism.iso.hom :=
    automorphism.monoidal
  simpa using
    (NatTrans.IsMonoidal.unit
      (τ := automorphism.iso.hom))

/-- Naturality moves a positive automorphism coupon through any morphism. -/
theorem hom_naturality
    {X Y : C}
    (f : X ⟶ Y) :
    automorphism.iso.hom.app X ≫ f =
      f ≫ automorphism.iso.hom.app Y := by
  simpa using (automorphism.iso.hom.naturality f).symm

/-- Naturality also moves an inverse automorphism coupon through a morphism. -/
theorem inv_naturality
    {X Y : C}
    (f : X ⟶ Y) :
    automorphism.iso.inv.app X ≫ f =
      f ≫ automorphism.iso.inv.app Y := by
  simpa using (automorphism.iso.inv.naturality f).symm

/-- The inverse components satisfy the tensor law; this is derived. -/
theorem tensor_inv (X Y : C) :
    automorphism.iso.inv.app (X ⊗ Y) =
      automorphism.iso.inv.app X ⊗ₘ
        automorphism.iso.inv.app Y := by
  letI : NatTrans.IsMonoidal automorphism.iso.hom :=
    automorphism.monoidal
  simpa using
    (NatTrans.IsMonoidal.tensor
      (τ := automorphism.iso.inv) X Y)

/-- The inverse component on the tensor unit is also the identity. -/
theorem unit_inv :
    automorphism.iso.inv.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
  letI : NatTrans.IsMonoidal automorphism.iso.hom :=
    automorphism.monoidal
  simpa using
    (NatTrans.IsMonoidal.unit
      (τ := automorphism.iso.inv))

/-- A positive coupon followed by its inverse cancels. -/
theorem hom_inv_cancel (X : C) :
    automorphism.iso.hom.app X ≫ automorphism.iso.inv.app X =
      𝟙 X :=
  automorphism.iso.hom_inv_id_app X

/-- An inverse coupon followed by the positive coupon cancels. -/
theorem inv_hom_cancel (X : C) :
    automorphism.iso.inv.app X ≫ automorphism.iso.hom.app X =
      𝟙 X :=
  automorphism.iso.inv_hom_id_app X

/-- Right mates of an inverse/positive pair cancel in the induced order. -/
theorem rightMate_inv_hom_cancel (X : C) :
    (automorphism.iso.inv.app X)ᘁ ≫
        (automorphism.iso.hom.app X)ᘁ =
      𝟙 (Xᘁ) := by
  rw [← comp_rightAdjointMate]
  rw [automorphism.iso.hom_inv_id_app X]
  exact rightAdjointMate_id

/-- Right mates also cancel in the opposite induced order. -/
theorem rightMate_hom_inv_cancel (X : C) :
    (automorphism.iso.hom.app X)ᘁ ≫
        (automorphism.iso.inv.app X)ᘁ =
      𝟙 (Xᘁ) := by
  rw [← comp_rightAdjointMate]
  rw [automorphism.iso.inv_hom_id_app X]
  exact rightAdjointMate_id

/-- Left mates of an inverse/positive pair cancel in the induced order. -/
theorem leftMate_inv_hom_cancel (X : C) :
    (ᘁ(automorphism.iso.inv.app X)) ≫
        (ᘁ(automorphism.iso.hom.app X)) =
      𝟙 (ᘁX) := by
  rw [← comp_leftAdjointMate]
  rw [automorphism.iso.hom_inv_id_app X]
  exact leftAdjointMate_id

/-- Left mates also cancel in the opposite induced order. -/
theorem leftMate_hom_inv_cancel (X : C) :
    (ᘁ(automorphism.iso.hom.app X)) ≫
        (ᘁ(automorphism.iso.inv.app X)) =
      𝟙 (ᘁX) := by
  rw [← comp_leftAdjointMate]
  rw [automorphism.iso.inv_hom_id_app X]
  exact leftAdjointMate_id

end CouponLaws

section SimplePower

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable [Abelian C] [CategoryTheory.Linear K C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
The scalar/coupon comparison remains valid after insertion into any typed
one-hole context.

The theorem is deliberately stated before closing the diagram.  It can be
used at the exact cut selected by a Kirby or attaching-sphere movie.
-/
theorem eval_plug_automorphismCouponPower
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (simple : S)
    (exponent : ℤ)
    {wholeSource wholeTarget : Boundary C}
    (context :
      Context C
        (.atom (data.simple simple))
        (.atom (data.simple simple))
        wholeSource wholeTarget) :
    Diagram.eval C
        (Context.plug C context
          (atomicCoupon "tensor-automorphism-power"
            (data.automorphismCouponPower
              automorphism simple exponent))) =
      data.automorphismScalarPower automorphism simple exponent •
        Diagram.eval C
          (Context.plug C context
            (atomicCoupon "identity" (𝟙 (data.simple simple)))) := by
  simp only [atomicCoupon]
  let linearMap := evalContextLinearMap (R := K) context
  calc
    Diagram.eval C
          (Context.plug C context
            (Diagram.coupon "tensor-automorphism-power"
              (data.automorphismCouponPower
                automorphism simple exponent))) =
        linearMap
          (data.automorphismCouponPower
            automorphism simple exponent) :=
      (evalContextLinearMap_apply
        (R := K) context "tensor-automorphism-power" _).symm
    _ = linearMap
          (data.automorphismScalarPower automorphism simple exponent •
            𝟙 (data.simple simple)) := by
      rw [data.automorphismCouponPower_eq_smul_identity
        automorphism simple exponent]
    _ = data.automorphismScalarPower automorphism simple exponent •
          linearMap (𝟙 (data.simple simple)) :=
      linearMap.map_smul _ _
    _ = data.automorphismScalarPower automorphism simple exponent •
          Diagram.eval C
            (Context.plug C context
              (Diagram.coupon "identity"
                (𝟙 (data.simple simple)))) := by
      rw [evalContextLinearMap_apply (R := K) context "identity"]

end SimplePower

/--
Closed whitelist of local tensor-automorphism coupon calculations.

Every constructor names an exact categorical law.  In particular, there is
no constructor from an arbitrary morphism equality or scalar equality.
-/
inductive LocalMove
    (automorphism : TensorIdentityAutomorphism C) :
    {source target : Boundary C} →
      Diagram C source target → Diagram C source target →
        Type (max u v)
  | homNaturality
      {X Y : C}
      (f : X ⟶ Y) :
      LocalMove automorphism
        (atomicCoupon "tensor-automorphism"
            (automorphism.iso.hom.app X) ≫ᵈ
          atomicCoupon "morphism" f)
        (atomicCoupon "morphism" f ≫ᵈ
          atomicCoupon "tensor-automorphism"
            (automorphism.iso.hom.app Y))
  | invNaturality
      {X Y : C}
      (f : X ⟶ Y) :
      LocalMove automorphism
        (atomicCoupon "tensor-automorphism-inverse"
            (automorphism.iso.inv.app X) ≫ᵈ
          atomicCoupon "morphism" f)
        (atomicCoupon "morphism" f ≫ᵈ
          atomicCoupon "tensor-automorphism-inverse"
            (automorphism.iso.inv.app Y))
  | tensorHom
      (X Y : C) :
      LocalMove automorphism
        (atomicCoupon "tensor-automorphism-on-tensor"
          (automorphism.iso.hom.app (X ⊗ Y)))
        (atomicCoupon "factorized-tensor-automorphism"
          (automorphism.iso.hom.app X ⊗ₘ
            automorphism.iso.hom.app Y))
  | tensorInv
      (X Y : C) :
      LocalMove automorphism
        (atomicCoupon "tensor-automorphism-inverse-on-tensor"
          (automorphism.iso.inv.app (X ⊗ Y)))
        (atomicCoupon "factorized-tensor-automorphism-inverse"
          (automorphism.iso.inv.app X ⊗ₘ
            automorphism.iso.inv.app Y))
  | unitHom :
      LocalMove automorphism
        (atomicCoupon "tensor-automorphism-on-unit"
          (automorphism.iso.hom.app (𝟙_ C)))
        (Diagram.identity (.atom (𝟙_ C)))
  | unitInv :
      LocalMove automorphism
        (atomicCoupon "tensor-automorphism-inverse-on-unit"
          (automorphism.iso.inv.app (𝟙_ C)))
        (Diagram.identity (.atom (𝟙_ C)))
  | positiveCrossing
      {X Y : C} :
      LocalMove automorphism
        (positiveCrossingBefore
          (automorphism.iso.hom.app X)
          (automorphism.iso.hom.app Y))
        (positiveCrossingAfter
          (automorphism.iso.hom.app X)
          (automorphism.iso.hom.app Y))
  | negativeCrossing
      {X Y : C} :
      LocalMove automorphism
        (negativeCrossingBefore
          (automorphism.iso.hom.app X)
          (automorphism.iso.hom.app Y))
        (negativeCrossingAfter
          (automorphism.iso.hom.app X)
          (automorphism.iso.hom.app Y))
  | rightCup
      {X : C} :
      LocalMove automorphism
        (rightCupMateSide (automorphism.iso.hom.app X))
        (rightCupOriginalSide (automorphism.iso.hom.app X))
  | rightCap
      {X : C} :
      LocalMove automorphism
        (rightCapMateSide (automorphism.iso.hom.app X))
        (rightCapOriginalSide (automorphism.iso.hom.app X))
  | leftCup
      {X : C} :
      LocalMove automorphism
        (leftCupMateSide (automorphism.iso.hom.app X))
        (leftCupOriginalSide (automorphism.iso.hom.app X))
  | leftCap
      {X : C} :
      LocalMove automorphism
        (leftCapMateSide (automorphism.iso.hom.app X))
        (leftCapOriginalSide (automorphism.iso.hom.app X))
  | homInvCancel
      (X : C) :
      LocalMove automorphism
        (atomicCoupon "tensor-automorphism"
            (automorphism.iso.hom.app X) ≫ᵈ
          atomicCoupon "tensor-automorphism-inverse"
            (automorphism.iso.inv.app X))
        (Diagram.identity (.atom X))
  | invHomCancel
      (X : C) :
      LocalMove automorphism
        (atomicCoupon "tensor-automorphism-inverse"
            (automorphism.iso.inv.app X) ≫ᵈ
          atomicCoupon "tensor-automorphism"
            (automorphism.iso.hom.app X))
        (Diagram.identity (.atom X))

namespace LocalMove

/-- Every whitelisted local coupon calculation preserves diagram evaluation. -/
theorem sound
    {automorphism : TensorIdentityAutomorphism C}
    {source target : Boundary C}
    {before after : Diagram C source target}
    (move : LocalMove automorphism before after) :
    Diagram.eval C before = Diagram.eval C after := by
  cases move with
  | homNaturality f =>
      exact CouponLaws.hom_naturality automorphism f
  | invNaturality f =>
      exact CouponLaws.inv_naturality automorphism f
  | tensorHom X Y =>
      exact CouponLaws.tensor_hom automorphism X Y
  | tensorInv X Y =>
      exact CouponLaws.tensor_inv automorphism X Y
  | unitHom =>
      exact CouponLaws.unit_hom automorphism
  | unitInv =>
      exact CouponLaws.unit_inv automorphism
  | positiveCrossing =>
      exact positiveCrossingMove_sound _ _
  | negativeCrossing =>
      exact negativeCrossingMove_sound _ _
  | rightCup =>
      exact rightCupMove_sound _
  | rightCap =>
      exact rightCapMove_sound _
  | leftCup =>
      exact leftCupMove_sound _
  | leftCap =>
      exact leftCapMove_sound _
  | homInvCancel X =>
      exact CouponLaws.hom_inv_cancel automorphism X
  | invHomCancel X =>
      exact CouponLaws.inv_hom_cancel automorphism X

end LocalMove

/--
Finite coupon calculation generated by the local whitelist.

Context closure is essential: it says the calculation remains valid inside
an arbitrary larger tangle, without postulating a global graphical law.
-/
inductive GeneratedCalculation
    (automorphism : TensorIdentityAutomorphism C) :
    {source target : Boundary C} →
      Diagram C source target → Diagram C source target → Prop
  | refl
      {source target : Boundary C}
      (diagram : Diagram C source target) :
      GeneratedCalculation automorphism diagram diagram
  | step
      {source target : Boundary C}
      {before after : Diagram C source target}
      (move : LocalMove automorphism before after) :
      GeneratedCalculation automorphism before after
  | symm
      {source target : Boundary C}
      {before after : Diagram C source target} :
      GeneratedCalculation automorphism before after →
      GeneratedCalculation automorphism after before
  | trans
      {source target : Boundary C}
      {first middle last : Diagram C source target} :
      GeneratedCalculation automorphism first middle →
      GeneratedCalculation automorphism middle last →
      GeneratedCalculation automorphism first last
  | inContext
      {holeSource holeTarget wholeSource wholeTarget : Boundary C}
      {before after : Diagram C holeSource holeTarget}
      (context :
        Context C holeSource holeTarget wholeSource wholeTarget) :
      GeneratedCalculation automorphism before after →
      GeneratedCalculation automorphism
        (Context.plug C context before)
        (Context.plug C context after)

namespace GeneratedCalculation

/-- Every generated tensor-automorphism coupon movie preserves evaluation. -/
theorem eval_eq
    {automorphism : TensorIdentityAutomorphism C}
    {source target : Boundary C}
    {before after : Diagram C source target}
    (calculation : GeneratedCalculation automorphism before after) :
    Diagram.eval C before = Diagram.eval C after := by
  induction calculation with
  | refl =>
      rfl
  | step move =>
      exact move.sound
  | symm _ inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans _ _ firstSound secondSound =>
      exact firstSound.trans secondSound
  | inContext context _ inductionHypothesis =>
      exact Context.eval_plug_congr C context inductionHypothesis

end GeneratedCalculation

section Linear

variable {K : Type uK} [CommSemiring K]
variable [Preadditive C] [CategoryTheory.Linear K C]

/--
Linear closure of generated coupon calculations.

This is the proof language needed for Kirby colours, which are finite linear
combinations of fully labelled diagrams rather than single objects.
-/
inductive LinearGeneratedCalculation
    (automorphism : TensorIdentityAutomorphism C) :
    LinearDiagram (R := K) (C := C) .unit .unit →
      LinearDiagram (R := K) (C := C) .unit .unit →
        Type (max uK (max u v))
  | atom
      {before after : Diagram C .unit .unit}
      (calculation :
        GeneratedCalculation automorphism before after) :
      LinearGeneratedCalculation automorphism
        (LinearDiagram.atom (R := K) before)
        (LinearDiagram.atom (R := K) after)
  | add
      {leftBefore leftAfter rightBefore rightAfter :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      LinearGeneratedCalculation automorphism leftBefore leftAfter →
      LinearGeneratedCalculation automorphism rightBefore rightAfter →
      LinearGeneratedCalculation automorphism
        (leftBefore + rightBefore) (leftAfter + rightAfter)
  | smul
      (scalar : K)
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      LinearGeneratedCalculation automorphism before after →
      LinearGeneratedCalculation automorphism
        (scalar • before) (scalar • after)
  | symm
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      LinearGeneratedCalculation automorphism before after →
      LinearGeneratedCalculation automorphism after before
  | trans
      {first middle last :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      LinearGeneratedCalculation automorphism first middle →
      LinearGeneratedCalculation automorphism middle last →
      LinearGeneratedCalculation automorphism first last

namespace LinearGeneratedCalculation

/-- Every generated linear coupon calculation preserves linear evaluation. -/
theorem eval_eq
    {automorphism : TensorIdentityAutomorphism C}
    {before after :
      LinearDiagram (R := K) (C := C) .unit .unit}
    (calculation :
      LinearGeneratedCalculation automorphism before after) :
    LinearDiagram.eval before = LinearDiagram.eval after := by
  induction calculation with
  | atom calculation =>
      simpa only [LinearDiagram.eval_atom] using calculation.eval_eq
  | add _ _ leftSound rightSound =>
      simpa only [map_add] using
        congrArg₂ (· + ·) leftSound rightSound
  | smul scalar _ sound =>
      simpa only [map_smul] using
        congrArg (fun value => scalar • value) sound
  | symm _ sound =>
      exact sound.symm
  | trans _ _ firstSound secondSound =>
      exact firstSound.trans secondSound

end LinearGeneratedCalculation

end Linear

section FusionLinear

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable [Abelian C] [CategoryTheory.Linear K C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
Fusion-aware linear coupon calculations.

The extra base constructor does not accept an equality.  It names exactly the
proved comparison between an integral automorphism coupon and the scalar
coefficient used by the evaluator, at one explicit typed cut.
-/
inductive FusionLinearGeneratedCalculation
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C) :
    LinearDiagram (R := K) (C := C) .unit .unit →
      LinearDiagram (R := K) (C := C) .unit .unit →
        Type (max uK (max u v))
  | generated
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit}
      (calculation :
        LinearGeneratedCalculation automorphism before after) :
      FusionLinearGeneratedCalculation data automorphism before after
  | simplePower
      (simple : S)
      (exponent : ℤ)
      (context :
        Context C
          (.atom (data.simple simple))
          (.atom (data.simple simple))
          .unit .unit) :
      FusionLinearGeneratedCalculation data automorphism
        (LinearDiagram.atom (R := K)
          (Context.plug C context
            (atomicCoupon "tensor-automorphism-power"
              (data.automorphismCouponPower
                automorphism simple exponent))))
        (data.automorphismScalarPower automorphism simple exponent •
          LinearDiagram.atom (R := K)
            (Context.plug C context
              (atomicCoupon "identity"
                (𝟙 (data.simple simple)))))
  | add
      {leftBefore leftAfter rightBefore rightAfter :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      FusionLinearGeneratedCalculation
          data automorphism leftBefore leftAfter →
      FusionLinearGeneratedCalculation
          data automorphism rightBefore rightAfter →
      FusionLinearGeneratedCalculation data automorphism
        (leftBefore + rightBefore) (leftAfter + rightAfter)
  | smul
      (scalar : K)
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      FusionLinearGeneratedCalculation
          data automorphism before after →
      FusionLinearGeneratedCalculation data automorphism
        (scalar • before) (scalar • after)
  | symm
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      FusionLinearGeneratedCalculation
          data automorphism before after →
      FusionLinearGeneratedCalculation
          data automorphism after before
  | trans
      {first middle last :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      FusionLinearGeneratedCalculation
          data automorphism first middle →
      FusionLinearGeneratedCalculation
          data automorphism middle last →
      FusionLinearGeneratedCalculation data automorphism first last

namespace FusionLinearGeneratedCalculation

/-- Every fusion-aware generated calculation preserves linear evaluation. -/
theorem eval_eq
    {data : FusionCategoryData (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {before after :
      LinearDiagram (R := K) (C := C) .unit .unit}
    (calculation :
      FusionLinearGeneratedCalculation
        data automorphism before after) :
    LinearDiagram.eval before = LinearDiagram.eval after := by
  induction calculation with
  | generated calculation =>
      exact calculation.eval_eq
  | simplePower simple exponent context =>
      simpa only [LinearDiagram.eval_atom, map_smul] using
        eval_plug_automorphismCouponPower
          data automorphism simple exponent context
  | add _ _ leftSound rightSound =>
      simpa only [map_add] using
        congrArg₂ (· + ·) leftSound rightSound
  | smul scalar _ sound =>
      simpa only [map_smul] using
        congrArg (fun value => scalar • value) sound
  | symm _ sound =>
      exact sound.symm
  | trans _ _ firstSound secondSound =>
      exact firstSound.trans secondSound

end FusionLinearGeneratedCalculation

end FusionLinear

end TwistedYetter.Kirby.TensorAutomorphismCouponCalculus
