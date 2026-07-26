import TwistedYetter.Kirby.PremodularUnitCutSlides
import TwistedYetter.Kirby.RoleAwareComponentDiagram

/-!
# Free role-aware diagrams for dotted Kirby slides

This file binds the local categorical calculations to explicit free syntax.
The character coupon, normalized tensor-unit cut, crossing orientation, and
unchanged exterior context are all visible in the theorem statements.
-/

namespace TwistedYetter.Kirby.RoleAwareUnitCutSlideDiagrams

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.PremodularUnitCutSlides
open TwistedYetter.Kirby.PremodularDottedCutting
open TwistedYetter.Kirby.RoleAwareComponentDiagram

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

private def strand (componentId : String) : ComponentBoundary :=
  .atom (positiveAtom componentId)

/-- Pure topology-side positive 2/1 window, before inserting a character coupon. -/
def twoOverOnePositiveTopologyBefore
    (dottedId : String)
    (punctureBoundary movingBoundary : ComponentBoundary) :
    RoleAwareDiagram
      (.tensor punctureBoundary movingBoundary)
      (.tensor movingBoundary punctureBoundary) :=
  .comp
    (.tensor
      (.specialDottedCut dottedId punctureBoundary)
      (.ordinary (.identity movingBoundary)))
    (.ordinary (.crossingPositive punctureBoundary movingBoundary))

/-- Pure topology-side negative 2/1 window, before inserting a character coupon. -/
def twoOverOneNegativeTopologyBefore
    (dottedId : String)
    (punctureBoundary movingBoundary : ComponentBoundary) :
    RoleAwareDiagram
      (.tensor movingBoundary punctureBoundary)
      (.tensor punctureBoundary movingBoundary) :=
  .comp
    (.tensor
      (.ordinary (.identity movingBoundary))
      (.specialDottedCut dottedId punctureBoundary))
    (.ordinary (.crossingNegative movingBoundary punctureBoundary))

/-- Pure topology-side 1/1 window; both cuts remain explicit. -/
def oneOverOneTopologyBefore
    (leftDottedId rightDottedId : String)
    (leftBoundary rightBoundary : ComponentBoundary) :
    RoleAwareDiagram
      (.tensor leftBoundary rightBoundary)
      (.tensor leftBoundary rightBoundary) :=
  .comp
    (.tensor
      (.specialDottedCut leftDottedId leftBoundary)
      (.ordinary (.identity rightBoundary)))
    (.tensor
      (.ordinary (.identity leftBoundary))
      (.specialDottedCut rightDottedId rightBoundary))

/-- Pure topology-side 1/1 endpoint with the two local cut operations reversed. -/
def oneOverOneTopologyAfter
    (leftDottedId rightDottedId : String)
    (leftBoundary rightBoundary : ComponentBoundary) :
    RoleAwareDiagram
      (.tensor leftBoundary rightBoundary)
      (.tensor leftBoundary rightBoundary) :=
  .comp
    (.tensor
      (.ordinary (.identity leftBoundary))
      (.specialDottedCut rightDottedId rightBoundary))
    (.tensor
      (.specialDottedCut leftDottedId leftBoundary)
      (.ordinary (.identity rightBoundary)))

/-- Positive 2/1 window for an arbitrary (possibly long) puncture word. -/
def twoOverOnePositiveBeforeBoundary
    (dottedId : String)
    (punctureBoundary movingBoundary : ComponentBoundary)
    (exponent : ℤ) :
    RoleAwareDiagram
      (.tensor punctureBoundary movingBoundary)
      (.tensor movingBoundary punctureBoundary) :=
  .comp
    (.tensor
      (.comp
        (.characterPower punctureBoundary exponent)
        (.specialDottedCut dottedId punctureBoundary))
      (.ordinary (.identity movingBoundary)))
    (.ordinary (.crossingPositive punctureBoundary movingBoundary))

/-- Positive 2/1 endpoint after crossing an arbitrary puncture word. -/
def twoOverOnePositiveAfterBoundary
    (dottedId : String)
    (punctureBoundary movingBoundary : ComponentBoundary) :
    RoleAwareDiagram
      (.tensor punctureBoundary movingBoundary)
      (.tensor movingBoundary punctureBoundary) :=
  .comp
    (.ordinary (.crossingPositive punctureBoundary movingBoundary))
    (.tensor
      (.ordinary (.identity movingBoundary))
      (.specialDottedCut dottedId punctureBoundary))

/-- Negative 2/1 window for an arbitrary puncture word. -/
def twoOverOneNegativeBeforeBoundary
    (dottedId : String)
    (punctureBoundary movingBoundary : ComponentBoundary)
    (exponent : ℤ) :
    RoleAwareDiagram
      (.tensor movingBoundary punctureBoundary)
      (.tensor punctureBoundary movingBoundary) :=
  .comp
    (.tensor
      (.ordinary (.identity movingBoundary))
      (.comp
        (.specialDottedCut dottedId punctureBoundary)
        (.characterPower punctureBoundary exponent)))
    (.ordinary (.crossingNegative movingBoundary punctureBoundary))

/-- Negative 2/1 endpoint after crossing an arbitrary puncture word. -/
def twoOverOneNegativeAfterBoundary
    (dottedId : String)
    (punctureBoundary movingBoundary : ComponentBoundary) :
    RoleAwareDiagram
      (.tensor movingBoundary punctureBoundary)
      (.tensor punctureBoundary movingBoundary) :=
  .comp
    (.ordinary (.crossingNegative movingBoundary punctureBoundary))
    (.tensor
      (.specialDottedCut dottedId punctureBoundary)
      (.ordinary (.identity movingBoundary)))

/-- One-over-one window for two arbitrary simultaneous dotted cuts. -/
def oneOverOneBeforeBoundary
    (leftDottedId rightDottedId : String)
    (leftBoundary rightBoundary : ComponentBoundary)
    (leftExponent rightExponent : ℤ) :
    RoleAwareDiagram
      (.tensor leftBoundary rightBoundary)
      (.tensor leftBoundary rightBoundary) :=
  .comp
    (.tensor
      (.comp
        (.characterPower leftBoundary leftExponent)
        (.specialDottedCut leftDottedId leftBoundary))
      (.ordinary (.identity rightBoundary)))
    (.tensor
      (.ordinary (.identity leftBoundary))
      (.comp
        (.characterPower rightBoundary rightExponent)
        (.specialDottedCut rightDottedId rightBoundary)))

/-- The same arbitrary simultaneous cuts in the opposite local order. -/
def oneOverOneAfterBoundary
    (leftDottedId rightDottedId : String)
    (leftBoundary rightBoundary : ComponentBoundary)
    (leftExponent rightExponent : ℤ) :
    RoleAwareDiagram
      (.tensor leftBoundary rightBoundary)
      (.tensor leftBoundary rightBoundary) :=
  .comp
    (.tensor
      (.ordinary (.identity leftBoundary))
      (.comp
        (.characterPower rightBoundary rightExponent)
        (.specialDottedCut rightDottedId rightBoundary)))
    (.tensor
      (.comp
        (.characterPower leftBoundary leftExponent)
        (.specialDottedCut leftDottedId leftBoundary))
      (.ordinary (.identity rightBoundary)))

/-- Positive 2/1 window before the moving strand crosses the dotted cut. -/
def twoOverOnePositiveBefore
    (dottedId punctureId movingId : String)
    (exponent : ℤ) :
    RoleAwareDiagram
      (.tensor (strand punctureId) (strand movingId))
      (.tensor (strand movingId) (strand punctureId)) :=
  twoOverOnePositiveBeforeBoundary dottedId
    (strand punctureId) (strand movingId) exponent

/-- Positive 2/1 window after the moving strand crosses the dotted cut. -/
def twoOverOnePositiveAfter
    (dottedId punctureId movingId : String) :
    RoleAwareDiagram
      (.tensor (strand punctureId) (strand movingId))
      (.tensor (strand movingId) (strand punctureId)) :=
  twoOverOnePositiveAfterBoundary dottedId
    (strand punctureId) (strand movingId)

/-- Negative 2/1 window before the inverse crossing. -/
def twoOverOneNegativeBefore
    (dottedId punctureId movingId : String)
    (exponent : ℤ) :
    RoleAwareDiagram
      (.tensor (strand movingId) (strand punctureId))
      (.tensor (strand punctureId) (strand movingId)) :=
  twoOverOneNegativeBeforeBoundary dottedId
    (strand punctureId) (strand movingId) exponent

/-- Negative 2/1 window after the inverse crossing. -/
def twoOverOneNegativeAfter
    (dottedId punctureId movingId : String) :
    RoleAwareDiagram
      (.tensor (strand movingId) (strand punctureId))
      (.tensor (strand punctureId) (strand movingId)) :=
  twoOverOneNegativeAfterBoundary dottedId
    (strand punctureId) (strand movingId)

/-- One-over-one window with both character coupons visible. -/
def oneOverOneBefore
    (leftDottedId leftPunctureId rightDottedId rightPunctureId : String)
    (leftExponent rightExponent : ℤ) :
    RoleAwareDiagram
      (.tensor (strand leftPunctureId) (strand rightPunctureId))
      (.tensor (strand leftPunctureId) (strand rightPunctureId)) :=
  oneOverOneBeforeBoundary leftDottedId rightDottedId
    (strand leftPunctureId) (strand rightPunctureId)
    leftExponent rightExponent

/-- The same two disjoint dotted cuts in the opposite local order. -/
def oneOverOneAfter
    (leftDottedId leftPunctureId rightDottedId rightPunctureId : String)
    (leftExponent rightExponent : ℤ) :
    RoleAwareDiagram
      (.tensor (strand leftPunctureId) (strand rightPunctureId))
      (.tensor (strand leftPunctureId) (strand rightPunctureId)) :=
  oneOverOneAfterBoundary leftDottedId rightDottedId
    (strand leftPunctureId) (strand rightPunctureId)
    leftExponent rightExponent

/--
The pure topology-side 1/1 endpoints already evaluate equally.  Character
coupons are not required to state this interchange; their absorption is the
stronger theorem below.
-/
theorem oneOverOneTopologyBoundary_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (leftDottedId rightDottedId : String)
    (leftBoundary rightBoundary : ComponentBoundary) :
    Diagram.eval C
        ((oneOverOneTopologyBefore leftDottedId rightDottedId
          leftBoundary rightBoundary).interpret 𝒞 η labelOf) =
      Diagram.eval C
        ((oneOverOneTopologyAfter leftDottedId rightDottedId
          leftBoundary rightBoundary).interpret 𝒞 η labelOf) := by
  simp only [oneOverOneTopologyBefore, oneOverOneTopologyAfter,
    RoleAwareDiagram.interpret,
    ComponentDiagram.interpret, Diagram.eval,
    RoleAwareDiagram.interpretSpecialDottedCut,
    MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom]
  exact disjoint_specialDottedCuts_interchange 𝒞
    (leftBoundary.interpret 𝒞 labelOf).denote
    (rightBoundary.interpret 𝒞 labelOf).denote

theorem twoOverOnePositiveBoundary_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId : String)
    (punctureBoundary movingBoundary : ComponentBoundary)
    (exponent : ℤ) :
    Diagram.eval C
        ((twoOverOnePositiveBeforeBoundary dottedId
          punctureBoundary movingBoundary exponent).interpret 𝒞 η labelOf) =
      Diagram.eval C
        ((twoOverOnePositiveAfterBoundary dottedId
          punctureBoundary movingBoundary).interpret 𝒞 η labelOf) := by
  simp only [twoOverOnePositiveBeforeBoundary,
    twoOverOnePositiveAfterBoundary, RoleAwareDiagram.interpret,
    ComponentDiagram.interpret, Diagram.eval,
    RoleAwareDiagram.interpretSpecialDottedCut]
  simpa only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom] using
      twoOverOne_positive 𝒞 η
        (punctureBoundary.interpret 𝒞 labelOf).denote
        (movingBoundary.interpret 𝒞 labelOf).denote exponent

theorem twoOverOneNegativeBoundary_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId : String)
    (punctureBoundary movingBoundary : ComponentBoundary)
    (exponent : ℤ) :
    Diagram.eval C
        ((twoOverOneNegativeBeforeBoundary dottedId
          punctureBoundary movingBoundary exponent).interpret 𝒞 η labelOf) =
      Diagram.eval C
        ((twoOverOneNegativeAfterBoundary dottedId
          punctureBoundary movingBoundary).interpret 𝒞 η labelOf) := by
  simp only [twoOverOneNegativeBeforeBoundary,
    twoOverOneNegativeAfterBoundary, RoleAwareDiagram.interpret,
    ComponentDiagram.interpret, Diagram.eval,
    RoleAwareDiagram.interpretSpecialDottedCut]
  simpa only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom] using
      twoOverOne_negative 𝒞 η
        (punctureBoundary.interpret 𝒞 labelOf).denote
        (movingBoundary.interpret 𝒞 labelOf).denote exponent

theorem oneOverOneBoundary_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (leftDottedId rightDottedId : String)
    (leftBoundary rightBoundary : ComponentBoundary)
    (leftExponent rightExponent : ℤ) :
    Diagram.eval C
        ((oneOverOneBeforeBoundary leftDottedId rightDottedId
          leftBoundary rightBoundary leftExponent rightExponent).interpret
            𝒞 η labelOf) =
      Diagram.eval C
        ((oneOverOneAfterBoundary leftDottedId rightDottedId
          leftBoundary rightBoundary leftExponent rightExponent).interpret
            𝒞 η labelOf) := by
  simp only [oneOverOneBeforeBoundary, oneOverOneAfterBoundary,
    RoleAwareDiagram.interpret, ComponentDiagram.interpret, Diagram.eval,
    RoleAwareDiagram.interpretSpecialDottedCut]
  simpa only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom] using
      oneOverOne 𝒞 η
        (leftBoundary.interpret 𝒞 labelOf).denote
        (rightBoundary.interpret 𝒞 labelOf).denote
        leftExponent rightExponent

/-- Boundary-general positive 2/1 equality in an unchanged exterior. -/
theorem twoOverOnePositiveBoundary_eval_eq_inContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId : String)
    (punctureBoundary movingBoundary : ComponentBoundary)
    (exponent : ℤ)
    {wholeSource wholeTarget : ComponentBoundary}
    (context :
      RoleAwareDiagram.Context
        (.tensor punctureBoundary movingBoundary)
        (.tensor movingBoundary punctureBoundary)
        wholeSource wholeTarget) :
    Diagram.eval C
        ((context.plug
          (twoOverOnePositiveBeforeBoundary dottedId
            punctureBoundary movingBoundary exponent)).interpret
          𝒞 η labelOf) =
      Diagram.eval C
        ((context.plug
          (twoOverOnePositiveAfterBoundary dottedId
            punctureBoundary movingBoundary)).interpret
          𝒞 η labelOf) := by
  rw [context.interpret_plug, context.interpret_plug]
  exact CategoricalTangle.Context.eval_plug_congr C
    (context.interpret 𝒞 η labelOf)
    (twoOverOnePositiveBoundary_eval_eq 𝒞 η labelOf dottedId
      punctureBoundary movingBoundary exponent)

/-- Boundary-general negative 2/1 equality in an unchanged exterior. -/
theorem twoOverOneNegativeBoundary_eval_eq_inContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId : String)
    (punctureBoundary movingBoundary : ComponentBoundary)
    (exponent : ℤ)
    {wholeSource wholeTarget : ComponentBoundary}
    (context :
      RoleAwareDiagram.Context
        (.tensor movingBoundary punctureBoundary)
        (.tensor punctureBoundary movingBoundary)
        wholeSource wholeTarget) :
    Diagram.eval C
        ((context.plug
          (twoOverOneNegativeBeforeBoundary dottedId
            punctureBoundary movingBoundary exponent)).interpret
          𝒞 η labelOf) =
      Diagram.eval C
        ((context.plug
          (twoOverOneNegativeAfterBoundary dottedId
            punctureBoundary movingBoundary)).interpret
          𝒞 η labelOf) := by
  rw [context.interpret_plug, context.interpret_plug]
  exact CategoricalTangle.Context.eval_plug_congr C
    (context.interpret 𝒞 η labelOf)
    (twoOverOneNegativeBoundary_eval_eq 𝒞 η labelOf dottedId
      punctureBoundary movingBoundary exponent)

/-- Boundary-general 1/1 equality in an unchanged exterior. -/
theorem oneOverOneBoundary_eval_eq_inContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (leftDottedId rightDottedId : String)
    (leftBoundary rightBoundary : ComponentBoundary)
    (leftExponent rightExponent : ℤ)
    {wholeSource wholeTarget : ComponentBoundary}
    (context :
      RoleAwareDiagram.Context
        (.tensor leftBoundary rightBoundary)
        (.tensor leftBoundary rightBoundary)
        wholeSource wholeTarget) :
    Diagram.eval C
        ((context.plug
          (oneOverOneBeforeBoundary leftDottedId rightDottedId
            leftBoundary rightBoundary leftExponent rightExponent)).interpret
          𝒞 η labelOf) =
      Diagram.eval C
        ((context.plug
          (oneOverOneAfterBoundary leftDottedId rightDottedId
            leftBoundary rightBoundary leftExponent rightExponent)).interpret
          𝒞 η labelOf) := by
  rw [context.interpret_plug, context.interpret_plug]
  exact CategoricalTangle.Context.eval_plug_congr C
    (context.interpret 𝒞 η labelOf)
    (oneOverOneBoundary_eval_eq 𝒞 η labelOf
      leftDottedId rightDottedId leftBoundary rightBoundary
      leftExponent rightExponent)

/-- Pure topology-side 1/1 interchange in an arbitrary unchanged exterior. -/
theorem oneOverOneTopologyBoundary_eval_eq_inContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (leftDottedId rightDottedId : String)
    (leftBoundary rightBoundary : ComponentBoundary)
    {wholeSource wholeTarget : ComponentBoundary}
    (context :
      RoleAwareDiagram.Context
        (.tensor leftBoundary rightBoundary)
        (.tensor leftBoundary rightBoundary)
        wholeSource wholeTarget) :
    Diagram.eval C
        ((context.plug
          (oneOverOneTopologyBefore leftDottedId rightDottedId
            leftBoundary rightBoundary)).interpret 𝒞 η labelOf) =
      Diagram.eval C
        ((context.plug
          (oneOverOneTopologyAfter leftDottedId rightDottedId
            leftBoundary rightBoundary)).interpret 𝒞 η labelOf) := by
  rw [context.interpret_plug, context.interpret_plug]
  exact CategoricalTangle.Context.eval_plug_congr C
    (context.interpret 𝒞 η labelOf)
    (oneOverOneTopologyBoundary_eval_eq 𝒞 η labelOf
      leftDottedId rightDottedId leftBoundary rightBoundary)

theorem twoOverOnePositive_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId punctureId movingId : String)
    (exponent : ℤ) :
    Diagram.eval C
        ((twoOverOnePositiveBefore dottedId punctureId movingId exponent).interpret
          𝒞 η labelOf) =
      Diagram.eval C
        ((twoOverOnePositiveAfter dottedId punctureId movingId).interpret
          𝒞 η labelOf) := by
  exact twoOverOnePositiveBoundary_eval_eq 𝒞 η labelOf dottedId
    (strand punctureId) (strand movingId) exponent

theorem twoOverOneNegative_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId punctureId movingId : String)
    (exponent : ℤ) :
    Diagram.eval C
        ((twoOverOneNegativeBefore dottedId punctureId movingId exponent).interpret
          𝒞 η labelOf) =
      Diagram.eval C
        ((twoOverOneNegativeAfter dottedId punctureId movingId).interpret
          𝒞 η labelOf) := by
  exact twoOverOneNegativeBoundary_eval_eq 𝒞 η labelOf dottedId
    (strand punctureId) (strand movingId) exponent

theorem oneOverOne_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (leftDottedId leftPunctureId rightDottedId rightPunctureId : String)
    (leftExponent rightExponent : ℤ) :
    Diagram.eval C
        ((oneOverOneBefore
          leftDottedId leftPunctureId rightDottedId rightPunctureId
          leftExponent rightExponent).interpret 𝒞 η labelOf) =
      Diagram.eval C
        ((oneOverOneAfter
          leftDottedId leftPunctureId rightDottedId rightPunctureId
          leftExponent rightExponent).interpret 𝒞 η labelOf) := by
  exact oneOverOneBoundary_eval_eq 𝒞 η labelOf
    leftDottedId rightDottedId
    (strand leftPunctureId) (strand rightPunctureId)
    leftExponent rightExponent

/-- Any unchanged role-aware exterior preserves the positive 2/1 equality. -/
theorem twoOverOnePositive_eval_eq_inContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId punctureId movingId : String)
    (exponent : ℤ)
    {wholeSource wholeTarget : ComponentBoundary}
    (context :
      RoleAwareDiagram.Context
        (.tensor (strand punctureId) (strand movingId))
        (.tensor (strand movingId) (strand punctureId))
        wholeSource wholeTarget) :
    Diagram.eval C
        ((context.plug
          (twoOverOnePositiveBefore
            dottedId punctureId movingId exponent)).interpret
          𝒞 η labelOf) =
      Diagram.eval C
        ((context.plug
          (twoOverOnePositiveAfter
            dottedId punctureId movingId)).interpret
          𝒞 η labelOf) := by
  rw [context.interpret_plug, context.interpret_plug]
  exact CategoricalTangle.Context.eval_plug_congr C
    (context.interpret 𝒞 η labelOf)
    (twoOverOnePositive_eval_eq
      𝒞 η labelOf dottedId punctureId movingId exponent)

/-- Any unchanged role-aware exterior preserves the negative 2/1 equality. -/
theorem twoOverOneNegative_eval_eq_inContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId punctureId movingId : String)
    (exponent : ℤ)
    {wholeSource wholeTarget : ComponentBoundary}
    (context :
      RoleAwareDiagram.Context
        (.tensor (strand movingId) (strand punctureId))
        (.tensor (strand punctureId) (strand movingId))
        wholeSource wholeTarget) :
    Diagram.eval C
        ((context.plug
          (twoOverOneNegativeBefore
            dottedId punctureId movingId exponent)).interpret
          𝒞 η labelOf) =
      Diagram.eval C
        ((context.plug
          (twoOverOneNegativeAfter
            dottedId punctureId movingId)).interpret
          𝒞 η labelOf) := by
  rw [context.interpret_plug, context.interpret_plug]
  exact CategoricalTangle.Context.eval_plug_congr C
    (context.interpret 𝒞 η labelOf)
    (twoOverOneNegative_eval_eq
      𝒞 η labelOf dottedId punctureId movingId exponent)

/-- Any unchanged role-aware exterior preserves the 1/1 equality. -/
theorem oneOverOne_eval_eq_inContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (leftDottedId leftPunctureId rightDottedId rightPunctureId : String)
    (leftExponent rightExponent : ℤ)
    {wholeSource wholeTarget : ComponentBoundary}
    (context :
      RoleAwareDiagram.Context
        (.tensor (strand leftPunctureId) (strand rightPunctureId))
        (.tensor (strand leftPunctureId) (strand rightPunctureId))
        wholeSource wholeTarget) :
    Diagram.eval C
        ((context.plug
          (oneOverOneBefore
            leftDottedId leftPunctureId rightDottedId rightPunctureId
            leftExponent rightExponent)).interpret 𝒞 η labelOf) =
      Diagram.eval C
        ((context.plug
          (oneOverOneAfter
            leftDottedId leftPunctureId rightDottedId rightPunctureId
            leftExponent rightExponent)).interpret 𝒞 η labelOf) := by
  rw [context.interpret_plug, context.interpret_plug]
  exact CategoricalTangle.Context.eval_plug_congr C
    (context.interpret 𝒞 η labelOf)
    (oneOverOne_eval_eq 𝒞 η labelOf
      leftDottedId leftPunctureId rightDottedId rightPunctureId
      leftExponent rightExponent)

end TwistedYetter.Kirby.RoleAwareUnitCutSlideDiagrams
