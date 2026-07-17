import Mathlib.CategoryTheory.Monoidal.Linear
import TwistedYetter.Fusion.Insertion
import TwistedYetter.Kirby.CategoricalTangle

/-!
# Linearity of one-hole diagram contexts

Plugging a coupon into a typed one-hole context is linear in that coupon.
Consequently a categorical identity resolution can be inserted into any
surrounding tangle without postulating a new whole-diagram equality.
-/

namespace TwistedYetter.Kirby.LinearContext

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.Insertion
open TwistedYetter.Kirby.CategoricalTangle

universe uR u v uS uI

variable {R : Type uR} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear R C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear R C]

/-- The evaluator of a one-hole context as a linear map on its hole. -/
noncomputable def evalContextLinearMap
    {holeSource holeTarget wholeSource wholeTarget : Boundary C}
    (context :
      Context C holeSource holeTarget wholeSource wholeTarget) :
    (holeSource.denote ⟶ holeTarget.denote) →ₗ[R]
      (wholeSource.denote ⟶ wholeTarget.denote) :=
  match context with
  | .hole _ _ => LinearMap.id
  | .compLeft before =>
      { toFun := fun morphism => Diagram.eval C before ≫ morphism
        map_add' := by simp
        map_smul' := by simp }
  | .compRight after =>
      { toFun := fun morphism => morphism ≫ Diagram.eval C after
        map_add' := by simp
        map_smul' := by simp }
  | .tensorLeft rightPiece =>
      { toFun := fun morphism => morphism ⊗ₘ (Diagram.eval C rightPiece)
        map_add' := by
          intro left right
          simp [tensorHom_def]
          rfl
        map_smul' := by
          intro scalar morphism
          simp [tensorHom_def]
          rfl }
  | .tensorRight leftPiece =>
      { toFun := fun morphism => (Diagram.eval C leftPiece) ⊗ₘ morphism
        map_add' := by
          intro left right
          simp [tensorHom_def]
          rfl
        map_smul' := by
          intro scalar morphism
          simp [tensorHom_def]
          rfl }
  | .compose inner outer =>
      (evalContextLinearMap outer).comp (evalContextLinearMap inner)

/-- The context linear map agrees with plugging a coupon carrying the input. -/
theorem evalContextLinearMap_apply
    {holeSource holeTarget wholeSource wholeTarget : Boundary C}
    (context :
      Context C holeSource holeTarget wholeSource wholeTarget)
    (name : String)
    (morphism : holeSource.denote ⟶ holeTarget.denote) :
    evalContextLinearMap (R := R) context morphism =
      Diagram.eval C
        (Context.plug C context (Diagram.coupon name morphism)) := by
  induction context with
  | hole =>
      simp [evalContextLinearMap, Context.plug, Diagram.eval]
  | compLeft before =>
      simp [evalContextLinearMap, Context.plug, Diagram.eval]
  | compRight after =>
      simp [evalContextLinearMap, Context.plug, Diagram.eval]
  | tensorLeft rightPiece =>
      simp [evalContextLinearMap, Context.plug, Diagram.eval]
  | tensorRight leftPiece =>
      simp [evalContextLinearMap, Context.plug, Diagram.eval]
  | compose inner outer innerIH outerIH =>
      simp only [evalContextLinearMap, LinearMap.comp_apply, Context.plug]
      rw [innerIH, outerIH]
      exact Context.eval_plug_congr C outer rfl

/- Compatibility alias retaining the coupon-oriented API name. -/
noncomputable def evalCouponLinearMap
    {holeSource holeTarget wholeSource wholeTarget : Boundary C}
    (context :
      Context C holeSource holeTarget wholeSource wholeTarget)
    (_name : String) :
    (holeSource.denote ⟶ holeTarget.denote) →ₗ[R]
      (wholeSource.denote ⟶ wholeTarget.denote) :=
  evalContextLinearMap (R := R) context

@[simp]
theorem evalCouponLinearMap_apply
    {holeSource holeTarget wholeSource wholeTarget : Boundary C}
    (context :
      Context C holeSource holeTarget wholeSource wholeTarget)
    (name : String)
    (morphism : holeSource.denote ⟶ holeTarget.denote) :
    evalCouponLinearMap (R := R) context name morphism =
      Diagram.eval C
        (Context.plug C context (Diagram.coupon name morphism)) :=
  evalContextLinearMap_apply context name morphism

/--
Insert a source-backed identity resolution into an arbitrary typed context.
This is the context-level form of Bärenz--Barrett Lemma 3.2.
-/
theorem insertIdentity
    {T : C}
    {S : Type uS} [Fintype S]
    {I : S → Type uI} [∀ s, Fintype (I s)]
    (resolution : IdentityResolution (R := R) (S := S) (I := I) T)
    {wholeSource wholeTarget : Boundary C}
    (context :
      Context C (.atom T) (.atom T) wholeSource wholeTarget)
    (name : String) :
    ∑ s, ∑ i : I s,
      resolution.weight s •
        Diagram.eval C
          (Context.plug C context
            (Diagram.coupon name
              (resolution.projection s i ≫ resolution.inclusion s i))) =
      Diagram.eval C
        (Context.plug C context (Diagram.identity (.atom T))) := by
  let linearMap := evalCouponLinearMap (R := R) context name
  calc
    ∑ s, ∑ i : I s,
        resolution.weight s •
          Diagram.eval C
            (Context.plug C context
              (Diagram.coupon name
                (resolution.projection s i ≫ resolution.inclusion s i))) =
      linearMap
        (∑ s, ∑ i : I s,
          resolution.weight s •
            (resolution.projection s i ≫ resolution.inclusion s i)) := by
      symm
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      change linearMap
          (resolution.weight s •
            (resolution.projection s i ≫ resolution.inclusion s i)) =
        resolution.weight s •
          Diagram.eval C
            (Context.plug C context
              (Diagram.coupon name
                (resolution.projection s i ≫ resolution.inclusion s i)))
      calc
        linearMap
            (resolution.weight s •
              (resolution.projection s i ≫ resolution.inclusion s i)) =
          resolution.weight s •
            linearMap
              (resolution.projection s i ≫ resolution.inclusion s i) :=
          linearMap.map_smul _ _
        _ = resolution.weight s •
            Diagram.eval C
              (Context.plug C context
                (Diagram.coupon name
                  (resolution.projection s i ≫ resolution.inclusion s i))) :=
          congrArg (fun value => resolution.weight s • value)
            (evalCouponLinearMap_apply context name
              (resolution.projection s i ≫ resolution.inclusion s i))
    _ = linearMap (𝟙 T) :=
      congrArg linearMap resolution.sound
    _ = Diagram.eval C
        (Context.plug C context (Diagram.coupon name (𝟙 T))) := by
      exact evalCouponLinearMap_apply context name (𝟙 T)
    _ = Diagram.eval C
        (Context.plug C context (Diagram.identity (.atom T))) :=
      Context.eval_plug_congr C context rfl

end TwistedYetter.Kirby.LinearContext
