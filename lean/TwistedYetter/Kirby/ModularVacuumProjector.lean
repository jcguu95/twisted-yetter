import TwistedYetter.Kirby.ThamThreeHandleVacuum
import TwistedYetter.Kirby.TensorAutomorphismCouponCalculus

/-!
# The modular vacuum projector on an arbitrary fusion object

For a fusion object `X`, the Tham `k = 3` vacuum operation retains the
tensor-unit isotypic summand.  This file defines that summand projector from
the stored finite biproduct decomposition and proves the algebraic fact needed
by homological twisting: every integral power of a monoidal natural
automorphism of the identity is invisible on either side of the projector.

Unlike the closed Hopf-pair specialization, `X` is arbitrary.  It may
therefore stand for a parenthesized tensor product of all strands puncturing
a dotted-handle disk.  The result below is the category-theoretic core of the
general dual `d3` boundary movie.

This module does not identify a raw serialized dotted neighborhood with this
projector.  That separate topology-to-diagram compiler obligation remains
visible downstream.
-/

namespace TwistedYetter.Kirby.ModularVacuumProjector

open scoped BigOperators
open CategoryTheory
open CategoryTheory.Limits
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ThamThreeHandleVacuum
open TwistedYetter.Kirby.TensorAutomorphismCouponCalculus

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Projection onto all copies of the tensor-unit simple inside `X`. -/
noncomputable def unitSummandProjector
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (X : C) : X ⟶ X :=
  ∑ i : Fin (data.multiplicity X data.unitIndex),
    data.projection X ⟨data.unitIndex, i⟩ ≫
      data.inclusion X ⟨data.unitIndex, i⟩

/-- The forward component of a tensor automorphism is identity on the unit. -/
theorem automorphism_hom_unit_simple
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C) :
    automorphism.iso.hom.app (data.simple data.unitIndex) =
      𝟙 (data.simple data.unitIndex) := by
  rw [data.automorphism_app_eq_smul_identity automorphism]
  rw [automorphismSimpleScalar_unitIndex data automorphism]
  simp

/-- The inverse component is likewise identity on the unit. -/
theorem automorphism_inv_unit_simple
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C) :
    automorphism.iso.inv.app (data.simple data.unitIndex) =
      𝟙 (data.simple data.unitIndex) := by
  rw [← cancel_epi (automorphism.iso.hom.app (data.simple data.unitIndex))]
  rw [automorphism.iso.hom_inv_id_app]
  simp [automorphism_hom_unit_simple data automorphism]

/-- A forward coupon immediately before the vacuum projector disappears. -/
theorem automorphism_hom_projector_left
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C) :
    automorphism.iso.hom.app X ≫ unitSummandProjector data X =
      unitSummandProjector data X := by
  classical
  unfold unitSummandProjector
  calc
    automorphism.iso.hom.app X ≫
        (∑ i : Fin (data.multiplicity X data.unitIndex),
          data.projection X ⟨data.unitIndex, i⟩ ≫
            data.inclusion X ⟨data.unitIndex, i⟩) =
        ∑ i : Fin (data.multiplicity X data.unitIndex),
        automorphism.iso.hom.app X ≫
          (data.projection X ⟨data.unitIndex, i⟩ ≫
            data.inclusion X ⟨data.unitIndex, i⟩) := by
      simpa using
        Preadditive.comp_sum (Finset.univ)
          (automorphism.iso.hom.app X)
          (fun i : Fin (data.multiplicity X data.unitIndex) =>
            data.projection X ⟨data.unitIndex, i⟩ ≫
              data.inclusion X ⟨data.unitIndex, i⟩)
    _ = ∑ i : Fin (data.multiplicity X data.unitIndex),
          data.projection X ⟨data.unitIndex, i⟩ ≫
            data.inclusion X ⟨data.unitIndex, i⟩ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Category.assoc]
      rw [CouponLaws.hom_naturality automorphism
        (data.projection X ⟨data.unitIndex, i⟩)]
      rw [automorphism_hom_unit_simple data automorphism]
      simp

/-- An inverse coupon immediately before the vacuum projector disappears. -/
theorem automorphism_inv_projector_left
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C) :
    automorphism.iso.inv.app X ≫ unitSummandProjector data X =
      unitSummandProjector data X := by
  classical
  unfold unitSummandProjector
  calc
    automorphism.iso.inv.app X ≫
        (∑ i : Fin (data.multiplicity X data.unitIndex),
          data.projection X ⟨data.unitIndex, i⟩ ≫
            data.inclusion X ⟨data.unitIndex, i⟩) =
        ∑ i : Fin (data.multiplicity X data.unitIndex),
        automorphism.iso.inv.app X ≫
          (data.projection X ⟨data.unitIndex, i⟩ ≫
            data.inclusion X ⟨data.unitIndex, i⟩) := by
      simpa using
        Preadditive.comp_sum (Finset.univ)
          (automorphism.iso.inv.app X)
          (fun i : Fin (data.multiplicity X data.unitIndex) =>
            data.projection X ⟨data.unitIndex, i⟩ ≫
              data.inclusion X ⟨data.unitIndex, i⟩)
    _ = ∑ i : Fin (data.multiplicity X data.unitIndex),
          data.projection X ⟨data.unitIndex, i⟩ ≫
            data.inclusion X ⟨data.unitIndex, i⟩ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Category.assoc]
      rw [CouponLaws.inv_naturality automorphism
        (data.projection X ⟨data.unitIndex, i⟩)]
      rw [automorphism_inv_unit_simple data automorphism]
      simp

/-- A forward coupon immediately after the vacuum projector disappears. -/
theorem automorphism_hom_projector_right
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C) :
    unitSummandProjector data X ≫ automorphism.iso.hom.app X =
      unitSummandProjector data X := by
  classical
  unfold unitSummandProjector
  calc
    (∑ i : Fin (data.multiplicity X data.unitIndex),
        data.projection X ⟨data.unitIndex, i⟩ ≫
          data.inclusion X ⟨data.unitIndex, i⟩) ≫
        automorphism.iso.hom.app X =
      ∑ i : Fin (data.multiplicity X data.unitIndex),
        (data.projection X ⟨data.unitIndex, i⟩ ≫
          data.inclusion X ⟨data.unitIndex, i⟩) ≫
            automorphism.iso.hom.app X := by
      simpa using
        Preadditive.sum_comp (Finset.univ)
          (fun i : Fin (data.multiplicity X data.unitIndex) =>
            data.projection X ⟨data.unitIndex, i⟩ ≫
              data.inclusion X ⟨data.unitIndex, i⟩)
          (automorphism.iso.hom.app X)
    _ = ∑ i : Fin (data.multiplicity X data.unitIndex),
          data.projection X ⟨data.unitIndex, i⟩ ≫
            data.inclusion X ⟨data.unitIndex, i⟩ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Category.assoc]
      rw [← CouponLaws.hom_naturality automorphism
        (data.inclusion X ⟨data.unitIndex, i⟩)]
      rw [automorphism_hom_unit_simple data automorphism]
      simp

/-- An inverse coupon immediately after the vacuum projector disappears. -/
theorem automorphism_inv_projector_right
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C) :
    unitSummandProjector data X ≫ automorphism.iso.inv.app X =
      unitSummandProjector data X := by
  classical
  unfold unitSummandProjector
  calc
    (∑ i : Fin (data.multiplicity X data.unitIndex),
        data.projection X ⟨data.unitIndex, i⟩ ≫
          data.inclusion X ⟨data.unitIndex, i⟩) ≫
        automorphism.iso.inv.app X =
      ∑ i : Fin (data.multiplicity X data.unitIndex),
        (data.projection X ⟨data.unitIndex, i⟩ ≫
          data.inclusion X ⟨data.unitIndex, i⟩) ≫
            automorphism.iso.inv.app X := by
      simpa using
        Preadditive.sum_comp (Finset.univ)
          (fun i : Fin (data.multiplicity X data.unitIndex) =>
            data.projection X ⟨data.unitIndex, i⟩ ≫
              data.inclusion X ⟨data.unitIndex, i⟩)
          (automorphism.iso.inv.app X)
    _ = ∑ i : Fin (data.multiplicity X data.unitIndex),
          data.projection X ⟨data.unitIndex, i⟩ ≫
            data.inclusion X ⟨data.unitIndex, i⟩ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Category.assoc]
      rw [← CouponLaws.inv_naturality automorphism
        (data.inclusion X ⟨data.unitIndex, i⟩)]
      rw [automorphism_inv_unit_simple data automorphism]
      simp

/-- The component of an integral power of the tensor automorphism on `X`. -/
noncomputable def automorphismObjectPower
    (automorphism : TensorIdentityAutomorphism C)
    (X : C)
    (exponent : ℤ) : X ⟶ X :=
  let component : Aut X := automorphism.iso.app X
  (component ^ exponent).hom

/-- Every integral coupon power disappears before the vacuum projector. -/
theorem automorphism_power_projector_left
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C)
    (exponent : ℤ) :
    automorphismObjectPower automorphism X exponent ≫
        unitSummandProjector data X =
      unitSummandProjector data X := by
  let component : Aut X := automorphism.iso.app X
  change (component ^ exponent).hom ≫ unitSummandProjector data X = _
  induction exponent using Int.induction_on with
  | zero =>
      change 𝟙 X ≫ unitSummandProjector data X = _
      simp
  | @succ n ih =>
      have hzpow :
          component ^ ((n : ℤ) + 1) = component ^ (n : ℤ) * component := by
        rw [zpow_add, zpow_one]
      rw [hzpow, CategoryTheory.Aut.Aut_mul_def, Iso.trans_hom]
      change
        (automorphism.iso.hom.app X ≫ (component ^ (n : ℤ)).hom) ≫
          unitSummandProjector data X = _
      calc
        _ = automorphism.iso.hom.app X ≫
            ((component ^ (n : ℤ)).hom ≫ unitSummandProjector data X) :=
              Category.assoc _ _ _
        _ = automorphism.iso.hom.app X ≫ unitSummandProjector data X := by
              exact congrArg
                (fun morphism : X ⟶ X => automorphism.iso.hom.app X ≫ morphism)
                ih
        _ = unitSummandProjector data X :=
              automorphism_hom_projector_left data automorphism X
  | @pred n ih =>
      have hzpow :
          component ^ (-(n : ℤ) - 1) =
            component ^ (-(n : ℤ)) * component ^ (-1 : ℤ) := by
        exact zpow_add component (-(n : ℤ)) (-1)
      rw [hzpow, zpow_neg_one, CategoryTheory.Aut.Aut_mul_def, Iso.trans_hom]
      change
        (automorphism.iso.inv.app X ≫ (component ^ (-(n : ℤ))).hom) ≫
          unitSummandProjector data X = _
      calc
        _ = automorphism.iso.inv.app X ≫
            ((component ^ (-(n : ℤ))).hom ≫ unitSummandProjector data X) :=
              Category.assoc _ _ _
        _ = automorphism.iso.inv.app X ≫ unitSummandProjector data X := by
              exact congrArg
                (fun morphism : X ⟶ X => automorphism.iso.inv.app X ≫ morphism)
                ih
        _ = unitSummandProjector data X :=
              automorphism_inv_projector_left data automorphism X

/-- Every integral coupon power disappears after the vacuum projector. -/
theorem automorphism_power_projector_right
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C)
    (exponent : ℤ) :
    unitSummandProjector data X ≫
        automorphismObjectPower automorphism X exponent =
      unitSummandProjector data X := by
  let component : Aut X := automorphism.iso.app X
  change unitSummandProjector data X ≫ (component ^ exponent).hom = _
  induction exponent using Int.induction_on with
  | zero =>
      change unitSummandProjector data X ≫ 𝟙 X = _
      simp
  | @succ n ih =>
      have hzpow :
          component ^ ((n : ℤ) + 1) = component ^ (n : ℤ) * component := by
        rw [zpow_add, zpow_one]
      rw [hzpow, CategoryTheory.Aut.Aut_mul_def, Iso.trans_hom]
      change
        unitSummandProjector data X ≫
          (automorphism.iso.hom.app X ≫ (component ^ (n : ℤ)).hom) = _
      calc
        _ = (unitSummandProjector data X ≫ automorphism.iso.hom.app X) ≫
            (component ^ (n : ℤ)).hom := (Category.assoc _ _ _).symm
        _ = unitSummandProjector data X ≫ (component ^ (n : ℤ)).hom := by
              exact congrArg
                (fun morphism : X ⟶ X => morphism ≫ (component ^ (n : ℤ)).hom)
                (automorphism_hom_projector_right data automorphism X)
        _ = unitSummandProjector data X := ih
  | @pred n ih =>
      have hzpow :
          component ^ (-(n : ℤ) - 1) =
            component ^ (-(n : ℤ)) * component ^ (-1 : ℤ) := by
        exact zpow_add component (-(n : ℤ)) (-1)
      rw [hzpow, zpow_neg_one, CategoryTheory.Aut.Aut_mul_def, Iso.trans_hom]
      change
        unitSummandProjector data X ≫
          (automorphism.iso.inv.app X ≫
            (component ^ (-(n : ℤ))).hom) = _
      calc
        _ = (unitSummandProjector data X ≫ automorphism.iso.inv.app X) ≫
            (component ^ (-(n : ℤ))).hom := (Category.assoc _ _ _).symm
        _ = unitSummandProjector data X ≫
            (component ^ (-(n : ℤ))).hom := by
              exact congrArg
                (fun morphism : X ⟶ X =>
                  morphism ≫ (component ^ (-(n : ℤ))).hom)
                (automorphism_inv_projector_right data automorphism X)
        _ = unitSummandProjector data X := ih

/-- The typed local picture with the integral coupon before the vacuum cut. -/
noncomputable def powerThenVacuumDiagram
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C)
    (exponent : ℤ) :
    Diagram C (.atom X) (.atom X) :=
  atomicCoupon "tensor-automorphism-power-then-vacuum"
    (automorphismObjectPower automorphism X exponent ≫
      unitSummandProjector data X)

/-- The same local picture after the coupon has disappeared. -/
noncomputable def vacuumDiagram
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (X : C) :
    Diagram C (.atom X) (.atom X) :=
  atomicCoupon "unit-summand-vacuum-projector"
    (unitSummandProjector data X)

/-- The actual typed local diagrams have equal categorical evaluations. -/
theorem powerThenVacuumDiagram_eval_eq
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C)
    (exponent : ℤ) :
    Diagram.eval C
        (powerThenVacuumDiagram data automorphism X exponent) =
      Diagram.eval C (vacuumDiagram data X) := by
  simpa only [powerThenVacuumDiagram, vacuumDiagram, atomicCoupon,
    Diagram.eval] using
    automorphism_power_projector_left data automorphism X exponent

/--
The coupon remains invisible after inserting the vacuum cut in an arbitrary
larger tangle.  This is the exact category-side theorem required by the
dotted-neighbourhood compiler.
-/
theorem powerThenVacuumDiagram_eval_eq_inContext
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C)
    (exponent : ℤ)
    (context :
      Context C (.atom X) (.atom X) .unit .unit) :
    Diagram.eval C
        (Context.plug C context
          (powerThenVacuumDiagram data automorphism X exponent)) =
      Diagram.eval C
        (Context.plug C context (vacuumDiagram data X)) :=
  Context.eval_plug_congr C context
    (powerThenVacuumDiagram_eval_eq data automorphism X exponent)

/--
Closed proof grammar for a complete linear dotted-vacuum calculation.

There is no constructor from an arbitrary diagram equality.  A compiler may
use only the already checked coupon calculus, the context-closed vacuum move,
linearity, symmetry, and transitivity.
-/
inductive DottedVacuumLinearCalculation
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C) :
    LinearDiagram (R := K) (C := C) .unit .unit →
      LinearDiagram (R := K) (C := C) .unit .unit →
        Type (max uK (max uC vC))
  | generated
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit}
      (calculation :
        FusionLinearGeneratedCalculation data automorphism before after) :
      DottedVacuumLinearCalculation data automorphism before after
  | vacuum
      (X : C)
      (exponent : ℤ)
      (context :
        Context C (.atom X) (.atom X) .unit .unit) :
      DottedVacuumLinearCalculation data automorphism
        (LinearDiagram.atom (R := K)
          (Context.plug C context
            (powerThenVacuumDiagram data automorphism X exponent)))
        (LinearDiagram.atom (R := K)
          (Context.plug C context (vacuumDiagram data X)))
  | add
      {leftBefore leftAfter rightBefore rightAfter :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      DottedVacuumLinearCalculation
          data automorphism leftBefore leftAfter →
      DottedVacuumLinearCalculation
          data automorphism rightBefore rightAfter →
      DottedVacuumLinearCalculation data automorphism
        (leftBefore + rightBefore) (leftAfter + rightAfter)
  | smul
      (scalar : K)
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      DottedVacuumLinearCalculation data automorphism before after →
      DottedVacuumLinearCalculation data automorphism
        (scalar • before) (scalar • after)
  | symm
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      DottedVacuumLinearCalculation data automorphism before after →
      DottedVacuumLinearCalculation data automorphism after before
  | trans
      {first middle last :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      DottedVacuumLinearCalculation data automorphism first middle →
      DottedVacuumLinearCalculation data automorphism middle last →
      DottedVacuumLinearCalculation data automorphism first last

namespace DottedVacuumLinearCalculation

/-- Every calculation generated by the closed grammar preserves evaluation. -/
theorem eval_eq
    {data : FusionCategoryData (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {before after :
      LinearDiagram (R := K) (C := C) .unit .unit}
    (calculation :
      DottedVacuumLinearCalculation data automorphism before after) :
    LinearDiagram.eval before = LinearDiagram.eval after := by
  induction calculation with
  | generated calculation =>
      exact calculation.eval_eq
  | vacuum X exponent context =>
      simpa only [LinearDiagram.eval_atom] using
        powerThenVacuumDiagram_eval_eq_inContext
          data automorphism X exponent context
  | add _ _ leftSound rightSound =>
      simpa only [map_add] using
        congrArg₂ (fun left right => left + right) leftSound rightSound
  | smul scalar _ sound =>
      simpa only [map_smul] using
        congrArg (fun value => scalar • value) sound
  | symm _ sound =>
      exact sound.symm
  | trans _ _ firstSound secondSound =>
      exact firstSound.trans secondSound

end DottedVacuumLinearCalculation

/-- Machine-visible result without a claim about raw diagram compilation. -/
def currentStatus : String :=
  "PASS_CONTEXT_CLOSED_ARBITRARY_OBJECT_INTEGER_COUPON_VACUUM_NEUTRALITY"

/-- The remaining interface is geometric, not another category axiom. -/
def remainingScope : String :=
  "Compile each certified dual d3 generator to a dotted-handle disk window "
    ++ "whose encircling operator is the unit-summand projector."

end TwistedYetter.Kirby.ModularVacuumProjector
