import TwistedYetter.Kirby.ModularDottedEncircling

/-!
# Closed proof grammar for a modular dotted-boundary movie

The final local calculation language contains no arbitrary equality
constructor.  Its atoms are:

* the checked tensor-automorphism coupon calculus;
* the algebraic unit-projector vacuum calculation; and
* the source-backed open Kirby-encircling killing identity.

Linearity, symmetry, and transitivity then assemble complete finite Kirby
colour sums.  The remaining presentation compiler must construct a term in
this grammar with the exact cycle-linear-diagram endpoints.
-/

namespace TwistedYetter.Kirby.ModularDottedBoundaryCalculation

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ModularDottedEncircling
open TwistedYetter.Kirby.ModularVacuumProjector

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Restricted calculations whose endpoints are complete closed linear sums. -/
inductive DottedBoundaryLinearCalculation
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C) :
    LinearDiagram (R := K) (C := C) .unit .unit →
      LinearDiagram (R := K) (C := C) .unit .unit →
        Type (max uK (max uC vC))
  | vacuumGenerated
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit}
      (calculation :
        DottedVacuumLinearCalculation
          𝒞.premodular.toFusionCategoryData
          automorphism before after) :
      DottedBoundaryLinearCalculation 𝒞 automorphism before after
  | openEncircling
      (X : C)
      (exponent : ℤ)
      (context :
        Context C (.atom X) (.atom X) .unit .unit) :
      DottedBoundaryLinearCalculation 𝒞 automorphism
        (LinearDiagram.atom (R := K)
          (Context.plug C context
            (powerThenOpenKirbyEncirclingCoupon
              𝒞 automorphism X exponent)))
        (LinearDiagram.atom (R := K)
          (Context.plug C context
            (openKirbyEncirclingCoupon 𝒞 X)))
  | add
      {leftBefore leftAfter rightBefore rightAfter :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      DottedBoundaryLinearCalculation
          𝒞 automorphism leftBefore leftAfter →
      DottedBoundaryLinearCalculation
          𝒞 automorphism rightBefore rightAfter →
      DottedBoundaryLinearCalculation 𝒞 automorphism
        (leftBefore + rightBefore) (leftAfter + rightAfter)
  | smul
      (scalar : K)
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      DottedBoundaryLinearCalculation 𝒞 automorphism before after →
      DottedBoundaryLinearCalculation 𝒞 automorphism
        (scalar • before) (scalar • after)
  | symm
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      DottedBoundaryLinearCalculation 𝒞 automorphism before after →
      DottedBoundaryLinearCalculation 𝒞 automorphism after before
  | trans
      {first middle last :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      DottedBoundaryLinearCalculation 𝒞 automorphism first middle →
      DottedBoundaryLinearCalculation 𝒞 automorphism middle last →
      DottedBoundaryLinearCalculation 𝒞 automorphism first last

namespace DottedBoundaryLinearCalculation

/-- Every term in the restricted grammar preserves categorical evaluation. -/
theorem eval_eq
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {before after :
      LinearDiagram (R := K) (C := C) .unit .unit}
    (calculation :
      DottedBoundaryLinearCalculation 𝒞 automorphism before after) :
    LinearDiagram.eval before = LinearDiagram.eval after := by
  induction calculation with
  | vacuumGenerated calculation =>
      exact calculation.eval_eq
  | openEncircling X exponent context =>
      simpa only [LinearDiagram.eval_atom] using
        powerThenOpenKirbyEncircling_eval_eq_inContext
          𝒞 automorphism X exponent context
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

end DottedBoundaryLinearCalculation

/-- Machine-visible status of the closed local proof language. -/
def currentStatus : String :=
  "PASS_CLOSED_DOTTED_BOUNDARY_CALCULATION_GRAMMAR_SOUND"

end TwistedYetter.Kirby.ModularDottedBoundaryCalculation
