import TwistedYetter.Kirby.ModularVacuumProjector
import TwistedYetter.Kirby.PresentationIsotopy

/-!
# The open modular dotted-encircling operator

This module states the standard modular killing identity at its useful open
tangle boundary.  The weighted Kirby-coloured meridian around an arbitrary
object is the global dimension times the projector onto all tensor-unit
summands.  Unlike the earlier closed Hopf-link scalar identity, this version
can be inserted into an arbitrary exterior tangle.

The open killing identity itself is an explicit literature axiom, sourced to
Bärenz--Barrett Lemmas 2.46--2.47 and Tham Definition 5.11 (`k = 3`).
Everything involving the homological tensor-automorphism coupon is proved
below from that identity and the monoidal naturality already formalized in
`ModularVacuumProjector`.
-/

namespace TwistedYetter.Kirby.ModularDottedEncircling

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.ModularVacuumProjector
open TwistedYetter.Kirby.PresentationIsotopy

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance selectedRigidRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/-- One simple-labelled meridian, left open on the encircled object `X`. -/
noncomputable def openEncirclingDiagram
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (simple : S)
    (X : C) : Diagram C (.atom X) (.atom X) :=
  let Y := data.simple simple
  leftUnitorInvDiagram X ≫ᵈ
    (Diagram.exactCup Y Yᘁ inferInstance ⊗ᵈ
      Diagram.identity (.atom X)) ≫ᵈ
    associatorHomDiagram Y Yᘁ X ≫ᵈ
    (Diagram.identity (.atom Y) ⊗ᵈ
      (Diagram.crossing (.atom Yᘁ) (.atom X) ≫ᵈ
        Diagram.crossing (.atom X) (.atom Yᘁ))) ≫ᵈ
    associatorInvDiagram Y Yᘁ X ≫ᵈ
    (Diagram.exactCap Yᘁ Y
        (pivotalReverseExactPairing data.pivotal Y) ⊗ᵈ
      Diagram.identity (.atom X)) ≫ᵈ
    leftUnitorHomDiagram X

/-- The finite dimension-weighted open meridian operator. -/
noncomputable def openKirbyEncirclingOperator
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (X : C) : X ⟶ X :=
  ∑ simple,
    data.quantumDimension simple •
      Diagram.eval C (openEncirclingDiagram data simple X)

/-- Stable source metadata for the one imported open graphical identity. -/
def openKillingSourceRef : String :=
  "ref:baerenz-barrett-dichromatic-2018;ref:tham-extended-crane-yetter-2021"

def openKillingSourceLocator : String :=
  "Barenz-Barrett Lemmas 2.46-2.47; Tham Definition 5.11, k=3, "
    ++ "PDF page 59 / printed page 53"

/--
The standard open modular killing identity: a Kirby-coloured meridian keeps
exactly the tensor-unit isotypic summand.
-/
axiom baerenzBarrett_tham_openKirbyKilling
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (X : C) :
    openKirbyEncirclingOperator 𝒞.premodular X =
      globalDimension 𝒞.premodular •
        unitSummandProjector
          𝒞.premodular.toFusionCategoryData X

/-- Every integral twisting coupon is invisible before the open meridian. -/
theorem automorphism_power_openKirbyEncircling_left
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C)
    (exponent : ℤ) :
    automorphismObjectPower automorphism X exponent ≫
        openKirbyEncirclingOperator 𝒞.premodular X =
      openKirbyEncirclingOperator 𝒞.premodular X := by
  rw [baerenzBarrett_tham_openKirbyKilling]
  rw [CategoryTheory.Linear.comp_smul]
  rw [automorphism_power_projector_left]

/-- The same open operator represented by one typed coupon. -/
noncomputable def openKirbyEncirclingCoupon
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (X : C) : Diagram C (.atom X) (.atom X) :=
  atomicCoupon "open-kirby-encircling-operator"
    (openKirbyEncirclingOperator 𝒞.premodular X)

/-- Insert an integral twisting coupon immediately before the open operator. -/
noncomputable def powerThenOpenKirbyEncirclingCoupon
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C)
    (exponent : ℤ) : Diagram C (.atom X) (.atom X) :=
  atomicCoupon "power-then-open-kirby-encircling-operator"
    (automorphismObjectPower automorphism X exponent ≫
      openKirbyEncirclingOperator 𝒞.premodular X)

/-- The source-backed open killing theorem is stable in every exterior. -/
theorem powerThenOpenKirbyEncircling_eval_eq_inContext
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (X : C)
    (exponent : ℤ)
    (context : Context C (.atom X) (.atom X) .unit .unit) :
    Diagram.eval C
        (Context.plug C context
          (powerThenOpenKirbyEncirclingCoupon
            𝒞 automorphism X exponent)) =
      Diagram.eval C
        (Context.plug C context
          (openKirbyEncirclingCoupon 𝒞 X)) :=
  Context.eval_plug_congr C context (by
    simpa only [powerThenOpenKirbyEncirclingCoupon,
      openKirbyEncirclingCoupon, atomicCoupon, Diagram.eval] using
      automorphism_power_openKirbyEncircling_left
        𝒞 automorphism X exponent)

/-- Machine-visible status of the open categorical bridge. -/
def currentStatus : String :=
  "PASS_OPEN_MODULAR_KILLING_IMPLIES_CONTEXT_CLOSED_TWIST_NEUTRALITY"

end TwistedYetter.Kirby.ModularDottedEncircling
