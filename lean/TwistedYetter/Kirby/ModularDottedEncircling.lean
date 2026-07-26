import TwistedYetter.Kirby.ModularVacuumProjector
import TwistedYetter.Kirby.PresentationIsotopy

/-!
# The open modular dotted-encircling operator

This module states the standard modular killing identity at its useful open
tangle boundary.  The weighted Kirby-coloured meridian around an arbitrary
object is the global dimension times the projector onto all tensor-unit
summands.  The open version can be inserted into an arbitrary exterior
tangle; its closed Hopf-link specialization is now derived from pivotal
closure rather than imported separately.

The open killing identity itself is an explicit literature axiom, sourced to
Bärenz--Barrett Lemmas 2.46--2.47 and Tham Definition 5.11 (`k = 3`).
Everything involving the homological tensor-automorphism coupon is proved
below from that identity and the monoidal naturality already formalized in
`ModularVacuumProjector`.
-/

namespace TwistedYetter.Kirby.ModularDottedEncircling

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.ModularOpenKilling
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
noncomputable abbrev openEncirclingDiagram
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (simple : S)
    (X : C) : Diagram C (.atom X) (.atom X) :=
  ModularOpenKilling.openEncirclingDiagram data simple X

/-- The finite dimension-weighted open meridian operator. -/
noncomputable abbrev openKirbyEncirclingOperator
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (X : C) : X ⟶ X :=
  ModularOpenKilling.openKirbyEncirclingOperator data X

/--
Sliding a coupon through one fixed-label open meridian.

This is naturality of the double braiding together with functoriality of the
cup-cap trace; it is proved from the interpreted diagram rather than assumed
as part of the modular killing statement.
-/
theorem openEncirclingDiagram_naturality
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (simple : S)
    {X Y : C}
  (f : X ⟶ Y) :
    f ≫ Diagram.eval C (openEncirclingDiagram data simple Y) =
      Diagram.eval C (openEncirclingDiagram data simple X) ≫ f := by
  simp only [openEncirclingDiagram,
    ModularOpenKilling.openEncirclingDiagram, leftUnitorInvDiagram,
    leftUnitorHomDiagram, associatorHomDiagram, associatorInvDiagram,
    leftAssociated, rightAssociated, atom, Diagram.eval, Boundary.denote]
  let A := data.simple simple
  let B := Aᘁ
  letI reversePairing : ExactPairing B A :=
    pivotalReverseExactPairing data.pivotal A
  have cup_naturality :
      (𝟙_ C ◁ f) ≫ (η_ A B ⊗ₘ 𝟙 Y) =
        (η_ A B ⊗ₘ 𝟙 X) ≫ (A ⊗ B) ◁ f := by
    rw [← id_tensorHom]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [Category.id_comp, Category.comp_id]
    rw [← id_tensorHom (A ⊗ B) f]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have double_braiding_naturality :
      (B ◁ f) ≫ (β_ B Y).hom ≫ (β_ Y B).hom =
        (β_ B X).hom ≫ (β_ X B).hom ≫ (B ◁ f) := by
    rw [BraidedCategory.braiding_naturality_right_assoc]
    rw [BraidedCategory.braiding_naturality_left]
  have whiskered_double_braiding_naturality :
      (A ◁ B ◁ f) ≫
          (𝟙 A ⊗ₘ
            ((β_ B Y).hom ≫ (β_ Y B).hom)) =
        (𝟙 A ⊗ₘ
            ((β_ B X).hom ≫ (β_ X B).hom)) ≫
          (A ◁ B ◁ f) := by
    simpa only [MonoidalCategory.id_tensorHom, whiskerLeft_comp,
      Category.assoc] using
      congrArg (fun morphism => A ◁ morphism)
        double_braiding_naturality
  have cap_naturality :
      ((A ⊗ B) ◁ f) ≫ (ε_ B A ⊗ₘ 𝟙 Y) =
        (ε_ B A ⊗ₘ 𝟙 X) ≫ (𝟙_ C ◁ f) := by
    rw [← id_tensorHom]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [Category.id_comp, Category.comp_id]
    rw [← id_tensorHom (𝟙_ C) f]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  slice_lhs 1 2 =>
    rw [leftUnitor_inv_naturality]
  slice_lhs 2 3 =>
    exact cup_naturality
  slice_lhs 3 4 =>
    rw [associator_naturality_right]
  slice_lhs 4 5 =>
    exact whiskered_double_braiding_naturality
  slice_lhs 5 6 =>
    rw [associator_inv_naturality_right]
  slice_lhs 6 7 =>
    exact cap_naturality
  slice_lhs 7 8 =>
    rw [MonoidalCategory.leftUnitor_naturality]
  dsimp only [A, B]
  simp only [Category.assoc]

/-- The full Kirby-coloured open meridian is natural in the open strand. -/
theorem openKirbyEncirclingOperator_naturality
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    {X Y : C}
    (f : X ⟶ Y) :
    f ≫ openKirbyEncirclingOperator data Y =
      openKirbyEncirclingOperator data X ≫ f := by
  classical
  simp only [openKirbyEncirclingOperator,
    ModularOpenKilling.openKirbyEncirclingOperator]
  rw [Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro simple _
  let r := data.quantumDimension simple
  let leftOperator :=
    Diagram.eval C (openEncirclingDiagram data simple X)
  let rightOperator :=
    Diagram.eval C (openEncirclingDiagram data simple Y)
  calc
    f ≫ (r • rightOperator) =
        r • (f ≫ rightOperator) := by
      exact CategoryTheory.Linear.comp_smul X Y Y f r rightOperator
    _ = r • (leftOperator ≫ f) := by
      exact congrArg (fun morphism => r • morphism)
        (openEncirclingDiagram_naturality data simple f)
    _ = (r • leftOperator) ≫ f := by
      exact (CategoryTheory.Linear.smul_comp X X Y r leftOperator f).symm

/-- Stable source metadata for the one imported open graphical identity. -/
def openKillingSourceRef : String :=
  ModularOpenKilling.openKillingSourceRef

def openKillingSourceLocator : String :=
  ModularOpenKilling.openKillingSourceLocator

/--
The label-resolved open modular killing identity on a simple strand.

This is the irreducible graphical input.  The arbitrary-object projector
formula below is derived from it, naturality, and the stored semisimple
decomposition.
-/
theorem baerenzBarrett_tham_openKirbyKilling_simple
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (simple : S) :
    openKirbyEncirclingOperator 𝒞.premodular
        (𝒞.premodular.simple simple) =
      if simple =
          𝒞.premodular.toFusionCategoryData.unitIndex then
        globalDimension 𝒞.premodular •
          𝟙 (𝒞.premodular.simple simple)
      else
        0 := by
  simpa only [openKirbyEncirclingOperator, globalDimension,
    PremodularCategory.globalDimension] using
    ModularOpenKilling.baerenzBarrett_tham_openKirbyKilling_simple
      𝒞 simple

/--
The standard open modular killing identity on an arbitrary fusion object.

No arbitrary-object graphical law is assumed here.  Naturality moves the
operator onto every selected simple summand, and the simple killing identity
then retains exactly the tensor-unit summands.
-/
theorem baerenzBarrett_tham_openKirbyKilling
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (X : C) :
    openKirbyEncirclingOperator 𝒞.premodular X =
      globalDimension 𝒞.premodular •
        unitSummandProjector
          𝒞.premodular.toFusionCategoryData X := by
  classical
  let data := 𝒞.premodular.toFusionCategoryData
  let operator := openKirbyEncirclingOperator 𝒞.premodular
  calc
    operator X = (𝟙 X) ≫ operator X := by simp
    _ = (∑ p : data.SummandIndex X,
          data.projection X p ≫ data.inclusion X p) ≫
        operator X := by
      rw [data.sum_projection_inclusion X]
    _ = ∑ p : data.SummandIndex X,
          (data.projection X p ≫ data.inclusion X p) ≫
            operator X := by
      rw [Preadditive.sum_comp]
    _ = ∑ p : data.SummandIndex X,
          data.projection X p ≫
            operator (data.simple p.1) ≫
              data.inclusion X p := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [Category.assoc]
      rw [← openKirbyEncirclingOperator_naturality
        𝒞.premodular (data.inclusion X p)]
    _ = ∑ p : data.SummandIndex X,
          data.projection X p ≫
            (if p.1 = data.unitIndex then
              globalDimension 𝒞.premodular •
                𝟙 (data.simple p.1)
            else
              0) ≫
              data.inclusion X p := by
      apply Finset.sum_congr rfl
      intro p _
      dsimp only [operator, data]
      rw [baerenzBarrett_tham_openKirbyKilling_simple 𝒞 p.1]
    _ = globalDimension 𝒞.premodular •
        unitSummandProjector data X := by
      unfold unitSummandProjector
      rw [Finset.smul_sum]
      rw [Fintype.sum_sigma]
      calc
        (∑ s : S, ∑ i : Fin (data.multiplicity X s),
            data.projection X ⟨s, i⟩ ≫
              (if s = data.unitIndex then
                globalDimension 𝒞.premodular • 𝟙 (data.simple s)
              else
                0) ≫
                data.inclusion X ⟨s, i⟩) =
            ∑ s : S, if s = data.unitIndex then
              ∑ i : Fin (data.multiplicity X s),
                globalDimension 𝒞.premodular •
                  data.projection X ⟨s, i⟩ ≫
                    data.inclusion X ⟨s, i⟩
            else
              0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases h : s = data.unitIndex
          · subst s
            simp
          · simp [h]
        _ = ∑ i : Fin (data.multiplicity X data.unitIndex),
              globalDimension 𝒞.premodular •
                data.projection X ⟨data.unitIndex, i⟩ ≫
                  data.inclusion X ⟨data.unitIndex, i⟩ := by
          simp

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
