import TwistedYetter.Kirby.ComponentRibbonDiagram
import TwistedYetter.Kirby.PresentationIsotopy

/-!
# Shared open modular killing input

This module proves the simple-labelled open modular killing identity from
three standard EGNO inputs: the partial-trace character formula, weighted
S-column orthogonality, and nonvanishing of simple quantum dimensions.

The closed Hopf identity is deliberately absent.  It is derived downstream by
closing this operator with the canonical pivotal trace.
-/

namespace TwistedYetter.Kirby.ModularOpenKilling

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.ComponentRibbonDiagram
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

/--
The categorical partial trace represented by `openEncirclingDiagram`, written
without graphical syntax.
-/
noncomputable def openEncirclingPartialTrace
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (simple : S)
    (X : C) : X ⟶ X :=
  let Y := data.simple simple
  (λ_ X).inv ≫
    ((@ExactPairing.coevaluation C _ _ Y Yᘁ inferInstance) ⊗ₘ 𝟙 X) ≫
    (α_ Y Yᘁ X).hom ≫
    (𝟙 Y ⊗ₘ
      ((β_ Yᘁ X).hom ≫ (β_ X Yᘁ).hom)) ≫
    (α_ Y Yᘁ X).inv ≫
    ((@ExactPairing.evaluation C _ _ Yᘁ Y
      (pivotalReverseExactPairing data.pivotal Y)) ⊗ₘ 𝟙 X) ≫
    (λ_ X).hom

/--
The local diagram compiler has exactly the EGNO partial-trace semantics.
-/
theorem openEncirclingDiagram_eval
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (simple : S)
    (X : C) :
    Diagram.eval C (openEncirclingDiagram data simple X) =
      openEncirclingPartialTrace data simple X := by
  rfl

/-- Schur scalar of one simple-labelled partial-trace operator. -/
noncomputable def openEncirclingSimpleScalar
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (loop encircled : S) : K :=
  letI : Simple (data.simple encircled) :=
    data.simple_isSimple encircled
  data.toFusionCategoryData.simpleScalar
    (data.simple encircled)
    (openEncirclingPartialTrace data loop (data.simple encircled))

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
EGNO Section 8.13's partial-trace character identity, specialized to the
explicit categorical partial trace used by `openEncirclingDiagram`.

This is a textbook identity about a ribbon fusion category.  The equality
between our diagram evaluator and its categorical left-hand side is proved
locally by `openEncirclingDiagram_eval`.
-/
axiom egno_partialTraceCharacter
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (loop encircled : S) :
    𝒞.premodular.quantumDimension encircled *
        openEncirclingSimpleScalar 𝒞.premodular loop encircled =
      premodularSMatrix 𝒞.premodular loop encircled

/--
The weighted S-column orthogonality calculation written explicitly in the
proof of EGNO Proposition 8.14.2.
-/
axiom egno_weightedSColumn
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (encircled : S) :
    ∑ loop,
        𝒞.premodular.quantumDimension loop *
          premodularSMatrix 𝒞.premodular loop encircled =
      if encircled =
          𝒞.premodular.toFusionCategoryData.unitIndex then
        𝒞.premodular.globalDimension
      else
        0

/--
Every simple quantum dimension in a characteristic-zero ribbon fusion
category is nonzero; see EGNO immediately after equation (8.40), before
Remark 8.10.13.
-/
axiom egno_simpleQuantumDimension_ne_zero
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (simple : S) :
    𝒞.premodular.quantumDimension simple ≠ 0

/--
The scalar of the open meridian operator on one simple object.

Schur's lemma guarantees that this scalar determines the complete
endomorphism.
-/
noncomputable def openKirbyEncirclingScalar
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (simple : S) : K :=
  letI : Simple (data.simple simple) := data.simple_isSimple simple
  data.toFusionCategoryData.simpleScalar
    (data.simple simple)
    (openKirbyEncirclingOperator data (data.simple simple))

/--
Schur's lemma reconstructs the complete open operator from its scalar.

This is kernel-checked category theory; it is not part of the imported modular
killing formula.
-/
theorem openKirbyEncirclingOperator_eq_scalar_smul
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (simple : S) :
    openKirbyEncirclingOperator data (data.simple simple) =
      openKirbyEncirclingScalar data simple •
        𝟙 (data.simple simple) := by
  letI : Simple (data.simple simple) := data.simple_isSimple simple
  symm
  exact
    (data.toFusionCategoryData.simpleEndLinearEquiv
      (data.simple simple)).apply_symm_apply
        (openKirbyEncirclingOperator data (data.simple simple))

/--
Scalarization commutes with the finite Kirby-colour sum.
-/
theorem openKirbyEncirclingScalar_eq_sum
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (encircled : S) :
    openKirbyEncirclingScalar 𝒞.premodular encircled =
      ∑ loop,
        𝒞.premodular.quantumDimension loop *
          openEncirclingSimpleScalar 𝒞.premodular loop encircled := by
  letI : Simple (𝒞.premodular.simple encircled) :=
    𝒞.premodular.simple_isSimple encircled
  unfold openKirbyEncirclingScalar openKirbyEncirclingOperator
  change
    (𝒞.premodular.toFusionCategoryData.simpleEndLinearEquiv
      (𝒞.premodular.simple encircled)).symm
        (∑ simple,
          𝒞.premodular.quantumDimension simple •
            Diagram.eval C
              (openEncirclingDiagram 𝒞.premodular simple
                (𝒞.premodular.simple encircled))) =
      _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro loop _
  rw [openEncirclingDiagram_eval]
  change
    (𝒞.premodular.toFusionCategoryData.simpleEndLinearEquiv
      (𝒞.premodular.simple encircled)).symm
        (𝒞.premodular.quantumDimension loop •
          openEncirclingPartialTrace 𝒞.premodular loop
            (𝒞.premodular.simple encircled)) =
      𝒞.premodular.quantumDimension loop •
        (𝒞.premodular.toFusionCategoryData.simpleEndLinearEquiv
          (𝒞.premodular.simple encircled)).symm
          (openEncirclingPartialTrace 𝒞.premodular loop
            (𝒞.premodular.simple encircled))
  exact
    LinearEquiv.map_smul
      (𝒞.premodular.toFusionCategoryData.simpleEndLinearEquiv
        (𝒞.premodular.simple encircled)).symm
      (𝒞.premodular.quantumDimension loop)
      (openEncirclingPartialTrace 𝒞.premodular loop
        (𝒞.premodular.simple encircled))

/--
Multiplying the open Kirby scalar by the encircled object's dimension gives
the weighted S-column.
-/
theorem quantumDimension_mul_openKirbyEncirclingScalar
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (encircled : S) :
    𝒞.premodular.quantumDimension encircled *
        openKirbyEncirclingScalar 𝒞.premodular encircled =
      ∑ loop,
        𝒞.premodular.quantumDimension loop *
          premodularSMatrix 𝒞.premodular loop encircled := by
  rw [openKirbyEncirclingScalar_eq_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro loop _
  rw [← egno_partialTraceCharacter 𝒞 loop encircled]
  ring

/--
The scalar open modular killing formula, now derived from EGNO's
partial-trace character identity and weighted S-column orthogonality.
-/
theorem baerenzBarrett_tham_openKirbyKilling_simpleScalar
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (simple : S) :
    openKirbyEncirclingScalar 𝒞.premodular simple =
      if simple =
          𝒞.premodular.toFusionCategoryData.unitIndex then
        𝒞.premodular.globalDimension
      else
        0 := by
  have weighted :=
    (quantumDimension_mul_openKirbyEncirclingScalar 𝒞 simple).trans
      (egno_weightedSColumn 𝒞 simple)
  split_ifs with h
  · subst simple
    simpa [𝒞.premodular.quantumDimension_unit] using weighted
  · have scalar_zero :
        openKirbyEncirclingScalar 𝒞.premodular simple = 0 := by
      have weighted_zero :
          𝒞.premodular.quantumDimension simple *
              openKirbyEncirclingScalar 𝒞.premodular simple = 0 := by
        simpa [h] using weighted
      exact (mul_eq_zero.mp weighted_zero).resolve_left
        (egno_simpleQuantumDimension_ne_zero 𝒞 simple)
    exact scalar_zero

/--
The label-resolved open modular killing identity, derived from Schur
scalarization and the one remaining scalar formula.
-/
theorem baerenzBarrett_tham_openKirbyKilling_simple
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (simple : S) :
    openKirbyEncirclingOperator 𝒞.premodular
        (𝒞.premodular.simple simple) =
      if simple =
          𝒞.premodular.toFusionCategoryData.unitIndex then
        𝒞.premodular.globalDimension •
          𝟙 (𝒞.premodular.simple simple)
      else
        0 := by
  rw [openKirbyEncirclingOperator_eq_scalar_smul]
  rw [baerenzBarrett_tham_openKirbyKilling_simpleScalar 𝒞 simple]
  split <;> simp

/-- Canonical pivotal closure of an endomorphism. -/
noncomputable def pivotalClosure
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (X : C)
    (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  pivotalTrace data.pivotal f

theorem pivotalClosure_add
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (X : C)
    (f g : X ⟶ X) :
    pivotalClosure data X (f + g) =
      pivotalClosure data X f + pivotalClosure data X g := by
  simp [pivotalClosure, pivotalTrace, leftCategoricalTrace,
    Preadditive.add_comp, Preadditive.comp_add]

theorem pivotalClosure_smul
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (X : C)
    (r : K)
    (f : X ⟶ X) :
    pivotalClosure data X (r • f) =
      r • pivotalClosure data X f := by
  simp [pivotalClosure, pivotalTrace, leftCategoricalTrace,
    CategoryTheory.Linear.comp_smul,
    CategoryTheory.Linear.smul_comp]

noncomputable def pivotalClosureLinearMap
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (X : C) :
    (X ⟶ X) →ₗ[K] (𝟙_ C ⟶ 𝟙_ C) where
  toFun := pivotalClosure data X
  map_add' := pivotalClosure_add data X
  map_smul' := pivotalClosure_smul data X

theorem pivotalClosure_sum
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (X : C)
    (f : S → (X ⟶ X)) :
    pivotalClosure data X (∑ s, f s) =
      ∑ s, pivotalClosure data X (f s) :=
  map_sum (pivotalClosureLinearMap data X) f Finset.univ

/--
The free Hopf pair is literally the pivotal closure of its open dotted
meridian after interpretation.
-/
theorem oneTwoHopfPair_eval_eq_pivotalClosure
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (dottedId twoHandleId : String)
    (labelOf : String → S) :
    Diagram.eval C
        ((ComponentDiagram.oneTwoHopfPair
          dottedId twoHandleId).interpret data labelOf) =
      pivotalClosure data (data.simple (labelOf twoHandleId))
        (Diagram.eval C
          (openEncirclingDiagram data (labelOf dottedId)
            (data.simple (labelOf twoHandleId)))) := by
  simp only [ComponentDiagram.oneTwoHopfPair,
    ComponentDiagram.openDottedEncircling,
    ComponentDiagram.interpret, openEncirclingDiagram,
    pivotalClosure, pivotalTrace, leftCategoricalTrace,
    pivotalReverseExactPairing,
    CategoryTheory.ExactPairing.evaluation,
    CategoryTheory.exactPairingCongrRight,
    leftUnitorInvDiagram, leftUnitorHomDiagram,
    associatorHomDiagram, associatorInvDiagram,
    leftAssociated, rightAssociated, atom,
    Diagram.eval, Boundary.denote]
  monoidal

theorem pivotalClosure_identity_closedScalar
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (simple : S) :
    data.toFusionCategoryData.closedScalar
        (pivotalClosure data (data.simple simple)
          (𝟙 (data.simple simple))) =
      data.quantumDimension simple := by
  simp [pivotalClosure, RibbonFusionCategoryData.quantumDimension,
    RibbonFusionCategoryData.categoricalDimension,
    pivotalTrace, pivotalDimension]

end TwistedYetter.Kirby.ModularOpenKilling
