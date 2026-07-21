import TwistedYetter.Kirby.ComponentRibbonDiagram
import TwistedYetter.Kirby.ModularDottedEncircling

/-!
# Category-neutral dotted encircling windows

This file supplies the exact free-diagram window used by the dotted-handle
compiler.  It is intentionally below every invariant and every linear Kirby
colour sum: the syntax records only one serialized component ID surrounding
one parenthesized component boundary.

The signed multiplicity below is the oriented intersection count seen by a
dotted spanning disk.  A later topology certificate must prove that these
integers agree with the appropriate handle-boundary row; no such equality is
assumed here.
-/

namespace TwistedYetter.Kirby.ComponentDottedEncircling

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.ModularDottedEncircling

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Oriented multiplicity of one component ID in a free boundary word. -/
def signedMultiplicity (componentId : String) : ComponentBoundary → ℤ
  | .unit => 0
  | .atom component =>
      if component.componentId = componentId then
        match component.orientation with
        | .positive => 1
        | .negative => -1
      else
        0
  | .tensor left right =>
      signedMultiplicity componentId left +
        signedMultiplicity componentId right

@[simp] theorem signedMultiplicity_unit (componentId : String) :
    signedMultiplicity componentId .unit = 0 :=
  rfl

@[simp] theorem signedMultiplicity_tensor
    (componentId : String)
    (left right : ComponentBoundary) :
    signedMultiplicity componentId (.tensor left right) =
      signedMultiplicity componentId left +
        signedMultiplicity componentId right :=
  rfl

@[simp] theorem signedMultiplicity_positive_same (componentId : String) :
    signedMultiplicity componentId
        (.atom (positiveAtom componentId)) = 1 := by
  simp [signedMultiplicity, positiveAtom]

@[simp] theorem signedMultiplicity_negative_same (componentId : String) :
    signedMultiplicity componentId
        (.atom (negativeAtom componentId)) = -1 := by
  simp [signedMultiplicity, negativeAtom]

@[simp] theorem signedMultiplicity_atom_other
    (componentId otherId : String)
    (different : otherId ≠ componentId)
    (orientation : TwistedYetter.Kirby.Presentation.Orientation) :
    signedMultiplicity componentId
        (.atom ⟨otherId, orientation⟩) = 0 := by
  simp [signedMultiplicity, different]

/-- A component absent from the boundary word has signed multiplicity zero. -/
theorem signedMultiplicity_eq_zero_of_not_mem
    (componentId : String)
    (boundary : ComponentBoundary)
    (absent : componentId ∉ boundary.componentIds) :
    signedMultiplicity componentId boundary = 0 := by
  induction boundary with
  | unit => rfl
  | atom component =>
      simp only [ComponentBoundary.componentIds, List.mem_singleton] at absent
      have different : component.componentId ≠ componentId := by
        intro equal
        exact absent equal.symm
      simp [signedMultiplicity, different]
  | tensor left right leftIH rightIH =>
      simp only [ComponentBoundary.componentIds, List.mem_append,
        not_or] at absent
      simp [signedMultiplicity, leftIH absent.1, rightIH absent.2]

namespace ComponentDiagram

/--
One free dotted meridian around an arbitrary parenthesized boundary.

All associators and unitors are explicit.  The two crossings are the positive
double braiding used by the open modular killing identity.
-/
def openDottedEncircling
    (dottedId : String)
    (inside : ComponentBoundary) :
    ComponentDiagram inside inside :=
  let dotted : ComponentBoundary :=
    .atom (positiveAtom dottedId)
  let dottedDual : ComponentBoundary :=
    .atom (negativeAtom dottedId)
  .leftUnitorInv inside ≫ᶜ
    (.cupPositiveNegative dottedId ⊗ᶜ .identity inside) ≫ᶜ
    .associatorHom dotted dottedDual inside ≫ᶜ
    (.identity dotted ⊗ᶜ
      (.crossingPositive dottedDual inside ≫ᶜ
        .crossingPositive inside dottedDual)) ≫ᶜ
    .associatorInv dotted dottedDual inside ≫ᶜ
    (.capPositiveNegative dottedId ⊗ᶜ .identity inside) ≫ᶜ
    .leftUnitorHom inside

/--
Interpreting the free window gives exactly the simple-labelled open
encircling morphism.  The two diagrams use different boundary syntax, so the
statement compares their evaluated morphisms.
-/
theorem openDottedEncircling_interpret_eval
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (labelOf : String → S)
    (dottedId : String)
    (inside : ComponentBoundary) :
    Diagram.eval C
        ((openDottedEncircling dottedId inside).interpret data labelOf) =
      Diagram.eval C
        (openEncirclingDiagram data (labelOf dottedId)
          (inside.interpret data labelOf).denote) := by
  rfl

end ComponentDiagram

/-- Machine-visible scope: free window and its interpretation, not a global movie. -/
def currentStatus : String :=
  "PASS_FREE_DOTTED_ENCIRCLING_WINDOW_AND_SIGNED_MULTIPLICITY"

end TwistedYetter.Kirby.ComponentDottedEncircling
