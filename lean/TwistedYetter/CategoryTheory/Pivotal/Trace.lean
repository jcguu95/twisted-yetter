import Mathlib.CategoryTheory.Monoidal.Linear
import TwistedYetter.CategoryTheory.Pivotal.Basic

/-!
# Linearity of pivotal traces

The categorical trace of EGNO equation (4.8), and hence the pivotal trace of
equation (8.40), are linear in the morphism being closed.
-/

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

universe v u uK

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [Preadditive C] [MonoidalPreadditive C]

@[simp]
theorem leftCategoricalTrace_zero {X : C} :
    leftCategoricalTrace (0 : X ⟶ (Xᘁ)ᘁ) = 0 := by
  simp [leftCategoricalTrace]

theorem leftCategoricalTrace_add {X : C} (f g : X ⟶ (Xᘁ)ᘁ) :
    leftCategoricalTrace (f + g) =
      leftCategoricalTrace f + leftCategoricalTrace g := by
  simp [leftCategoricalTrace, Preadditive.comp_add, Preadditive.add_comp]

variable (K : Type uK) [Field K] [Linear K C] [MonoidalLinear K C]

theorem leftCategoricalTrace_smul {X : C} (scalar : K)
    (f : X ⟶ (Xᘁ)ᘁ) :
    leftCategoricalTrace (scalar • f) =
      scalar • leftCategoricalTrace f := by
  simp [leftCategoricalTrace]

/-- The left categorical trace as a linear map. -/
def leftCategoricalTraceLinearMap (X : C) :
    (X ⟶ (Xᘁ)ᘁ) →ₗ[K] (𝟙_ C ⟶ 𝟙_ C) where
  toFun := leftCategoricalTrace
  map_add' := leftCategoricalTrace_add
  map_smul' := leftCategoricalTrace_smul K

variable [(rightDoubleDualFunctor C).Monoidal]

theorem pivotalTrace_smul (pivotal : PivotalStructure C) {X : C}
    (scalar : K) (f : X ⟶ X) :
    pivotalTrace pivotal (scalar • f) =
      scalar • pivotalTrace pivotal f := by
  simp [pivotalTrace, leftCategoricalTrace_smul K]

theorem pivotalTrace_add (pivotal : PivotalStructure C) {X : C}
    (f g : X ⟶ X) :
    pivotalTrace pivotal (f + g) =
      pivotalTrace pivotal f + pivotalTrace pivotal g := by
  simp [pivotalTrace, leftCategoricalTrace_add]

/-- The pivotal trace of an object as a linear map on its endomorphisms. -/
def pivotalTraceLinearMap (pivotal : PivotalStructure C) (X : C) :
    (X ⟶ X) →ₗ[K] (𝟙_ C ⟶ 𝟙_ C) where
  toFun := pivotalTrace pivotal
  map_add' := pivotalTrace_add pivotal
  map_smul' := pivotalTrace_smul K pivotal

end CategoryTheory
