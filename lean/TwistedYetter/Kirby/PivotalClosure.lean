import TwistedYetter.Kirby.ComponentRibbonDiagram
import TwistedYetter.Kirby.PresentationIsotopy

/-!
# Pivotal closure used by the role-aware special cut

This file contains only the linear pivotal-trace operation needed by the
premodular 1--2 cancellation proof.  It is independent of modular open
killing.
-/

namespace TwistedYetter.Kirby.PremodularPivotalClosure

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance selectedRigidRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

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

end TwistedYetter.Kirby.PremodularPivotalClosure
