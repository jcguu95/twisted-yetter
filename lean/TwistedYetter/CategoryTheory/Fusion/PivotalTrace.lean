import TwistedYetter.CategoryTheory.Fusion.Schur
import TwistedYetter.CategoryTheory.Pivotal.Trace

/-!
# Pivotal traces on simple objects of a fusion category

The simple tensor unit identifies closed categorical traces with scalars.  On
a simple object of nonzero pivotal dimension, that scalar trace detects the
endomorphism by Schur's lemma.
-/

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

universe v uK uC uI

variable
  (K : Type uK) [Field K] [IsAlgClosed K]
  {C : Type uC} [Category.{v} C] [Abelian C] [Linear K C]
  [MonoidalCategory C] [RigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear K C]
  [FusionCategory.{v, uK, uC, uI} K C]
  [(rightDoubleDualFunctor C).Monoidal]

/-- The scalar-valued pivotal trace on one object. -/
noncomputable def scalarPivotalTraceLinearMap
    (pivotal : PivotalStructure C) (X : C) :
    (X ⟶ X) →ₗ[K] K := by
  letI : Simple (𝟙_ C) := FusionCategory.tensorUnit_simple (K := K)
  exact (simpleEndLinearEquiv K (𝟙_ C)).symm.toLinearMap.comp
    (pivotalTraceLinearMap K pivotal X)

include K

/--
On a simple object of nonzero pivotal dimension, equality of pivotal traces
implies equality of endomorphisms.
-/
theorem simple_endomorphism_eq_of_pivotalTrace_eq
    (pivotal : PivotalStructure C) (X : C) [Simple X]
    (dimension_ne_zero : pivotalDimension pivotal X ≠ 0)
    {f g : X ⟶ X}
    (trace_eq : pivotalTrace pivotal f = pivotalTrace pivotal g) :
    f = g := by
  letI : Simple (𝟙_ C) := FusionCategory.tensorUnit_simple (K := K)
  apply simple_endomorphism_eq_of_trace_eq K X
    (scalarPivotalTraceLinearMap K pivotal X)
  · change
      (simpleEndLinearEquiv K (𝟙_ C)).symm
        (pivotalTrace pivotal (𝟙 X)) ≠ 0
    have trace_identity :
        pivotalTrace pivotal (𝟙 X) = pivotalDimension pivotal X := by
      simp [pivotalTrace, pivotalDimension]
    rw [trace_identity]
    intro scalar_zero
    apply dimension_ne_zero
    apply (simpleEndLinearEquiv K (𝟙_ C)).symm.injective
    simpa using scalar_zero
  · exact congrArg
      (simpleEndLinearEquiv K (𝟙_ C)).symm trace_eq

end CategoryTheory
