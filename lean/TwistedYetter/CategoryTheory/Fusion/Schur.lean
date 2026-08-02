import Mathlib.CategoryTheory.Preadditive.Schur
import TwistedYetter.CategoryTheory.Fusion.Basic

/-!
# Schur reduction in a fusion category

Over an algebraically closed field, the endomorphisms of a simple object in a
fusion category are precisely the scalar multiples of its identity.  A linear
trace which is nonzero on the identity therefore detects equality of simple
endomorphisms.
-/

namespace CategoryTheory

universe v uK uC uI

variable
  (K : Type uK) [Field K] [IsAlgClosed K]
  {C : Type uC} [Category.{v} C] [Abelian C] [Linear K C]
  [FiniteSemisimpleCategory.{v, uK, uC, uI} K C]

/-- Scalar multiplication identifies `K` with the endomorphisms of a simple object. -/
noncomputable def simpleEndLinearEquiv (X : C) [Simple X] :
    K ≃ₗ[K] (X ⟶ X) := by
  letI : FiniteDimensional K (X ⟶ X) :=
    FiniteSemisimpleCategory.hom_finite X X
  let scalarMap : K →ₗ[K] (X ⟶ X) :=
    { toFun := fun scalar ↦ scalar • 𝟙 X
      map_add' := by
        intro left right
        simp only [add_smul]
      map_smul' := by
        intro left right
        simpa only [RingHom.id_apply, smul_eq_mul] using
          (mul_smul left right (𝟙 X)) }
  refine LinearEquiv.ofBijective scalarMap ⟨?_, ?_⟩
  · intro left right equality
    have zeroScalar : (left - right) • 𝟙 X = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact equality
    by_contra different
    exact
      (smul_ne_zero (sub_ne_zero.mpr different) (id_nonzero X)) zeroScalar
  · intro f
    obtain ⟨scalar, scalar_sound⟩ := endomorphism_simple_eq_smul_id K f
    exact ⟨scalar, scalar_sound⟩

/--
A linear trace nonzero on the identity detects endomorphisms of a simple
object.  This is the exact Schur step used after EGNO's trace identity.
-/
theorem simple_endomorphism_eq_of_trace_eq
    (X : C) [Simple X]
    (trace : (X ⟶ X) →ₗ[K] K)
    (trace_identity_ne_zero : trace (𝟙 X) ≠ 0)
    {f g : X ⟶ X} (trace_eq : trace f = trace g) :
    f = g := by
  letI : FiniteDimensional K (X ⟶ X) :=
    FiniteSemisimpleCategory.hom_finite X X
  obtain ⟨left, left_eq⟩ := endomorphism_simple_eq_smul_id K f
  obtain ⟨right, right_eq⟩ := endomorphism_simple_eq_smul_id K g
  rw [← left_eq, ← right_eq] at trace_eq ⊢
  simp only [map_smul, smul_eq_mul] at trace_eq
  have scalar_eq : left = right := by
    exact mul_right_cancel₀ trace_identity_ne_zero trace_eq
  rw [scalar_eq]

end CategoryTheory
