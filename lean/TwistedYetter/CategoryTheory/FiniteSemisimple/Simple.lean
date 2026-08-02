import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TwistedYetter.CategoryTheory.FiniteSemisimple.Basic

/-!
# Detecting simple objects in a finite semisimple category

In a finite semisimple linear category, a nonzero object whose endomorphism
space is one-dimensional is simple.  The proof expands a finite simple
decomposition and rules out two distinct summands using their orthogonal
idempotent projectors.
-/

namespace CategoryTheory

universe v uK uC uI

variable
  (K : Type uK) [Field K]
  {C : Type uC} [Category.{v} C] [Abelian C] [Linear K C]
  [FiniteSemisimpleCategory.{v, uK, uC, uI} K C]

include K

/--
An object of a finite semisimple category with one-dimensional endomorphism
space is simple.
-/
theorem simple_of_finrank_end_eq_one
    (A : C) (finrank_end : Module.finrank K (A ⟶ A) = 1) :
    Simple A := by
  letI : FiniteDimensional K (A ⟶ A) :=
    FiniteSemisimpleCategory.hom_finite A A
  have identity_ne_zero : (𝟙 A : A ⟶ A) ≠ 0 := by
    intro identity_zero
    haveI : Subsingleton (A ⟶ A) :=
      ⟨fun f g ↦ by
        have f_zero : f = 0 := by
          calc
            f = 𝟙 A ≫ f := by simp
            _ = 0 := by rw [identity_zero]; simp
        have g_zero : g = 0 := by
          calc
            g = 𝟙 A ≫ g := by simp
            _ = 0 := by rw [identity_zero]; simp
        exact f_zero.trans g_zero.symm⟩
    have rank_zero : Module.finrank K (A ⟶ A) = 0 :=
      finrank_zero_iff_forall_zero.mpr (fun f ↦ Subsingleton.elim f 0)
    omega
  let decomposition := Classical.choice
    (FiniteSemisimpleCategory.finite_simple_decomposition (K := K) A)
  have every_end_scalar :
      ∀ f : A ⟶ A, ∃ scalar : K, scalar • 𝟙 A = f :=
    (finrank_eq_one_iff_of_nonzero' (𝟙 A) identity_ne_zero).mp finrank_end
  have summand_nonempty : Nonempty decomposition.SummandIndex := by
    by_contra empty
    haveI : IsEmpty decomposition.SummandIndex :=
      not_nonempty_iff.mp empty
    have identity_zero : 𝟙 A = 0 := by
      rw [← decomposition.resolution_identity]
      simp
    exact identity_ne_zero identity_zero
  let distinguished := Classical.choice summand_nonempty
  have all_eq_distinguished :
      ∀ j : decomposition.SummandIndex, j = distinguished := by
    intro j
    letI : Simple (decomposition.summandObject distinguished) :=
      decomposition.summand_isSimple distinguished
    letI : Simple (decomposition.summandObject j) :=
      decomposition.summand_isSimple j
    by_contra different
    let projector : A ⟶ A :=
      decomposition.projection distinguished ≫
        decomposition.inclusion distinguished
    obtain ⟨scalar, scalar_projector⟩ := every_end_scalar projector
    have scalar_ne_zero : scalar ≠ 0 := by
      intro scalar_zero
      have projector_zero : projector = 0 := by
        rw [← scalar_projector, scalar_zero, zero_smul]
      have identity_zero :
          𝟙 (decomposition.summandObject distinguished) = 0 := by
        calc
          𝟙 (decomposition.summandObject distinguished) =
              decomposition.inclusion distinguished ≫
                projector ≫ decomposition.projection distinguished := by
            simp [projector, Category.assoc,
              decomposition.pairing_same]
          _ = 0 := by rw [projector_zero]; simp
      exact id_nonzero _ identity_zero
    have orthogonal_zero :
        decomposition.inclusion j ≫ projector ≫
            decomposition.projection j = 0 := by
      dsimp [projector]
      simp only [← Category.assoc]
      rw [decomposition.pairing_distinct j distinguished different]
      simp
    have scalar_identity_zero :
        scalar • 𝟙 (decomposition.summandObject j) = 0 := by
      calc
        scalar • 𝟙 (decomposition.summandObject j) =
            decomposition.inclusion j ≫
              (scalar • 𝟙 A) ≫ decomposition.projection j := by
          simp [decomposition.pairing_same]
        _ = decomposition.inclusion j ≫ projector ≫
              decomposition.projection j := by rw [scalar_projector]
        _ = 0 := orthogonal_zero
    exact (smul_ne_zero scalar_ne_zero (id_nonzero _)) scalar_identity_zero
  letI : Unique decomposition.SummandIndex :=
    { default := distinguished
      uniq := all_eq_distinguished }
  have projector_identity :
      decomposition.projection distinguished ≫
          decomposition.inclusion distinguished = 𝟙 A := by
    calc
      decomposition.projection distinguished ≫
          decomposition.inclusion distinguished =
          decomposition.projection default ≫
            decomposition.inclusion default := by
              rw [Unique.eq_default distinguished]
      _ = ∑ i : decomposition.SummandIndex,
          decomposition.projection i ≫ decomposition.inclusion i := by
            exact (Fintype.sum_unique
              (fun i : decomposition.SummandIndex ↦
                decomposition.projection i ≫
                  decomposition.inclusion i)).symm
      _ = 𝟙 A := decomposition.resolution_identity
  let iso : decomposition.summandObject distinguished ≅ A :=
    { hom := decomposition.inclusion distinguished
      inv := decomposition.projection distinguished
      hom_inv_id := decomposition.pairing_same distinguished
      inv_hom_id := projector_identity }
  letI : Simple (decomposition.summandObject distinguished) :=
    decomposition.summand_isSimple distinguished
  exact Simple.of_iso iso.symm

end CategoryTheory
