import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import TwistedYetter.CategoryTheory.FiniteSemisimple.Basic

/-!
# Extensionality from finite semisimple decompositions

Finite direct-sum resolutions detect equality of morphisms.  Consequently,
natural transformations between additive functors out of a finite semisimple
category are determined by their components on simple objects.

This is the semisimple reduction used in the converse direction of EGNO,
Proposition 8.10.12.  It contains no trace, Radford, or ribbon input.
-/

namespace CategoryTheory

universe v v' uK uC uD uI

section Resolution

variable {C : Type uC} [Category.{v} C] [Preadditive C]

/-- A finite resolution of the identity detects morphisms out of its object. -/
theorem hom_ext_of_finite_resolution
    {X Y : C} {I : Type uI} [Fintype I]
    {S : I → C} (projection : (i : I) → X ⟶ S i)
    (inclusion : (i : I) → S i ⟶ X)
    (resolution : (∑ i, projection i ≫ inclusion i) = 𝟙 X)
    {f g : X ⟶ Y}
    (onSummands : (i : I) → inclusion i ≫ f = inclusion i ≫ g) :
    f = g := by
  rw [← Category.id_comp f, ← Category.id_comp g, ← resolution]
  simp only [Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i _
  rw [onSummands i]

/-- A chosen finite simple decomposition detects morphisms out of its object. -/
theorem FiniteSimpleDecomposition.hom_ext
    {X Y : C} (decomposition : FiniteSimpleDecomposition.{v, uC, uI} X)
    {f g : X ⟶ Y}
    (onSummands : (i : decomposition.SummandIndex) →
      decomposition.inclusion i ≫ f = decomposition.inclusion i ≫ g) :
    f = g :=
  hom_ext_of_finite_resolution decomposition.projection
    decomposition.inclusion decomposition.resolution_identity onSummands

end Resolution

section NaturalTransformation

variable
  {C : Type uC} [Category.{v} C] [Abelian C]
  {D : Type uD} [Category.{v'} D] [Preadditive D]

/--
Natural transformations between additive functors out of a finite semisimple
category are determined by their components on simple objects.
-/
theorem natTrans_ext_of_simple
    (K : Type uK) [Field K] [Linear K C]
    [FiniteSemisimpleCategory.{v, uK, uC, uI} K C]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    (alpha beta : F ⟶ G)
    (onSimple : (X : C) → [Simple X] → alpha.app X = beta.app X) :
    alpha = beta := by
  apply NatTrans.ext
  funext X
  let decomposition := Classical.choice
    (FiniteSemisimpleCategory.finite_simple_decomposition (K := K) X)
  apply hom_ext_of_finite_resolution
    (fun i ↦ F.map (decomposition.projection i))
    (fun i ↦ F.map (decomposition.inclusion i))
  · simp only [← F.map_comp, ← F.map_sum,
      decomposition.resolution_identity, F.map_id]
  · intro i
    letI : Simple (decomposition.summandObject i) :=
      decomposition.summand_isSimple i
    rw [alpha.naturality, beta.naturality]
    rw [onSimple (decomposition.summandObject i)]

end NaturalTransformation

end CategoryTheory
