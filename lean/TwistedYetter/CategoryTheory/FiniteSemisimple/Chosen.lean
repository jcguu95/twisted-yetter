import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Simple

/-!
# Chosen finite semisimple data

This file contains explicit choices used to witness finite semisimplicity.  The
structures are separate from the `Prop`-valued category classes so downstream
computations may choose bases and summands without making those choices part of
the abstract definition.
-/

namespace CategoryTheory

open CategoryTheory.Limits

universe v u uI

variable {C : Type u} [Category.{v} C]

/-- A finite, irredundant, complete family of simple representatives. -/
structure FiniteSimpleSkeleton [HasZeroMorphisms C] where
  SimpleIndex : Type uI
  simpleFintype : Fintype SimpleIndex
  simpleDecidableEq : DecidableEq SimpleIndex
  simpleObject : SimpleIndex → C
  simple_isSimple : (i : SimpleIndex) → Simple (simpleObject i)
  simple_pairwise :
    {i j : SimpleIndex} → Nonempty (simpleObject i ≅ simpleObject j) → i = j
  simple_complete :
    (X : C) → Simple X → ∃ i, Nonempty (X ≅ simpleObject i)

attribute [instance] FiniteSimpleSkeleton.simpleFintype
attribute [instance] FiniteSimpleSkeleton.simpleDecidableEq

/--
A chosen expression of `X` as a finite direct sum of simple objects.

The inclusion/projection equations are the coordinate-free biproduct laws.
They do not choose bases in morphism spaces.
-/
structure FiniteSimpleDecomposition [Preadditive C] (X : C) where
  SummandIndex : Type uI
  summandFintype : Fintype SummandIndex
  summandDecidableEq : DecidableEq SummandIndex
  summandObject : SummandIndex → C
  summand_isSimple : (i : SummandIndex) → Simple (summandObject i)
  inclusion : (i : SummandIndex) → summandObject i ⟶ X
  projection : (i : SummandIndex) → X ⟶ summandObject i
  pairing_same :
    (i : SummandIndex) → inclusion i ≫ projection i = 𝟙 (summandObject i)
  pairing_distinct :
    (i j : SummandIndex) → i ≠ j → inclusion i ≫ projection j = 0
  resolution_identity :
    let _ := summandFintype
    (∑ i : SummandIndex, projection i ≫ inclusion i) = 𝟙 X

attribute [instance] FiniteSimpleDecomposition.summandFintype
attribute [instance] FiniteSimpleDecomposition.summandDecidableEq

end CategoryTheory
