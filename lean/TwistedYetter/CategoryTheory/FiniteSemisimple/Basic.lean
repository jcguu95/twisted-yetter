import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TwistedYetter.CategoryTheory.FiniteSemisimple.Chosen

/-!
# Finite semisimple categories

The definition follows EGNO, Definitions 1.5.1, 1.8.6, and 4.1.1.  Explicit
decompositions are existential witnesses; they are not fields callers may use
to alter the abstract category.
-/

namespace CategoryTheory

universe v uK uC uI

/--
A finite semisimple `K`-linear abelian category.

There are finitely many simple isomorphism classes, every object is a finite
direct sum of simples, and all morphism spaces are finite-dimensional.
-/
class FiniteSemisimpleCategory
    (K : Type uK) [Field K]
    (C : Type uC) [Category.{v} C] [Abelian C] [Linear K C] : Prop where
  hom_finite : (X Y : C) → FiniteDimensional K (X ⟶ Y)
  finite_simple_skeleton :
    Nonempty (FiniteSimpleSkeleton.{v, uC, uI} (C := C))
  finite_simple_decomposition :
    (X : C) → Nonempty (FiniteSimpleDecomposition.{v, uC, uI} X)

end CategoryTheory
