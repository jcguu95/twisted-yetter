import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Independent human specification of the algebraic input

This file is translated directly from the following human definitions and does
not import this repository's EGNO or Twisted Yetter algebraic implementation:

* EGNO, Definition 4.1.1: fusion category;
* EGNO, Definition 8.10.1: ribbon structure;
* EGNO, Proposition 8.10.12 and Definition 8.13.1: premodular category;
* EGNO, Definition 2.4.8: monoidal natural transformation, specialized to an
  automorphism of the identity functor.

The ground field is algebraically closed of characteristic zero, as required at
the start of EGNO Section 8.13.
-/

namespace TwistedYetter.Kirby.Final.IndependentAlgebraicInput

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance independentAbelianHasFiniteBiproducts :
    HasFiniteBiproducts C :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/--
EGNO Definition 4.1.1, expanded for an explicitly indexed finite set of
simple objects.

The ambient typeclasses supply a `K`-linear abelian rigid monoidal category
whose tensor product is bilinear. The fields below state finite
semisimplicity and `End(𝟙) = K` without hiding either condition behind the
name "fusion".
-/
structure FusionCategorySemantics where
  simple : S → C
  simple_isSimple : (s : S) → Simple (simple s)
  simple_pairwise :
    {s t : S} → Nonempty (simple s ≅ simple t) → s = t
  multiplicity : C → S → ℕ
  semisimple_decomposition :
    (X : C) →
      (⨁ fun p : Σ s, Fin (multiplicity X s) => simple p.1) ≅ X
  hom_finite :
    (X Y : C) → FiniteDimensional K (X ⟶ Y)
  unit_endomorphism_is_scalar :
    (f : 𝟙_ C ⟶ 𝟙_ C) →
      ∃! scalar : K, f = scalar • 𝟙 (𝟙_ C)

/--
EGNO Definition 8.10.1.

The first law is the balancing equation
`θ_(X⊗Y) = c_(X,Y) c_(Y,X) (θ_X ⊗ θ_Y)` in Lean's left-to-right
composition order. The second is compatibility with the selected right dual.
-/
structure RibbonStructureSemantics where
  twist : 𝟭 C ≅ 𝟭 C
  balancing :
    (X Y : C) →
      twist.hom.app (X ⊗ Y) =
        (β_ X Y).hom ≫ (β_ Y X).hom ≫
          (twist.hom.app X ⊗ₘ twist.hom.app Y)
  dual_compatible :
    (X : C) →
      (twist.hom.app X)ᘁ = twist.hom.app (Xᘁ)

/--
EGNO Definition 8.13.1: a premodular category is a ribbon fusion category.

Proposition 8.10.12 identifies this, equivalently, with a braided fusion
category carrying a spherical structure. We choose the ribbon presentation
because the graphical evaluator uses the twist explicitly.
-/
structure PremodularCategorySemantics where
  fusion : FusionCategorySemantics (K := K) (C := C) (S := S)
  ribbon : RibbonStructureSemantics (C := C)

/--
EGNO Definition 2.4.8 specialized to the canonical monoidal identity functor.

Thus `η` is not merely a natural automorphism: it preserves tensor products
and the tensor unit.
-/
structure TensorIdentityCharacterSemantics where
  iso : 𝟭 C ≅ 𝟭 C
  tensor :
    (X Y : C) →
      iso.hom.app (X ⊗ Y) =
        iso.hom.app X ⊗ₘ iso.hom.app Y
  unit :
    iso.hom.app (𝟙_ C) = 𝟙 (𝟙_ C)

/-- The intended human algebraic input is exactly `(𝒞, η)`. -/
abbrev TwistedPremodularCategorySemantics :=
  PremodularCategorySemantics (K := K) (C := C) (S := S) ×
    TensorIdentityCharacterSemantics (C := C)

end TwistedYetter.Kirby.Final.IndependentAlgebraicInput
