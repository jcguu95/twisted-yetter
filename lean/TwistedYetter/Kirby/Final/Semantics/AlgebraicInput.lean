import Mathlib.Algebra.Category.Grp.Basic
import TwistedYetter.Fusion.EGNOPremodularModular
import TwistedYetter.Fusion.EGNOTensorAutomorphism

/-!
# Human semantic specification

This file states the intended public mathematics without choosing a Kirby
implementation.  In particular, no global auxiliary model for second homology
appears here: the second homology type depends on the manifold.
-/

namespace TwistedYetter.Kirby.Final.SemanticSpecification

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped BigOperators
open TwistedYetter.Fusion.EGNO

universe uX uH uD uP uK uC vC uM

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance semanticAbelianHasFiniteBiproducts :
    HasFiniteBiproducts C :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/--
All dual-dependent semantic fields use the right dual selected by the ambient
`RigidCategory`, rather than the alternative one reconstructed from braiding.
-/
local instance semanticSelectedRigidRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/--
The human meaning of a premodular fusion category.

The ambient assumptions above supply the algebraically closed characteristic
zero field and the linear, abelian, rigid, braided monoidal category.  The
fields below state the remaining finite semisimple and ribbon data directly.
-/
structure PremodularCategory where
  simple : S → C
  simple_isSimple : (s : S) → Simple (simple s)
  simple_pairwise :
    {s t : S} → Nonempty (simple s ≅ simple t) → s = t
  simple_complete :
    (X : C) → Simple X → ∃ s, Nonempty (X ≅ simple s)
  hom_finite :
    (X Y : C) → FiniteDimensional K (X ⟶ Y)
  multiplicity : C → S → ℕ
  decomposition :
    (X : C) →
      (⨁ fun p : Σ s, Fin (multiplicity X s) => simple p.1) ≅ X
  unitIndex : S
  unitIso : simple unitIndex ≅ 𝟙_ C
  dualIndex : S → S
  dualIso : (s : S) → (simple s)ᘁ ≅ simple (dualIndex s)
  twist : 𝟭 C ≅ 𝟭 C
  twist_tensor :
    (X Y : C) →
      twist.hom.app (X ⊗ Y) =
        (β_ X Y).hom ≫ (β_ Y X).hom ≫
          (twist.hom.app X ⊗ₘ twist.hom.app Y)
  twist_dual :
    (X : C) →
      (twist.hom.app X)ᘁ =
        twist.hom.app (Xᘁ)

/--
The human meaning of the twisting character `η`: a natural automorphism of
the identity functor satisfying the tensor and unit laws.
-/
structure TensorIdentityCharacter where
  iso : 𝟭 C ≅ 𝟭 C
  tensor :
    (X Y : C) →
      iso.hom.app (X ⊗ Y) =
        iso.hom.app X ⊗ₘ iso.hom.app Y
  unit :
    iso.hom.app (𝟙_ C) = 𝟙 (𝟙_ C)

/-- The intended public algebraic input is exactly the pair `(𝒞, η)`. -/
abbrev TwistedPremodularCategory :=
  PremodularCategory (K := K) (C := C) (S := S) ×
    TensorIdentityCharacter (C := C)


end TwistedYetter.Kirby.Final.SemanticSpecification
