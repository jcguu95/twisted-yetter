import Mathlib.CategoryTheory.Preadditive.Schur
import TwistedYetter.Kirby.Final.Semantics.AlgebraicInput
import TwistedYetter.Kirby.Final.Semantics.IndependentAlgebraicInput

/-!
# One-way conformance bridge for the algebraic input

The independent human specification was fixed before this file imported the
existing semantic structure. This file may only construct the independent
structure from the existing one; it may not weaken the independent statement.
-/

namespace TwistedYetter.Kirby.Final.IndependentAlgebraicBridge

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

open TwistedYetter.Kirby.Final.SemanticSpecification
open TwistedYetter.Kirby.Final.IndependentAlgebraicInput

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance bridgeAbelianHasFiniteBiproducts :
    HasFiniteBiproducts C :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/--
The existing premodular-category datum satisfies the independently fixed EGNO
semantics.
-/
noncomputable def categoryConforms
    (𝒞 :
      PremodularCategory (K := K) (C := C) (S := S)) :
    PremodularCategorySemantics (K := K) (C := C) (S := S) := by
  letI : Simple (𝒞.simple 𝒞.unitIndex) :=
    𝒞.simple_isSimple 𝒞.unitIndex
  letI : Simple (𝟙_ C) := Simple.of_iso 𝒞.unitIso.symm
  letI : FiniteDimensional K (𝟙_ C ⟶ 𝟙_ C) :=
    𝒞.hom_finite (𝟙_ C) (𝟙_ C)
  exact
    {
      fusion :=
        {
          simple := 𝒞.simple
          simple_isSimple := 𝒞.simple_isSimple
          simple_pairwise := 𝒞.simple_pairwise
          multiplicity := 𝒞.multiplicity
          semisimple_decomposition := 𝒞.decomposition
          hom_finite := 𝒞.hom_finite
          unit_endomorphism_is_scalar := by
            intro f
            obtain ⟨scalar, scalar_eq⟩ :=
              endomorphism_simple_eq_smul_id K f
            refine ⟨scalar, scalar_eq.symm, ?_⟩
            intro other other_eq
            exact
              smul_left_injective K (id_nonzero (𝟙_ C))
                (scalar_eq.trans other_eq).symm
        }
      ribbon :=
        {
          twist := 𝒞.twist
          balancing := 𝒞.twist_tensor
          dual_compatible := 𝒞.twist_dual
        }
    }

/--
The existing twisting character satisfies EGNO Definition 2.4.8 specialized
to the identity functor.
-/
def characterConforms
    (η : TensorIdentityCharacter (C := C)) :
    TensorIdentityCharacterSemantics (C := C) :=
  {
    iso := η.iso
    tensor := η.tensor
    unit := η.unit
  }

/-- Conformance of the complete pair `(𝒞, η)`. -/
noncomputable def twistedCategoryConforms
    (𝒞η :
      TwistedPremodularCategory
        (K := K) (C := C) (S := S)) :
    TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S) :=
  (categoryConforms 𝒞η.1, characterConforms 𝒞η.2)

end TwistedYetter.Kirby.Final.IndependentAlgebraicBridge
