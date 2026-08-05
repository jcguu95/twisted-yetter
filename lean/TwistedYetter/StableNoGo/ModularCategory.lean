import TwistedYetter.StableNoGo.NumericalDefinitions

/-!
# Twisted modular categories

This file contains only the modular refinement of the public premodular
input.  Numerical consequences of modularity are stated separately, with
their literature locators, in `ModularCategoryInputs`.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- A twisted premodular category whose Mueger centre is trivial. -/
structure TwistedModularCategory (K : Type uK)
    [Field K] [IsAlgClosed K] [CharZero K]
    extends TwistedPremodularCategory K where
  nondegenerate :
    forall simple : category.Simple,
      (forall X : category.C,
        monodromyHom (category.simpleObject simple) X =
          𝟙 (category.simpleObject simple ⊗ X)) ->
      Nonempty (category.simpleObject simple ≅ 𝟙_ category.C)

def TwistedModularCategory.toPremodular
    (𝒞η : TwistedModularCategory K) : TwistedPremodularCategory K :=
  𝒞η.toTwistedPremodularCategory

end

end TwistedYetter.StableNoGo
