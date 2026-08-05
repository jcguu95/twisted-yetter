import TwistedYetter.StableNoGo.ModularCategory

/-!
# Literature inputs for the modular numerical reduction

The only external category facts introduced here are the character-object
correspondence and the two shifted Gauss-sum identities.  They are local
category statements and contain no four-manifold or evaluator equality.

References:

* EGNO, Lemma 8.22.9: characters of the universal grading group are
  represented by invertible objects in a non-degenerate braided fusion
  category.
* EGNO, Lemma 8.15.3 and Corollary 8.15.5: shifted Gauss sums under tensoring
  by an invertible object.
* EGNO, Proposition 8.15.4: `tau_plus * tau_minus = globalDimension`.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- An object has tensor inverse when tensoring it with its right dual gives the unit. -/
def IsTensorInvertible
    {C : Type*} [Category C] [MonoidalCategory C] [RightRigidCategory C]
    (X : C) : Prop :=
  Nonempty (X ⊗ Xᘁ ≅ 𝟙_ C)

/--
The invertible simple object `g_eta` representing the monoidal identity
character through monodromy.
-/
structure ModularCharacterObject (𝒞η : TwistedModularCategory K) where
  simple : 𝒞η.category.Simple
  tensorInvertible :
    IsTensorInvertible (𝒞η.category.simpleObject simple)
  representsCharacter :
    forall X : 𝒞η.category.C,
      monodromyHom (𝒞η.category.simpleObject simple) X =
        𝟙 (𝒞η.category.simpleObject simple) ⊗ₘ
          𝒞η.character.iso.hom.app X

/-- EGNO, Lemma 8.22.9, with the monodromy convention fixed above. -/
axiom egno_characterObject_exists (𝒞η : TwistedModularCategory K) :
    Nonempty (ModularCharacterObject 𝒞η)

/-- The ribbon twist of the character object, packaged as a unit of `K`. -/
noncomputable def ModularCharacterObject.twistUnit
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) : Kˣ :=
  Units.mk0
    (simpleTwistScalar 𝒞η.toPremodular g.simple)
    (simpleTwistScalar_ne_zero 𝒞η.toPremodular g.simple)

/-- The unshifted positive Gauss sum `tau_plus`. -/
noncomputable def positiveGaussSum
    (𝒞η : TwistedPremodularCategory K) : K :=
  positiveShiftedGaussSum 𝒞η 0

/-- The unshifted negative Gauss sum `tau_minus`. -/
noncomputable def negativeGaussSum
    (𝒞η : TwistedPremodularCategory K) : K :=
  negativeShiftedGaussSum 𝒞η 0

/--
EGNO, Lemma 8.15.3 and Corollary 8.15.5, together with quadraticity of the
ribbon twist on the pointed subcategory: `tau_plus^eta(n) = theta_g^(-n^2) tau_plus`.
-/
axiom egno_positiveShiftedGaussSum
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) (n : ℤ) :
    positiveShiftedGaussSum 𝒞η.toPremodular n =
      (((g.twistUnit ^ (-(n * n)) : Kˣ) : K)) *
        positiveGaussSum 𝒞η.toPremodular

/--
EGNO, Lemma 8.15.3 and Corollary 8.15.5, together with quadraticity of the
ribbon twist on the pointed subcategory: `tau_minus^eta(n) = theta_g^(n^2) tau_minus`.
-/
axiom egno_negativeShiftedGaussSum
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) (n : ℤ) :
    negativeShiftedGaussSum 𝒞η.toPremodular n =
      (((g.twistUnit ^ (n * n) : Kˣ) : K)) *
        negativeGaussSum 𝒞η.toPremodular

/-- EGNO, Proposition 8.15.4. -/
axiom egno_gaussSums_product (𝒞η : TwistedModularCategory K) :
    positiveGaussSum 𝒞η.toPremodular *
        negativeGaussSum 𝒞η.toPremodular =
      𝒞η.category.globalDimension

theorem positiveGaussSum_ne_zero (𝒞η : TwistedModularCategory K) :
    positiveGaussSum 𝒞η.toPremodular ≠ 0 := by
  intro positiveZero
  have productZero :
      positiveGaussSum 𝒞η.toPremodular *
          negativeGaussSum 𝒞η.toPremodular = 0 := by
    rw [positiveZero, zero_mul]
  exact egno_globalDimension_ne_zero 𝒞η.category
    ((egno_gaussSums_product 𝒞η).symm.trans productZero)

theorem negativeGaussSum_ne_zero (𝒞η : TwistedModularCategory K) :
    negativeGaussSum 𝒞η.toPremodular ≠ 0 := by
  intro negativeZero
  have productZero :
      positiveGaussSum 𝒞η.toPremodular *
          negativeGaussSum 𝒞η.toPremodular = 0 := by
    rw [negativeZero, mul_zero]
  exact egno_globalDimension_ne_zero 𝒞η.category
    ((egno_gaussSums_product 𝒞η).symm.trans productZero)

end

end TwistedYetter.StableNoGo
