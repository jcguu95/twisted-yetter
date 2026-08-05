import TwistedYetter.StableNoGo.ModularCharacterCorrespondence

/-!
# Literature inputs for the modular numerical reduction

The external category facts are stated at the same semantic level as their
sources: the character-object correspondence, the two `S`-matrix Gauss-sum
identities, and the standard description of the powers of the character
object.  The shifted Gauss-sum formulas used downstream are theorems below,
not literature axioms.

References:

* EGNO, Lemma 8.22.9: characters of the universal grading group are
  represented by invertible objects in a non-degenerate braided fusion
  category.
* EGNO, Lemma 8.15.3 and Corollary 8.15.5: the positive and negative
  `S`-matrix Gauss-sum identities.
* EGNO, Proposition 8.15.4: `tau_plus * tau_minus = globalDimension`.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- A character object is an invertible simple object together with the exact
EGNO (8.95) statement that it represents the prescribed character.  This
dependent pair replaces the former structure containing an unproved open
monodromy formula. -/
abbrev ModularCharacterObject (𝒞η : TwistedModularCategory K) :=
  { g : InvertibleSimpleObject 𝒞η.category //
    RepresentsIdentityCharacter 𝒞η g }

namespace ModularCharacterObject

def simple
    {𝒞η : TwistedModularCategory K} (g : ModularCharacterObject 𝒞η) :
    𝒞η.category.Simple :=
  g.1.simple

end ModularCharacterObject

/-- EGNO Lemma 8.22.9(iii), repackaged without strengthening its conclusion. -/
theorem egno_characterObject_exists (𝒞η : TwistedModularCategory K) :
    Nonempty (ModularCharacterObject 𝒞η) := by
  exact ⟨⟨egnoCharacterObject 𝒞η,
    egnoCharacterObject_represents 𝒞η⟩⟩

/-- The ribbon twist of the character object, packaged as a unit of `K`. -/
noncomputable def ModularCharacterObject.twistUnit
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) : Kˣ :=
  g.1.twistUnit

/-- The unshifted positive Gauss sum `tau_plus`. -/
noncomputable def positiveGaussSum
    (𝒞η : TwistedPremodularCategory K) : K :=
  positiveShiftedGaussSum 𝒞η 0

/-- The unshifted negative Gauss sum `tau_minus`. -/
noncomputable def negativeGaussSum
    (𝒞η : TwistedPremodularCategory K) : K :=
  negativeShiftedGaussSum 𝒞η 0

/--
EGNO, Lemma 8.15.3, equation (8.58), printed page 229:
`sum_X theta_X dim(X) s_XY = dim(Y) theta_Y⁻¹ tau⁺(C)`.
-/
axiom egno_positiveGaussSum_sMatrixIdentity
    (𝒞η : TwistedModularCategory K)
    (second : 𝒞η.category.Simple) :
    (∑ first : 𝒞η.category.Simple,
      simpleTwistScalar 𝒞η.toPremodular first *
        𝒞η.category.quantumDimension first *
        sMatrixEntry 𝒞η.toPremodular first second) =
      𝒞η.category.quantumDimension second *
        (simpleTwistScalar 𝒞η.toPremodular second)⁻¹ *
        positiveGaussSum 𝒞η.toPremodular

/--
EGNO, Corollary 8.15.5, equation (8.61), printed page 230:
`sum_X theta_X⁻¹ dim(X) s_XY = dim(Y) theta_Y tau⁻(C)`.
-/
axiom egno_negativeGaussSum_sMatrixIdentity
    (𝒞η : TwistedModularCategory K)
    (second : 𝒞η.category.Simple) :
    (∑ first : 𝒞η.category.Simple,
      (simpleTwistScalar 𝒞η.toPremodular first)⁻¹ *
        𝒞η.category.quantumDimension first *
        sMatrixEntry 𝒞η.toPremodular first second) =
      𝒞η.category.quantumDimension second *
        simpleTwistScalar 𝒞η.toPremodular second *
        negativeGaussSum 𝒞η.toPremodular

/-- A genuine simple representative of the tensor power `g^n`.  It carries
only the object and its power isomorphism, never an `S`-matrix or twist-value
conclusion. -/
abbrev ModularCharacterPower
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) (n : ℤ) :=
  CharacterPowerRepresentative g.1 n

/-- Existence of the simple representative, with no numerical conclusions. -/
theorem egno_characterPower_exists
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) (n : ℤ) :
    Nonempty (ModularCharacterPower g n) :=
  egno_characterPowerRepresentative_exists g.1 n

/-- EGNO Theorem 7.21.12, together with
`|X|² = dim(X) dim(X*)` in the pivotal case: a simple object's pivotal
dimension is nonzero. -/
axiom egno_simpleQuantumDimension_ne_zero
    (𝒞η : TwistedPremodularCategory K)
    (simple : 𝒞η.category.Simple) :
    𝒞η.category.quantumDimension simple ≠ 0

/-- The positive shifted formula derived from EGNO (8.58). -/
theorem egno_positiveShiftedGaussSum
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) (n : ℤ) :
    positiveShiftedGaussSum 𝒞η.toPremodular n =
      (((g.twistUnit ^ (-(n * n)) : Kˣ) : K)) *
        positiveGaussSum 𝒞η.toPremodular := by
  let power := Classical.choice (egno_characterPower_exists g n)
  have identity := egno_positiveGaussSum_sMatrixIdentity
    𝒞η power.object.simple
  have expanded :
      𝒞η.category.quantumDimension power.object.simple *
          positiveShiftedGaussSum 𝒞η.toPremodular n =
        𝒞η.category.quantumDimension power.object.simple *
          (simpleTwistScalar 𝒞η.toPremodular power.object.simple)⁻¹ *
          positiveGaussSum 𝒞η.toPremodular := by
    rw [← identity]
    unfold positiveShiftedGaussSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [sMatrixEntry_characterPower_eq g.1 g.2 n power]
    dsimp [TwistedModularCategory.toPremodular]
    ring
  have inverseTwist :
      ((((g.1.twistUnit ^ (n * n) : Kˣ) : K)))⁻¹ =
        (((g.1.twistUnit ^ (-(n * n)) : Kˣ) : K)) := by
    rw [zpow_neg, Units.val_inv_eq_inv_val]
  have powerDimensionNonzero :
      𝒞η.category.quantumDimension power.object.simple ≠ 0 := by
    simpa [TwistedModularCategory.toPremodular] using
      egno_simpleQuantumDimension_ne_zero 𝒞η.toPremodular
        power.object.simple
  exact mul_left_cancel₀ powerDimensionNonzero (by
    rw [expanded, simpleTwistScalar_characterPower_eq g.1 n power,
      ModularCharacterObject.twistUnit, inverseTwist]
    ring)

/-- The negative shifted formula derived from EGNO (8.61). -/
theorem egno_negativeShiftedGaussSum
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) (n : ℤ) :
    negativeShiftedGaussSum 𝒞η.toPremodular n =
      (((g.twistUnit ^ (n * n) : Kˣ) : K)) *
        negativeGaussSum 𝒞η.toPremodular := by
  let power := Classical.choice (egno_characterPower_exists g n)
  have identity := egno_negativeGaussSum_sMatrixIdentity
    𝒞η power.object.simple
  have expanded :
      𝒞η.category.quantumDimension power.object.simple *
          negativeShiftedGaussSum 𝒞η.toPremodular n =
        𝒞η.category.quantumDimension power.object.simple *
          simpleTwistScalar 𝒞η.toPremodular power.object.simple *
          negativeGaussSum 𝒞η.toPremodular := by
    rw [← identity]
    unfold negativeShiftedGaussSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [sMatrixEntry_characterPower_eq g.1 g.2 n power]
    dsimp [TwistedModularCategory.toPremodular]
    ring
  have powerDimensionNonzero :
      𝒞η.category.quantumDimension power.object.simple ≠ 0 := by
    simpa [TwistedModularCategory.toPremodular] using
      egno_simpleQuantumDimension_ne_zero 𝒞η.toPremodular
        power.object.simple
  exact mul_left_cancel₀ powerDimensionNonzero (by
    rw [expanded, simpleTwistScalar_characterPower_eq g.1 n power,
      ModularCharacterObject.twistUnit]
    ring)

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
