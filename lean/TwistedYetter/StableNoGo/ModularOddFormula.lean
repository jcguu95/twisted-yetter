import TwistedYetter.StableNoGo.ModularCategoryInputs
import TwistedYetter.StableNoGo.ModularTopologyInputs

/-!
# Modular reduction of the odd-diagonal formula

This file is pure algebra after the two EGNO shifted-Gauss identities.  It
combines the character-object twist factors and identifies their exponent with
minus the integral self-intersection.
-/

namespace TwistedYetter.StableNoGo

open scoped BigOperators
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

theorem prod_coe_zpow_eq_coe_zpow_sum
    (u : Kˣ) {n : ℕ} (exponent : Fin n -> ℤ) :
    (∏ i, ((u ^ exponent i : Kˣ) : K)) =
      ((u ^ (∑ i, exponent i) : Kˣ) : K) := by
  have unitsEquality :
      (∏ i, u ^ exponent i) = u ^ (∑ i, exponent i) := by
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | @insert i indices fresh inductionHypothesis =>
        rw [Finset.sum_insert fresh, Finset.prod_insert fresh,
          inductionHypothesis, zpow_add]
  simpa using congrArg Units.val unitsEquality

theorem product_positiveShiftedGaussSum
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η)
    {p : ℕ} (coordinates : Fin p -> ℤ) :
    (∏ i, positiveShiftedGaussSum 𝒞η.toPremodular (coordinates i)) =
      (((g.twistUnit ^ (-(∑ i, coordinates i * coordinates i)) : Kˣ) : K)) *
        positiveGaussSum 𝒞η.toPremodular ^ p := by
  simp_rw [egno_positiveShiftedGaussSum g]
  rw [Finset.prod_mul_distrib]
  rw [prod_coe_zpow_eq_coe_zpow_sum]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  simp only [Finset.sum_neg_distrib]

theorem product_negativeShiftedGaussSum
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η)
    {q : ℕ} (coordinates : Fin q -> ℤ) :
    (∏ j, negativeShiftedGaussSum 𝒞η.toPremodular (coordinates j)) =
      (((g.twistUnit ^ (∑ j, coordinates j * coordinates j) : Kˣ) : K)) *
        negativeGaussSum 𝒞η.toPremodular ^ q := by
  simp_rw [egno_negativeShiftedGaussSum g]
  rw [Finset.prod_mul_distrib]
  rw [prod_coe_zpow_eq_coe_zpow_sum]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem oddFormula_eq_explicitModularFormula
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η)
    {X : ClosedOrientedSmoothFourManifold}
    (diagonalization : OddDiagonalization X)
    (alpha : ManifoldH₂ X) :
    oddFormula 𝒞η.toPremodular diagonalization alpha =
      𝒞η.category.globalDimension *
        positiveGaussSum 𝒞η.toPremodular ^ diagonalization.positiveRank *
        negativeGaussSum 𝒞η.toPremodular ^ diagonalization.negativeRank *
        (((g.twistUnit ^ (-selfIntersection X alpha) : Kˣ) : K)) := by
  let coordinates := diagonalization.coordinates alpha
  have exponentEquality :
      -(∑ i, coordinates.1 i * coordinates.1 i) +
          ∑ j, coordinates.2 j * coordinates.2 j =
        -selfIntersection X alpha := by
    rw [selfIntersection, ← diagonalization.preservesPairing alpha alpha]
    simp only [standardOddPairing]
    ring
  have combineTwists :
      (((g.twistUnit ^ (-(∑ i, coordinates.1 i * coordinates.1 i)) : Kˣ) : K)) *
          (((g.twistUnit ^ (∑ j, coordinates.2 j * coordinates.2 j) : Kˣ) : K)) =
        (((g.twistUnit ^ (-selfIntersection X alpha) : Kˣ) : K)) := by
    rw [← exponentEquality]
    simpa using congrArg Units.val
      (zpow_add g.twistUnit
        (-(∑ i, coordinates.1 i * coordinates.1 i))
        (∑ j, coordinates.2 j * coordinates.2 j)).symm
  unfold oddFormula
  change
    𝒞η.category.globalDimension *
        (∏ i, positiveShiftedGaussSum 𝒞η.toPremodular (coordinates.1 i)) *
        (∏ j, negativeShiftedGaussSum 𝒞η.toPremodular (coordinates.2 j)) = _
  rw [product_positiveShiftedGaussSum g,
    product_negativeShiftedGaussSum g]
  rw [← combineTwists]
  ring

theorem twistedYetter_eq_explicitModularFormula_of_oddDiagonalization
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η)
    {X : ClosedOrientedSmoothFourManifold}
    (simplyConnectedX : IsSimplyConnected X)
    (diagonalization : OddDiagonalization X)
    (alpha : ManifoldH₂ X) :
    TwistedYetter 𝒞η.toPremodular ⟨X, alpha⟩ =
      𝒞η.category.globalDimension *
        positiveGaussSum 𝒞η.toPremodular ^ positiveSecondBettiNumber X *
        negativeGaussSum 𝒞η.toPremodular ^ negativeSecondBettiNumber X *
        (((g.twistUnit ^ (-selfIntersection X alpha) : Kˣ) : K)) := by
  rw [satisfiesOddFormula 𝒞η.toPremodular X
    simplyConnectedX diagonalization alpha]
  rw [oddFormula_eq_explicitModularFormula g]
  rw [diagonalization.positiveRank_eq_b2Plus,
    diagonalization.negativeRank_eq_b2Minus]

end

end TwistedYetter.StableNoGo
