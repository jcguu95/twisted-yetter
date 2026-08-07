import TwistedYetter.StableNoGo.ModularOddFormula

/-!
# Explicit modular formula

The proof follows the reviewed prose argument: apply the odd formula to
`X # CP2`, identify the connected-sum value, and cancel the nonzero positive
Gauss sum.
-/

namespace TwistedYetter.StableNoGo

open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- The EGNO character object, chosen noncomputably from its existence theorem. -/
noncomputable def characterObject (𝒞η : TwistedModularCategory K) :
    ModularCharacterObject 𝒞η :=
  Classical.choice (egno_characterObject_exists 𝒞η)

/-- The twist `theta_(g_eta)` of the object representing the character. -/
noncomputable def characterTwist (𝒞η : TwistedModularCategory K) : Kˣ :=
  (characterObject 𝒞η).twistUnit

/-- The exact value of the zero-marked positive projective-plane block. -/
theorem twistedYetter_complexProjectivePlane_zero
    (𝒞η : TwistedModularCategory K) :
    TwistedYetter 𝒞η.toPremodular ⟨complexProjectivePlane, 0⟩ =
      𝒞η.category.globalDimension *
        positiveGaussSum 𝒞η.toPremodular := by
  simpa [positiveGaussSum] using
    twistedYetter_complexProjectivePlane 𝒞η.toPremodular 0

/--
**Explicit modular marked formula.**

For a closed simply connected oriented smooth four-manifold,

`TY(X, alpha) = D * tauPlus^b2Plus * tauMinus^b2Minus * theta_g^(-alpha^2)`.
-/
theorem TwistedYetter_modular_explicit_formula
    (𝒞η : TwistedModularCategory K)
    {X : ClosedOrientedSmoothFourManifold}
    (simplyConnectedX : IsSimplyConnected X)
    (alpha : ManifoldH₂ X) :
    TwistedYetter 𝒞η.toPremodular ⟨X, alpha⟩ =
      𝒞η.category.globalDimension *
        positiveGaussSum 𝒞η.toPremodular ^ positiveSecondBettiNumber X *
        negativeGaussSum 𝒞η.toPremodular ^ negativeSecondBettiNumber X *
        ((((characterTwist 𝒞η) ^ (-selfIntersection X alpha) : Kˣ) : K)) := by
  let blowup : ClosedOrientedSmoothFourManifold :=
    connectedSum X complexProjectivePlane
  let blowupAlpha : ManifoldH₂ blowup :=
    connectedSumMarking alpha (0 : ManifoldH₂ complexProjectivePlane)
  let diagonalization := Classical.choice
    (cp2Blowup_oddDiagonalization X simplyConnectedX)
  have simplyConnectedBlowup : IsSimplyConnected blowup :=
    connectedSum_simplyConnected simplyConnectedX
      complexProjectivePlane_simplyConnected
  have oddValue :=
    twistedYetter_eq_explicitModularFormula_of_oddDiagonalization
      (g := characterObject 𝒞η)
      simplyConnectedBlowup diagonalization blowupAlpha
  have connectedSumValue :
      TwistedYetter 𝒞η.toPremodular ⟨blowup, blowupAlpha⟩ =
        TwistedYetter 𝒞η.toPremodular ⟨X, alpha⟩ *
          positiveGaussSum 𝒞η.toPremodular := by
    change
      TwistedYetter 𝒞η.toPremodular
          ⟨connectedSum X complexProjectivePlane,
            connectedSumMarking alpha 0⟩ = _
    rw [markedConnectedSumFormula 𝒞η.toPremodular,
      twistedYetter_complexProjectivePlane_zero]
    calc
      𝒞η.category.globalDimension⁻¹ *
            TwistedYetter 𝒞η.toPremodular ⟨X, alpha⟩ *
            (𝒞η.category.globalDimension *
              positiveGaussSum 𝒞η.toPremodular) =
          (𝒞η.category.globalDimension⁻¹ *
              𝒞η.category.globalDimension) *
            (TwistedYetter 𝒞η.toPremodular ⟨X, alpha⟩ *
              positiveGaussSum 𝒞η.toPremodular) := by ring
      _ = _ := by
        rw [inv_mul_cancel₀ (eno_globalDimension_ne_zero 𝒞η.category),
          one_mul]
  apply mul_right_cancel₀ (positiveGaussSum_ne_zero 𝒞η)
  rw [← connectedSumValue, oddValue]
  change
    𝒞η.category.globalDimension *
          positiveGaussSum 𝒞η.toPremodular ^
            positiveSecondBettiNumber blowup *
          negativeGaussSum 𝒞η.toPremodular ^
            negativeSecondBettiNumber blowup *
          ((((characterTwist 𝒞η) ^
            (-selfIntersection blowup blowupAlpha) : Kˣ) : K)) = _
  rw [positiveSecondBettiNumber_cp2Blowup,
    negativeSecondBettiNumber_cp2Blowup,
    selfIntersection_cp2Blowup_zero]
  rw [pow_succ]
  ring

/-- The zero-marked modular baseline. -/
theorem TwistedYetter_modular_zero_formula
    (𝒞η : TwistedModularCategory K)
    {X : ClosedOrientedSmoothFourManifold}
    (simplyConnectedX : IsSimplyConnected X) :
    TwistedYetter 𝒞η.toPremodular ⟨X, 0⟩ =
      𝒞η.category.globalDimension *
        positiveGaussSum 𝒞η.toPremodular ^ positiveSecondBettiNumber X *
        negativeGaussSum 𝒞η.toPremodular ^ negativeSecondBettiNumber X := by
  simpa [selfIntersection] using
    TwistedYetter_modular_explicit_formula 𝒞η simplyConnectedX (0 : ManifoldH₂ X)

/-- The quadratic correction relative to the zero-marked value. -/
theorem TwistedYetter_modular_quadratic_ratio
    (𝒞η : TwistedModularCategory K)
    {X : ClosedOrientedSmoothFourManifold}
    (simplyConnectedX : IsSimplyConnected X)
    (alpha : ManifoldH₂ X) :
    TwistedYetter 𝒞η.toPremodular ⟨X, alpha⟩ =
      TwistedYetter 𝒞η.toPremodular ⟨X, 0⟩ *
        ((((characterTwist 𝒞η) ^ (-selfIntersection X alpha) : Kˣ) : K)) := by
  rw [TwistedYetter_modular_explicit_formula 𝒞η simplyConnectedX alpha,
    TwistedYetter_modular_zero_formula 𝒞η simplyConnectedX]

end

end TwistedYetter.StableNoGo
