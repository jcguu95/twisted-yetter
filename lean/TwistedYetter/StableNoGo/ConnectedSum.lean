import TwistedYetter.StableNoGo.Statement

/-!
# Connected-sum vocabulary and iterated stabilization

This module introduces only the manifold-level connected-sum vocabulary needed
to state the prose proof.  The marked connected-sum formula remains a named
project obligation.  From that one-step formula, Lean proves the formula for
arbitrarily many `S^2 \times S^2` stabilizations by induction.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-! ## Category-neutral manifold vocabulary -/

/-- Oriented connected sum of closed oriented smooth four-manifolds. -/
axiom connectedSum :
  ClosedConnectedOrientedSmoothFourManifold →
  ClosedConnectedOrientedSmoothFourManifold →
  ClosedConnectedOrientedSmoothFourManifold

/-- The closed oriented smooth four-manifold `S^2 \times S^2`. -/
axiom sphereTwoProduct : ClosedConnectedOrientedSmoothFourManifold

/--
The canonical Mayer--Vietoris identification
`H₂(X # Y; ℤ) ≃ H₂(X; ℤ) ⊕ H₂(Y; ℤ)`.
-/
axiom connectedSumH₂
    (X Y : ClosedConnectedOrientedSmoothFourManifold) :
    ManifoldH₂ (connectedSum X Y) ≃+
      ManifoldH₂ X × ManifoldH₂ Y

/-- The class `alpha \oplus beta` in the connected sum. -/
def connectedSumMarking
    {X Y : ClosedConnectedOrientedSmoothFourManifold}
    (alpha : ManifoldH₂ X) (beta : ManifoldH₂ Y) :
    ManifoldH₂ (connectedSum X Y) :=
  (connectedSumH₂ X Y).symm (alpha, beta)

/-- Iterated stabilization by `S^2 \times S^2`, with fixed parenthesization. -/
def stabilize :
    ClosedConnectedOrientedSmoothFourManifold →
    Nat → ClosedConnectedOrientedSmoothFourManifold
  | X, 0 => X
  | X, n + 1 => connectedSum (stabilize X n) sphereTwoProduct

/-- The marking `alpha \oplus 0` under every stabilization. -/
def stabilizedMarking
    (X : ClosedConnectedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) :
    ∀ n : Nat, ManifoldH₂ (stabilize X n)
  | 0 => alpha
  | n + 1 => connectedSumMarking (stabilizedMarking X alpha n) 0

/-! ## Evaluator obligation and its formal consequence -/

/--
The exact marked connected-sum formula from the prose proof.

This is a transparent proposition, not an axiom.  Its future proof must come
from split special Kirby presentations, direct-sum marking naturality, raw
evaluator multiplicativity, and the THAM normalization.
-/
def MarkedConnectedSumFormula
    (𝒞η : TwistedPremodularCategory K)
    (globalDimension : K) : Prop :=
  ∀ (X Y : ClosedConnectedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) (beta : ManifoldH₂ Y),
    TwistedYetter 𝒞η
        ⟨connectedSum X Y, connectedSumMarking alpha beta⟩ =
      globalDimension⁻¹ *
        TwistedYetter 𝒞η ⟨X, alpha⟩ *
        TwistedYetter 𝒞η ⟨Y, beta⟩

/-- The multiplier contributed by one `S^2 \times S^2` stabilization. -/
def stabilizationMultiplier
    (𝒞η : TwistedPremodularCategory K)
    (globalDimension : K) : K :=
  globalDimension⁻¹ *
    TwistedYetter 𝒞η ⟨sphereTwoProduct, 0⟩

/--
The one-step marked connected-sum formula implies the formula for every finite
number of `S^2 \times S^2` stabilizations.
-/
theorem markedStabilizationFormula_of_connectedSum
    (𝒞η : TwistedPremodularCategory K)
    (globalDimension : K)
    (connectedSumFormula :
      MarkedConnectedSumFormula 𝒞η globalDimension) :
    MarkedStabilizationFormula
      𝒞η stabilize stabilizedMarking
      (stabilizationMultiplier 𝒞η globalDimension) := by
  intro X alpha n
  induction n with
  | zero =>
      simp [stabilize, stabilizedMarking]
  | succ n inductionHypothesis =>
      change
        TwistedYetter 𝒞η
            ⟨connectedSum (stabilize X n) sphereTwoProduct,
              connectedSumMarking (stabilizedMarking X alpha n) 0⟩ =
          stabilizationMultiplier 𝒞η globalDimension ^ (n + 1) *
            TwistedYetter 𝒞η ⟨X, alpha⟩
      rw [connectedSumFormula, inductionHypothesis]
      simp only [stabilizationMultiplier, pow_succ]
      ring

end

end TwistedYetter.StableNoGo
