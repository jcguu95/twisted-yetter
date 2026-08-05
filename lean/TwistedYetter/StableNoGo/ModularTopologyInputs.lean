import TwistedYetter.StableNoGo.FinalTheorem

/-!
# Topology inputs for the explicit modular formula

Mathlib does not currently provide the signature of the integral intersection
form of an abstract smooth four-manifold.  We therefore expose `b2Plus` and
`b2Minus` as foundational topology vocabulary and separately state the exact
standard results used by the proof.

The odd-diagonalization input combines:

* classification of indefinite odd unimodular integral forms; and
* Donaldson diagonalization for smooth definite forms.

No declaration in this file mentions a category or an evaluator.
-/

namespace TwistedYetter.StableNoGo

open TwistedYetter.Semantics.Independent

noncomputable section

/-- The positive index `b2Plus(X)` of the real intersection form. -/
axiom positiveSecondBettiNumber :
    ClosedOrientedSmoothFourManifold -> ℕ

/-- The negative index `b2Minus(X)` of the real intersection form. -/
axiom negativeSecondBettiNumber :
    ClosedOrientedSmoothFourManifold -> ℕ

/-- An odd integral diagonalization has exactly `b2Plus(X)` positive entries. -/
axiom OddDiagonalization.positiveRank_eq_b2Plus
    {X : ClosedOrientedSmoothFourManifold}
    (diagonalization : OddDiagonalization X) :
    diagonalization.positiveRank = positiveSecondBettiNumber X

/-- An odd integral diagonalization has exactly `b2Minus(X)` negative entries. -/
axiom OddDiagonalization.negativeRank_eq_b2Minus
    {X : ClosedOrientedSmoothFourManifold}
    (diagonalization : OddDiagonalization X) :
    diagonalization.negativeRank = negativeSecondBettiNumber X

/--
For simply connected smooth `X`, the odd form of `X # CP2` is integrally
diagonalizable.  This is the odd-unimodular classification in the indefinite
case and Donaldson's theorem in the definite case.
-/
axiom cp2Blowup_oddDiagonalization
    (X : ClosedOrientedSmoothFourManifold)
    (simplyConnectedX : IsSimplyConnected X) :
    Nonempty (OddDiagonalization (connectedSum X complexProjectivePlane))

/-- Positive index under one positive blow-up. -/
axiom positiveSecondBettiNumber_cp2Blowup
    (X : ClosedOrientedSmoothFourManifold) :
    positiveSecondBettiNumber (connectedSum X complexProjectivePlane) =
      positiveSecondBettiNumber X + 1

/-- Negative index under one positive blow-up. -/
axiom negativeSecondBettiNumber_cp2Blowup
    (X : ClosedOrientedSmoothFourManifold) :
    negativeSecondBettiNumber (connectedSum X complexProjectivePlane) =
      negativeSecondBettiNumber X

/-- The integral self-intersection `Q_X(alpha, alpha)`. -/
def selfIntersection
    (X : ClosedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) : ℤ :=
  integralIntersectionPairing X alpha alpha

@[simp]
theorem selfIntersection_cp2Blowup_zero
    (X : ClosedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) :
    selfIntersection (connectedSum X complexProjectivePlane)
        (connectedSumMarking alpha 0) =
      selfIntersection X alpha := by
  rw [selfIntersection, connectedSumH₂_preservesIntersectionPairing]
  simp [selfIntersection]

end

end TwistedYetter.StableNoGo
