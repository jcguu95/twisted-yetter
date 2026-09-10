import TwistedYetter.Kirby.Final.TwistedYetter

/-!
# Stable cancellation for the Twisted Yetter invariant

This file is deliberately separate from the Kirby-calculus development.  It
formalizes only the last, purely algebraic, step of the stable no-go argument:
if the same nonzero stabilization factor occurs on both sides, and a marked
diffeomorphism identifies the stabilized pairs, then the original invariant
values agree.

Nothing here asserts that stabilization is connected sum with
`S^2 \times S^2`.  Nothing here asserts Wall's theorem, the Ruberman--Strle
realization theorem, or the connected-sum formula.  Those are distinct future
obligations and must not be hidden in this lemma.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
The exact stabilization formula needed by the final cancellation argument.

Later, `stabilize X n` is to be instantiated by
`X # n (S^2 \times S^2)`, and `stabilizedMarking X alpha n` by
`alpha \oplus 0`.  Keeping those meanings out of this definition prevents the
pure field calculation from masquerading as a connected-sum theorem.
-/
def MarkedStabilizationFormula
    (𝒞η : TwistedPremodularCategory K)
    (stabilize : ClosedConnectedOrientedSmoothFourManifold →
      Nat → ClosedConnectedOrientedSmoothFourManifold)
    (stabilizedMarking :
      ∀ (X : ClosedConnectedOrientedSmoothFourManifold),
        ManifoldH₂ X →
        ∀ n : Nat, ManifoldH₂ (stabilize X n))
    (lambda : K) : Prop :=
  ∀ (X : ClosedConnectedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) (n : Nat),
      TwistedYetter 𝒞η ⟨stabilize X n, stabilizedMarking X alpha n⟩ =
        lambda ^ n * TwistedYetter 𝒞η ⟨X, alpha⟩

/--
The exact marked consequence needed from stable four-manifold topology.

It asks for one common stabilization level and an orientation-preserving
diffeomorphism whose induced map sends the stabilized source marking to the
stabilized target marking.  It does not assert why such data exist.
-/
def MarkedStableRealization
    (stabilize : ClosedConnectedOrientedSmoothFourManifold →
      Nat → ClosedConnectedOrientedSmoothFourManifold)
    (stabilizedMarking :
      ∀ (X : ClosedConnectedOrientedSmoothFourManifold),
        ManifoldH₂ X →
        ∀ n : Nat, ManifoldH₂ (stabilize X n))
    {X Y : ClosedConnectedOrientedSmoothFourManifold}
    (alpha : ManifoldH₂ X) (beta : ManifoldH₂ Y) : Prop :=
  ∃ (n : Nat)
    (F : OrientedDiffeomorphism (stabilize X n) (stabilize Y n)),
      inducedH₂ F (stabilizedMarking X alpha n) =
        stabilizedMarking Y beta n

/--
Pure cancellation step in the stable no-go proof.

The proof uses only the already established diffeomorphism invariance of
`TwistedYetter`, the displayed stabilization formula, marked stable
realization, and cancellation by the nonzero scalar `lambda ^ n`.
-/
theorem twistedYetter_eq_of_stable_realization
    (𝒞η : TwistedPremodularCategory K)
    (stabilize : ClosedConnectedOrientedSmoothFourManifold →
      Nat → ClosedConnectedOrientedSmoothFourManifold)
    (stabilizedMarking :
      ∀ (X : ClosedConnectedOrientedSmoothFourManifold),
        ManifoldH₂ X →
        ∀ n : Nat, ManifoldH₂ (stabilize X n))
    (lambda : K)
    (lambda_ne_zero : lambda ≠ 0)
    (stabilizationFormula :
      MarkedStabilizationFormula 𝒞η stabilize stabilizedMarking lambda)
    {X Y : ClosedConnectedOrientedSmoothFourManifold}
    (alpha : ManifoldH₂ X) (beta : ManifoldH₂ Y)
    (stableRealization :
      MarkedStableRealization stabilize stabilizedMarking alpha beta) :
    TwistedYetter 𝒞η ⟨X, alpha⟩ =
      TwistedYetter 𝒞η ⟨Y, beta⟩ := by
  obtain ⟨n, F, markingTransport⟩ := stableRealization
  have stabilizedEquality :=
    TwistedYetter_diffeomorphism_invariant
      𝒞η F (stabilizedMarking X alpha n)
  rw [markingTransport] at stabilizedEquality
  rw [stabilizationFormula X alpha n,
    stabilizationFormula Y beta n] at stabilizedEquality
  exact mul_left_cancel₀ (pow_ne_zero n lambda_ne_zero) stabilizedEquality

end

end TwistedYetter.StableNoGo
