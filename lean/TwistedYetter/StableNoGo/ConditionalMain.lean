import TwistedYetter.StableNoGo.Statement

/-!
# Conditional assembly of the stable no-go theorem

This file records exactly how the human theorem follows once two substantial
mathematical obligations have been discharged:

1. the marked stabilization formula for `TwistedYetter`;
2. marked stable realization of every integral intersection-form isometry.

Both obligations are explicit arguments.  This theorem is therefore an
internal assembly result, not the completed stable no-go theorem.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
Conditional assembly of marked intersection-form invariance.

The intended future instantiation is:

* `stabilize X n = X # n (S^2 \times S^2)`;
* `stabilizedMarking X alpha n = alpha \oplus 0`;
* `lambda` is the premodular stabilization multiplier.
-/
theorem premodularMarkedIntersectionFormInvariance_of_stable_inputs
    (𝒞η : TwistedPremodularCategory K)
    (stabilize : ClosedOrientedSmoothFourManifold →
      Nat → ClosedOrientedSmoothFourManifold)
    (stabilizedMarking :
      ∀ (X : ClosedOrientedSmoothFourManifold),
        ManifoldH₂ X →
        ∀ n : Nat, ManifoldH₂ (stabilize X n))
    (lambda : K)
    (lambda_ne_zero : lambda ≠ 0)
    (stabilizationFormula :
      MarkedStabilizationFormula 𝒞η stabilize stabilizedMarking lambda)
    (markedStableRealization :
      ∀ (X Y : ClosedOrientedSmoothFourManifold),
        IsSimplyConnected X →
        IsSimplyConnected Y →
        ∀ (f : IntegralIntersectionFormIsometry X Y)
          (alpha : ManifoldH₂ X),
          MarkedStableRealization
            stabilize stabilizedMarking alpha (f alpha)) :
    PremodularMarkedIntersectionFormInvariance 𝒞η := by
  intro X Y simplyConnectedX simplyConnectedY f alpha
  exact twistedYetter_eq_of_stable_realization
    𝒞η stabilize stabilizedMarking lambda lambda_ne_zero
    stabilizationFormula alpha (f alpha)
    (markedStableRealization
      X Y simplyConnectedX simplyConnectedY f alpha)

end

end TwistedYetter.StableNoGo
