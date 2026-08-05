import TwistedYetter.StableNoGo.FinalTheorem

/-!
# Topology inputs for the explicit modular formula

Mathlib does not currently provide the signature of the integral intersection
form of an abstract smooth four-manifold.  We therefore expose `b2Plus` and
`b2Minus` as foundational topology vocabulary and separately state the exact
standard results used by the proof.

The odd-diagonalization argument deliberately keeps two standard results
separate:

* Donaldson diagonalization for smooth definite forms; and
* classification of indefinite odd unimodular integral forms.

The diagonalization of `X # CP2` is proved below from these two inputs.  It is
not itself an entrance axiom.

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

/-- The real intersection form is definite exactly when one of its two indices vanishes. -/
def HasDefiniteIntersectionForm
    (X : ClosedOrientedSmoothFourManifold) : Prop :=
  positiveSecondBettiNumber X = 0 ∨
    negativeSecondBettiNumber X = 0

/-- The real intersection form is indefinite exactly when both indices are nonzero. -/
def HasIndefiniteIntersectionForm
    (X : ClosedOrientedSmoothFourManifold) : Prop :=
  positiveSecondBettiNumber X ≠ 0 ∧
    negativeSecondBettiNumber X ≠ 0

/-- A symmetric integral form is odd when some vector has odd square. -/
def HasOddIntersectionForm
    (X : ClosedOrientedSmoothFourManifold) : Prop :=
  ∃ alpha : ManifoldH₂ X,
    Odd (integralIntersectionPairing X alpha alpha)

/-- The definite/indefinite dichotomy, expressed through the two indices. -/
theorem not_definite_iff_indefinite
    (X : ClosedOrientedSmoothFourManifold) :
    ¬ HasDefiniteIntersectionForm X ↔
      HasIndefiniteIntersectionForm X := by
  simp [HasDefiniteIntersectionForm, HasIndefiniteIntersectionForm]

/--
Donaldson's diagonalization theorem in precisely the form used here: the
integral intersection form of a closed, simply connected, smooth four-manifold
with definite real extension is integrally diagonalizable over `Z` with all
diagonal entries equal to `+1` or all equal to `-1`.

Reference: S. K. Donaldson, *An application of gauge theory to
four-dimensional topology*, JDG 18 (1983), Theorem A.  The opposite-definite
case is the same statement after reversing the orientation of the manifold.
-/
axiom donaldson_definiteIntersectionForm_diagonalization
    (X : ClosedOrientedSmoothFourManifold)
    (simplyConnectedX : IsSimplyConnected X)
    (definite : HasDefiniteIntersectionForm X) :
    Nonempty (OddDiagonalization X)

/--
The odd indefinite unimodular classification, specialized to the integral
intersection lattice of a closed simply connected four-manifold.  Poincare
duality makes that lattice finite free and unimodular; an odd indefinite
unimodular integral symmetric form is integrally isometric to
`b2Plus * <1> + b2Minus * <-1>`.

This is the classical arithmetic classification of indefinite unimodular
integral symmetric bilinear forms; unlike the preceding axiom it uses no
smooth structure.  See C. Peters, *Symmetric and Quadratic Forms*, Theorem
2.3.1: every odd indefinite unimodular lattice is an orthogonal sum of copies
of `<1>` and `<-1>`.
-/
axiom oddIndefiniteUnimodularForm_diagonalization
    (X : ClosedOrientedSmoothFourManifold)
    (simplyConnectedX : IsSimplyConnected X)
    (odd : HasOddIntersectionForm X)
    (indefinite : HasIndefiniteIntersectionForm X) :
    Nonempty (OddDiagonalization X)

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

/-- A positive blow-up has an odd intersection form, witnessed by the `CP2` generator. -/
theorem cp2Blowup_hasOddIntersectionForm
    (X : ClosedOrientedSmoothFourManifold) :
    HasOddIntersectionForm
      (connectedSum X complexProjectivePlane) := by
  refine ⟨connectedSumMarking 0 positiveProjectivePlaneGenerator, ?_⟩
  rw [connectedSumH₂_preservesIntersectionPairing,
    complexProjectivePlane_intersectionForm]
  simp [positiveProjectivePlaneGenerator]

/--
For simply connected smooth `X`, the form of `X # CP2` is integrally
diagonalizable.  The proof separates the definite Donaldson branch from the
indefinite odd-unimodular arithmetic branch.
-/
theorem cp2Blowup_oddDiagonalization
    (X : ClosedOrientedSmoothFourManifold)
    (simplyConnectedX : IsSimplyConnected X) :
    Nonempty (OddDiagonalization
      (connectedSum X complexProjectivePlane)) := by
  let blowup := connectedSum X complexProjectivePlane
  have simplyConnectedBlowup : IsSimplyConnected blowup :=
    connectedSum_simplyConnected simplyConnectedX
      complexProjectivePlane_simplyConnected
  by_cases definite : HasDefiniteIntersectionForm blowup
  · exact donaldson_definiteIntersectionForm_diagonalization
      blowup simplyConnectedBlowup definite
  · exact oddIndefiniteUnimodularForm_diagonalization
      blowup simplyConnectedBlowup
      (cp2Blowup_hasOddIntersectionForm X)
      ((not_definite_iff_indefinite blowup).mp definite)

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
