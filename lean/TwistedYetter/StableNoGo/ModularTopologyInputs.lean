import TwistedYetter.StableNoGo.NumericalStatement

/-!
# Topology inputs for the simply-connected numerical formulas

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

/-- A symmetric integral form is even when every vector has even square. -/
def HasEvenIntersectionForm
    (X : ClosedOrientedSmoothFourManifold) : Prop :=
  ∀ alpha : ManifoldH₂ X,
    Even (integralIntersectionPairing X alpha alpha)

/-- Every integral intersection form is either odd or even, in the literal
parity sense fixed by the two preceding definitions. -/
theorem odd_or_even_intersectionForm
    (X : ClosedOrientedSmoothFourManifold) :
    HasOddIntersectionForm X ∨ HasEvenIntersectionForm X := by
  by_cases odd : HasOddIntersectionForm X
  · exact Or.inl odd
  · right
    intro alpha
    rw [← Int.not_odd_iff_even]
    intro alphaOdd
    exact odd ⟨alpha, alphaOdd⟩

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

/-- Every odd simply-connected smooth intersection form admits the standard
integral diagonalization: Donaldson handles the definite branch and the
arithmetic classification of odd unimodular lattices handles the indefinite
branch. -/
theorem oddIntersectionForm_diagonalization
    (X : ClosedOrientedSmoothFourManifold)
    (simplyConnectedX : IsSimplyConnected X)
    (odd : HasOddIntersectionForm X) :
    Nonempty (OddDiagonalization X) := by
  by_cases definite : HasDefiniteIntersectionForm X
  · exact donaldson_definiteIntersectionForm_diagonalization
      X simplyConnectedX definite
  · exact oddIndefiniteUnimodularForm_diagonalization
      X simplyConnectedX odd ((not_definite_iff_indefinite X).mp definite)

/-! ## Stable even `K3/H` models -/

/-- Split a marking on a connected sum of standard blocks into one marking per
block by the fixed Mayer--Vietoris equivalences.  This is a noncomputable
choice of coordinates derived from existing homology data, not a topology
axiom. -/
noncomputable def splitK3HBlockMarkings :
    (blocks : List K3HBlock) →
      ManifoldH₂ (connectedSumK3HBlocks blocks) → K3HBlockMarkings blocks
  | [], _ => PUnit.unit
  | block :: blocks, alpha =>
      let parts :=
        connectedSumH₂ block.manifold (connectedSumK3HBlocks blocks) alpha
      (parts.1, splitK3HBlockMarkings blocks parts.2)

/-- Reassembling the recursively split block markings recovers the original
homology class exactly. -/
theorem connectedSumK3HMarking_splitK3HBlockMarkings
    (blocks : List K3HBlock)
    (alpha : ManifoldH₂ (connectedSumK3HBlocks blocks)) :
    connectedSumK3HMarking blocks (splitK3HBlockMarkings blocks alpha) =
      alpha := by
  induction blocks with
  | nil =>
      exact (fourSphere_H₂_eq_zero alpha).symm
  | cons block blocks inductionHypothesis =>
      let parts :=
        connectedSumH₂ block.manifold (connectedSumK3HBlocks blocks) alpha
      change
        connectedSumMarking parts.1
            (connectedSumK3HMarking blocks
              (splitK3HBlockMarkings blocks parts.2)) = alpha
      rw [inductionHypothesis parts.2]
      exact
        (connectedSumH₂ block.manifold
          (connectedSumK3HBlocks blocks)).symm_apply_apply alpha

/--
Stable `K3/\bar K3/H` form of the even-unimodular classification used in
Reutter's proof of Corollary 3.9: a closed simply connected smooth
four-manifold with even intersection form becomes integrally
intersection-form isometric, after finitely many hyperbolic stabilizations,
to a finite connected sum of `K3`, orientation-reversed `K3`, and
`S² × S²` blocks.

This is an unmarked, category-neutral lattice/topology input.  It does not
assert a diffeomorphism or any equality of invariants.  Stable realization of
the resulting isometry is supplied separately by Wall and Ruberman--Strle.

Reference: D. Reutter, *Semisimple 4-dimensional topological field theories
cannot detect exotic smooth structure*, Corollary 3.9 and its proof, arXiv
PDF pp. 14--15, using the classification of even unimodular forms and
Rokhlin's theorem.

No form of the `11/8` conjecture is used here: the source is allowed an
arbitrary finite number of hyperbolic stabilizations.  Reutter notes that
forcing this source stabilization count to be zero is the stronger statement
equivalent to `11/8`.
-/
axiom evenIntersectionForm_stableK3H_isometry
    (X : ClosedOrientedSmoothFourManifold)
    (simplyConnectedX : IsSimplyConnected X)
    (even : HasEvenIntersectionForm X) :
    Σ stabilizationCount : ℕ, Σ blocks : List K3HBlock,
      IntegralIntersectionFormIsometry
        (stabilize X stabilizationCount) (connectedSumK3HBlocks blocks)

/-- The marked stable decomposition is derived from the preceding unmarked
isometry by transporting `alpha` and splitting its image across the standard
blocks.  No marked-realization axiom is added. -/
theorem evenStableK3HDecomposition_exists
    (X : ClosedOrientedSmoothFourManifold)
    (simplyConnectedX : IsSimplyConnected X)
    (even : HasEvenIntersectionForm X)
    (alpha : ManifoldH₂ X) :
    Nonempty (EvenStableK3HDecomposition X alpha) := by
  obtain ⟨stabilizationCount, blocks, isometry⟩ :=
    evenIntersectionForm_stableK3H_isometry X simplyConnectedX even
  let targetMarking :=
    isometry (stabilizedMarking X alpha stabilizationCount)
  let markings := splitK3HBlockMarkings blocks targetMarking
  refine ⟨
    { stabilizationCount := stabilizationCount
      blocks := blocks
      markings := markings
      isometry := isometry
      markingTransport := ?_ }⟩
  exact
    (connectedSumK3HMarking_splitK3HBlockMarkings
      blocks targetMarking).symm

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
