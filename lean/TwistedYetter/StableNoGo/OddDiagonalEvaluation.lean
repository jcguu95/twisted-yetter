import TwistedYetter.StableNoGo.NumericalStatement
import TwistedYetter.StableNoGo.ProjectivePlaneEvaluation

/-!
# Odd diagonal standard models

This file derives the standard odd connected-sum model from the already
approved rank-one manifolds and Mayer--Vietoris data.  It introduces no new
topology or category axiom.
-/

namespace TwistedYetter.StableNoGo

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- Split one leading integral coordinate from a finite coordinate vector. -/
def prependIntegerCoordinate (n : ℕ) :
    ℤ × (Fin n → ℤ) ≃+ (Fin (n + 1) → ℤ) where
  toFun pair := Fin.cases pair.1 pair.2
  invFun coordinates :=
    (coordinates 0, fun index => coordinates index.succ)
  left_inv pair := by
    rcases pair with ⟨head, tail⟩
    apply Prod.ext
    · rfl
    · funext index
      rfl
  right_inv coordinates := by
    funext index
    refine Fin.cases ?_ (fun tail => ?_) index
    · rfl
    · rfl
  map_add' left right := by
    funext index
    refine Fin.cases ?_ (fun tail => ?_) index
    · rfl
    · rfl

/-- The unique coordinate system on the zero group `H₂(S⁴)`. -/
def fourSphereCoordinates : ManifoldH₂ fourSphere ≃+ (Fin 0 → ℤ) where
  toFun _ index := Fin.elim0 index
  invFun _ := 0
  left_inv alpha := (fourSphere_H₂_eq_zero alpha).symm
  right_inv coordinates := by
    funext index
    exact Fin.elim0 index
  map_add' _ _ := by
    funext index
    exact Fin.elim0 index

/-- `p` positive rank-one blocks, with `S⁴` as the rank-zero base. -/
def positiveDiagonalManifold : ℕ → ClosedConnectedOrientedSmoothFourManifold
  | 0 => fourSphere
  | p + 1 => connectedSum complexProjectivePlane (positiveDiagonalManifold p)

/-- Canonical integral coordinates on the positive standard model. -/
def positiveDiagonalCoordinates :
    (p : ℕ) → ManifoldH₂ (positiveDiagonalManifold p) ≃+ (Fin p → ℤ)
  | 0 => fourSphereCoordinates
  | p + 1 =>
      (connectedSumH₂ complexProjectivePlane (positiveDiagonalManifold p)).trans
        ((complexProjectivePlaneH₂.prodCongr
          (positiveDiagonalCoordinates p)).trans
            (prependIntegerCoordinate p))

@[simp] theorem positiveDiagonalCoordinates_connectedSumMarking
    (p : ℕ) (a : ManifoldH₂ complexProjectivePlane)
    (b : ManifoldH₂ (positiveDiagonalManifold p)) :
    positiveDiagonalCoordinates (p + 1) (connectedSumMarking a b) =
      prependIntegerCoordinate p
        (complexProjectivePlaneH₂ a, positiveDiagonalCoordinates p b) := by
  change
    ((connectedSumH₂ complexProjectivePlane (positiveDiagonalManifold p)).trans
        ((complexProjectivePlaneH₂.prodCongr
          (positiveDiagonalCoordinates p)).trans (prependIntegerCoordinate p)))
      ((connectedSumH₂ complexProjectivePlane
        (positiveDiagonalManifold p)).symm (a, b)) = _
  rw [AddEquiv.trans_apply,
    (connectedSumH₂ complexProjectivePlane
      (positiveDiagonalManifold p)).apply_symm_apply,
    AddEquiv.trans_apply]
  change
    prependIntegerCoordinate p
        ((complexProjectivePlaneH₂.prodCongr (positiveDiagonalCoordinates p))
          (a, b)) = _
  change
    prependIntegerCoordinate p
      ((complexProjectivePlaneH₂.toEquiv.prodCongr
        (positiveDiagonalCoordinates p).toEquiv) (a, b)) = _
  rw [Equiv.prodCongr_apply]
  rw [Prod.map_apply']
  rfl

/-- `q` negative rank-one blocks, with `S⁴` as the rank-zero base. -/
def negativeDiagonalManifold : ℕ → ClosedConnectedOrientedSmoothFourManifold
  | 0 => fourSphere
  | q + 1 =>
      connectedSum reversedComplexProjectivePlane (negativeDiagonalManifold q)

/-- Canonical integral coordinates on the negative standard model. -/
def negativeDiagonalCoordinates :
    (q : ℕ) → ManifoldH₂ (negativeDiagonalManifold q) ≃+ (Fin q → ℤ)
  | 0 => fourSphereCoordinates
  | q + 1 =>
      (connectedSumH₂ reversedComplexProjectivePlane
        (negativeDiagonalManifold q)).trans
        ((reversedComplexProjectivePlaneH₂.prodCongr
          (negativeDiagonalCoordinates q)).trans
            (prependIntegerCoordinate q))

@[simp] theorem negativeDiagonalCoordinates_connectedSumMarking
    (q : ℕ) (a : ManifoldH₂ reversedComplexProjectivePlane)
    (b : ManifoldH₂ (negativeDiagonalManifold q)) :
    negativeDiagonalCoordinates (q + 1) (connectedSumMarking a b) =
      prependIntegerCoordinate q
        (reversedComplexProjectivePlaneH₂ a, negativeDiagonalCoordinates q b) := by
  change
    ((connectedSumH₂ reversedComplexProjectivePlane (negativeDiagonalManifold q)).trans
        ((reversedComplexProjectivePlaneH₂.prodCongr
          (negativeDiagonalCoordinates q)).trans (prependIntegerCoordinate q)))
      ((connectedSumH₂ reversedComplexProjectivePlane
        (negativeDiagonalManifold q)).symm (a, b)) = _
  rw [AddEquiv.trans_apply,
    (connectedSumH₂ reversedComplexProjectivePlane
      (negativeDiagonalManifold q)).apply_symm_apply,
    AddEquiv.trans_apply]
  change
    prependIntegerCoordinate q
      ((reversedComplexProjectivePlaneH₂.toEquiv.prodCongr
        (negativeDiagonalCoordinates q).toEquiv) (a, b)) = _
  rw [Equiv.prodCongr_apply]
  rw [Prod.map_apply']
  rfl

theorem positiveDiagonal_pairing
    (p : ℕ) (alpha beta : ManifoldH₂ (positiveDiagonalManifold p)) :
    integralIntersectionPairing (positiveDiagonalManifold p) alpha beta =
      ∑ i, positiveDiagonalCoordinates p alpha i *
        positiveDiagonalCoordinates p beta i := by
  induction p with
  | zero =>
      change integralIntersectionPairing fourSphere alpha beta = 0
      exact fourSphere_intersectionForm_eq_zero alpha beta
  | succ p inductionHypothesis =>
      let alphaParts :=
        connectedSumH₂ complexProjectivePlane (positiveDiagonalManifold p) alpha
      let betaParts :=
        connectedSumH₂ complexProjectivePlane (positiveDiagonalManifold p) beta
      have alphaSplit :
          alpha = connectedSumMarking alphaParts.1 alphaParts.2 := by
        exact (connectedSumH₂ complexProjectivePlane
          (positiveDiagonalManifold p)).symm_apply_apply alpha |>.symm
      have betaSplit :
          beta = connectedSumMarking betaParts.1 betaParts.2 := by
        exact (connectedSumH₂ complexProjectivePlane
          (positiveDiagonalManifold p)).symm_apply_apply beta |>.symm
      rw [alphaSplit, betaSplit]
      change
        integralIntersectionPairing
            (connectedSum complexProjectivePlane (positiveDiagonalManifold p))
            (connectedSumMarking alphaParts.1 alphaParts.2)
            (connectedSumMarking betaParts.1 betaParts.2) = _
      rw [connectedSumH₂_preservesIntersectionPairing,
        complexProjectivePlane_intersectionForm,
        inductionHypothesis]
      rw [Fin.sum_univ_succ]
      simp [positiveDiagonalCoordinates_connectedSumMarking,
        prependIntegerCoordinate]

theorem negativeDiagonal_pairing
    (q : ℕ) (alpha beta : ManifoldH₂ (negativeDiagonalManifold q)) :
    integralIntersectionPairing (negativeDiagonalManifold q) alpha beta =
      -(∑ i, negativeDiagonalCoordinates q alpha i *
        negativeDiagonalCoordinates q beta i) := by
  induction q with
  | zero =>
      change integralIntersectionPairing fourSphere alpha beta = 0
      exact fourSphere_intersectionForm_eq_zero alpha beta
  | succ q inductionHypothesis =>
      let alphaParts := connectedSumH₂ reversedComplexProjectivePlane
        (negativeDiagonalManifold q) alpha
      let betaParts := connectedSumH₂ reversedComplexProjectivePlane
        (negativeDiagonalManifold q) beta
      have alphaSplit :
          alpha = connectedSumMarking alphaParts.1 alphaParts.2 := by
        exact (connectedSumH₂ reversedComplexProjectivePlane
          (negativeDiagonalManifold q)).symm_apply_apply alpha |>.symm
      have betaSplit :
          beta = connectedSumMarking betaParts.1 betaParts.2 := by
        exact (connectedSumH₂ reversedComplexProjectivePlane
          (negativeDiagonalManifold q)).symm_apply_apply beta |>.symm
      rw [alphaSplit, betaSplit]
      change
        integralIntersectionPairing
            (connectedSum reversedComplexProjectivePlane (negativeDiagonalManifold q))
            (connectedSumMarking alphaParts.1 alphaParts.2)
            (connectedSumMarking betaParts.1 betaParts.2) = _
      rw [connectedSumH₂_preservesIntersectionPairing,
        reversedComplexProjectivePlane_intersectionForm,
        inductionHypothesis]
      rw [Fin.sum_univ_succ]
      simp [negativeDiagonalCoordinates_connectedSumMarking,
        prependIntegerCoordinate]
      ring

/-- The standard manifold realizing `p⟨1⟩ ⊕ q⟨-1⟩`. -/
def oddDiagonalManifold (p q : ℕ) : ClosedConnectedOrientedSmoothFourManifold :=
  connectedSum (positiveDiagonalManifold p) (negativeDiagonalManifold q)

/-- Canonical coordinates on the full odd standard model. -/
def oddDiagonalCoordinates (p q : ℕ) :
    ManifoldH₂ (oddDiagonalManifold p q) ≃+
      ((Fin p → ℤ) × (Fin q → ℤ)) :=
  (connectedSumH₂ (positiveDiagonalManifold p)
    (negativeDiagonalManifold q)).trans
      ((positiveDiagonalCoordinates p).prodCongr
        (negativeDiagonalCoordinates q))

@[simp] theorem oddDiagonalCoordinates_connectedSumMarking
    (p q : ℕ) (a : ManifoldH₂ (positiveDiagonalManifold p))
    (b : ManifoldH₂ (negativeDiagonalManifold q)) :
    oddDiagonalCoordinates p q (connectedSumMarking a b) =
      (positiveDiagonalCoordinates p a, negativeDiagonalCoordinates q b) := by
  unfold oddDiagonalCoordinates connectedSumMarking
  change
    ((positiveDiagonalCoordinates p).prodCongr (negativeDiagonalCoordinates q))
        ((connectedSumH₂ (positiveDiagonalManifold p) (negativeDiagonalManifold q))
          ((connectedSumH₂ (positiveDiagonalManifold p)
            (negativeDiagonalManifold q)).symm (a, b))) = _
  rw [(connectedSumH₂ (positiveDiagonalManifold p)
    (negativeDiagonalManifold q)).apply_symm_apply]
  rfl

theorem oddDiagonal_pairing
    (p q : ℕ) (alpha beta : ManifoldH₂ (oddDiagonalManifold p q)) :
    integralIntersectionPairing (oddDiagonalManifold p q) alpha beta =
      standardOddPairing p q
        (oddDiagonalCoordinates p q alpha)
        (oddDiagonalCoordinates p q beta) := by
  let alphaParts := connectedSumH₂ (positiveDiagonalManifold p)
    (negativeDiagonalManifold q) alpha
  let betaParts := connectedSumH₂ (positiveDiagonalManifold p)
    (negativeDiagonalManifold q) beta
  have alphaSplit : alpha = connectedSumMarking alphaParts.1 alphaParts.2 := by
    exact (connectedSumH₂ (positiveDiagonalManifold p)
      (negativeDiagonalManifold q)).symm_apply_apply alpha |>.symm
  have betaSplit : beta = connectedSumMarking betaParts.1 betaParts.2 := by
    exact (connectedSumH₂ (positiveDiagonalManifold p)
      (negativeDiagonalManifold q)).symm_apply_apply beta |>.symm
  rw [alphaSplit, betaSplit]
  change
    integralIntersectionPairing
        (connectedSum (positiveDiagonalManifold p) (negativeDiagonalManifold q))
        (connectedSumMarking alphaParts.1 alphaParts.2)
        (connectedSumMarking betaParts.1 betaParts.2) = _
  rw [connectedSumH₂_preservesIntersectionPairing,
    positiveDiagonal_pairing, negativeDiagonal_pairing]
  unfold standardOddPairing
  simp [oddDiagonalCoordinates_connectedSumMarking]
  ring

theorem normalizedTwistedYetter_connectedSum
    (𝒞η : TwistedPremodularCategory K)
    (X Y : ClosedConnectedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) (beta : ManifoldH₂ Y) :
    NormalizedTwistedYetter 𝒞η
        ⟨connectedSum X Y, connectedSumMarking alpha beta⟩ =
      NormalizedTwistedYetter 𝒞η ⟨X, alpha⟩ *
        NormalizedTwistedYetter 𝒞η ⟨Y, beta⟩ := by
  unfold NormalizedTwistedYetter
  rw [markedConnectedSumFormula 𝒞η]
  ring

theorem normalizedTwistedYetter_fourSphere_zero
    (𝒞η : TwistedPremodularCategory K) :
    NormalizedTwistedYetter 𝒞η ⟨fourSphere, 0⟩ = 1 := by
  unfold NormalizedTwistedYetter
  rw [twistedYetter_fourSphere_zero]
  exact inv_mul_cancel₀ (eno_globalDimension_ne_zero 𝒞η.category)

theorem normalizedTwistedYetter_complexProjectivePlane
    (𝒞η : TwistedPremodularCategory K)
    (alpha : ManifoldH₂ complexProjectivePlane) :
    NormalizedTwistedYetter 𝒞η ⟨complexProjectivePlane, alpha⟩ =
      positiveShiftedGaussSum 𝒞η (complexProjectivePlaneH₂ alpha) := by
  have alpha_eq :
      alpha = complexProjectivePlaneH₂ alpha • positiveProjectivePlaneGenerator := by
    apply complexProjectivePlaneH₂.injective
    simp [positiveProjectivePlaneGenerator]
  rw [alpha_eq]
  unfold NormalizedTwistedYetter
  rw [twistedYetter_complexProjectivePlane]
  rw [← alpha_eq]
  rw [← mul_assoc, inv_mul_cancel₀
    (eno_globalDimension_ne_zero 𝒞η.category), one_mul]

theorem normalizedTwistedYetter_reversedComplexProjectivePlane
    (𝒞η : TwistedPremodularCategory K)
    (alpha : ManifoldH₂ reversedComplexProjectivePlane) :
    NormalizedTwistedYetter 𝒞η ⟨reversedComplexProjectivePlane, alpha⟩ =
      negativeShiftedGaussSum 𝒞η
        (reversedComplexProjectivePlaneH₂ alpha) := by
  have alpha_eq :
      alpha = reversedComplexProjectivePlaneH₂ alpha •
        negativeProjectivePlaneGenerator := by
    apply reversedComplexProjectivePlaneH₂.injective
    simp [negativeProjectivePlaneGenerator]
  rw [alpha_eq]
  unfold NormalizedTwistedYetter
  rw [twistedYetter_reversedComplexProjectivePlane]
  rw [← alpha_eq]
  rw [← mul_assoc, inv_mul_cancel₀
    (eno_globalDimension_ne_zero 𝒞η.category), one_mul]

theorem positiveDiagonal_simplyConnected (p : ℕ) :
    IsSimplyConnected (positiveDiagonalManifold p) := by
  induction p with
  | zero => exact fourSphere_simplyConnected
  | succ p inductionHypothesis =>
      exact connectedSum_simplyConnected
        complexProjectivePlane_simplyConnected inductionHypothesis

theorem negativeDiagonal_simplyConnected (q : ℕ) :
    IsSimplyConnected (negativeDiagonalManifold q) := by
  induction q with
  | zero => exact fourSphere_simplyConnected
  | succ q inductionHypothesis =>
      exact connectedSum_simplyConnected
        reversedComplexProjectivePlane_simplyConnected inductionHypothesis

theorem oddDiagonal_simplyConnected (p q : ℕ) :
    IsSimplyConnected (oddDiagonalManifold p q) :=
  connectedSum_simplyConnected
    (positiveDiagonal_simplyConnected p) (negativeDiagonal_simplyConnected q)

theorem normalizedTwistedYetter_positiveDiagonal
    (𝒞η : TwistedPremodularCategory K)
    (p : ℕ) (alpha : ManifoldH₂ (positiveDiagonalManifold p)) :
    NormalizedTwistedYetter 𝒞η ⟨positiveDiagonalManifold p, alpha⟩ =
      ∏ i, positiveShiftedGaussSum 𝒞η
        (positiveDiagonalCoordinates p alpha i) := by
  induction p with
  | zero =>
      have alpha_eq : alpha = 0 := fourSphere_H₂_eq_zero alpha
      subst alpha
      exact normalizedTwistedYetter_fourSphere_zero 𝒞η
  | succ p inductionHypothesis =>
      let parts := connectedSumH₂ complexProjectivePlane
        (positiveDiagonalManifold p) alpha
      have alphaSplit : alpha = connectedSumMarking parts.1 parts.2 :=
        (connectedSumH₂ complexProjectivePlane
          (positiveDiagonalManifold p)).symm_apply_apply alpha |>.symm
      rw [alphaSplit]
      change
        NormalizedTwistedYetter 𝒞η
            ⟨connectedSum complexProjectivePlane (positiveDiagonalManifold p),
              connectedSumMarking parts.1 parts.2⟩ = _
      rw [normalizedTwistedYetter_connectedSum,
        normalizedTwistedYetter_complexProjectivePlane,
        inductionHypothesis, Fin.prod_univ_succ]
      simp [positiveDiagonalCoordinates_connectedSumMarking,
        prependIntegerCoordinate]

theorem normalizedTwistedYetter_negativeDiagonal
    (𝒞η : TwistedPremodularCategory K)
    (q : ℕ) (alpha : ManifoldH₂ (negativeDiagonalManifold q)) :
    NormalizedTwistedYetter 𝒞η ⟨negativeDiagonalManifold q, alpha⟩ =
      ∏ i, negativeShiftedGaussSum 𝒞η
        (negativeDiagonalCoordinates q alpha i) := by
  induction q with
  | zero =>
      have alpha_eq : alpha = 0 := fourSphere_H₂_eq_zero alpha
      subst alpha
      exact normalizedTwistedYetter_fourSphere_zero 𝒞η
  | succ q inductionHypothesis =>
      let parts := connectedSumH₂ reversedComplexProjectivePlane
        (negativeDiagonalManifold q) alpha
      have alphaSplit : alpha = connectedSumMarking parts.1 parts.2 :=
        (connectedSumH₂ reversedComplexProjectivePlane
          (negativeDiagonalManifold q)).symm_apply_apply alpha |>.symm
      rw [alphaSplit]
      change
        NormalizedTwistedYetter 𝒞η
            ⟨connectedSum reversedComplexProjectivePlane (negativeDiagonalManifold q),
              connectedSumMarking parts.1 parts.2⟩ = _
      rw [normalizedTwistedYetter_connectedSum,
        normalizedTwistedYetter_reversedComplexProjectivePlane,
        inductionHypothesis, Fin.prod_univ_succ]
      simp [negativeDiagonalCoordinates_connectedSumMarking,
        prependIntegerCoordinate]

theorem normalizedTwistedYetter_oddDiagonal
    (𝒞η : TwistedPremodularCategory K)
    (p q : ℕ) (alpha : ManifoldH₂ (oddDiagonalManifold p q)) :
    NormalizedTwistedYetter 𝒞η ⟨oddDiagonalManifold p q, alpha⟩ =
      (∏ i, positiveShiftedGaussSum 𝒞η
        ((oddDiagonalCoordinates p q alpha).1 i)) *
      ∏ j, negativeShiftedGaussSum 𝒞η
        ((oddDiagonalCoordinates p q alpha).2 j) := by
  let parts := connectedSumH₂ (positiveDiagonalManifold p)
    (negativeDiagonalManifold q) alpha
  have alphaSplit : alpha = connectedSumMarking parts.1 parts.2 :=
    (connectedSumH₂ (positiveDiagonalManifold p)
      (negativeDiagonalManifold q)).symm_apply_apply alpha |>.symm
  rw [alphaSplit]
  change
    NormalizedTwistedYetter 𝒞η
        ⟨connectedSum (positiveDiagonalManifold p) (negativeDiagonalManifold q),
          connectedSumMarking parts.1 parts.2⟩ = _
  rw [normalizedTwistedYetter_connectedSum,
    normalizedTwistedYetter_positiveDiagonal,
    normalizedTwistedYetter_negativeDiagonal]
  simp [oddDiagonalCoordinates_connectedSumMarking]

theorem twistedYetter_oddDiagonal
    (𝒞η : TwistedPremodularCategory K)
    (p q : ℕ) (alpha : ManifoldH₂ (oddDiagonalManifold p q)) :
    TwistedYetter 𝒞η ⟨oddDiagonalManifold p q, alpha⟩ =
      𝒞η.category.globalDimension *
        (∏ i, positiveShiftedGaussSum 𝒞η
          ((oddDiagonalCoordinates p q alpha).1 i)) *
        ∏ j, negativeShiftedGaussSum 𝒞η
          ((oddDiagonalCoordinates p q alpha).2 j) := by
  have normalized := normalizedTwistedYetter_oddDiagonal 𝒞η p q alpha
  unfold NormalizedTwistedYetter at normalized
  calc
    TwistedYetter 𝒞η ⟨oddDiagonalManifold p q, alpha⟩ =
      𝒞η.category.globalDimension *
          (𝒞η.category.globalDimension⁻¹ *
            TwistedYetter 𝒞η ⟨oddDiagonalManifold p q, alpha⟩) := by
      rw [← mul_assoc, mul_inv_cancel₀
        (eno_globalDimension_ne_zero 𝒞η.category), one_mul]
    _ = _ := by rw [normalized, mul_assoc]

/-- The intersection-form isometry canonically induced by odd coordinates. -/
def oddDiagonalIntersectionFormIsometry
    {X : ClosedConnectedOrientedSmoothFourManifold}
    (diagonalization : OddDiagonalization X) :
    IntegralIntersectionFormIsometry X
      (oddDiagonalManifold diagonalization.positiveRank
        diagonalization.negativeRank) where
  toAddEquiv := diagonalization.coordinates.trans
    (oddDiagonalCoordinates diagonalization.positiveRank
      diagonalization.negativeRank).symm
  preservesPairing a b := by
    rw [oddDiagonal_pairing]
    simp
    exact diagonalization.preservesPairing a b

end

end TwistedYetter.StableNoGo
