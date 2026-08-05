import TwistedYetter.StableNoGo.Main
import TwistedYetter.StableNoGo.NumericalDefinitions
import TwistedYetter.StableNoGo.NumericalStatement
import TwistedYetter.StableNoGo.OddDiagonalEvaluation
import TwistedYetter.StableNoGo.ProjectivePlaneEvaluation
import TwistedYetter.StableNoGo.SphereTwoProductEvaluation
import TwistedYetter.StableNoGo.ModularCategory
import TwistedYetter.StableNoGo.ModularTopologyInputs

/-!
# Stable calculation and no-go corollary

This file fixes the public theorem before its remaining proof obligations are
discharged.  Its signature contains only the mathematical input appearing in
the human statement.  Connected sums, stabilization scalars, Kirby diagrams,
and literature theorems belong to the proof and are not public assumptions.

All evaluator and stable-realization obligations are discharged in the
preceding modules.  The public statements contain no presentation, evaluator,
normalization, or proof-package parameter.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped BigOperators
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
Stable numerical calculation.  If `Y` is chosen to be an easily evaluated
standard representative of the marked intersection lattice of `X`, Wall and
Ruberman--Strle produce a common stabilization on which the numerator can be
calculated.  Dividing by the displayed nonzero stabilization multiplier
recovers the original value on `X`.
-/
theorem TwistedYetter_stable_calculation
    (𝒞η : TwistedPremodularCategory K)
    {X Y : ClosedOrientedSmoothFourManifold}
    (simplyConnectedX : IsSimplyConnected X)
    (simplyConnectedY : IsSimplyConnected Y)
    (f : IntegralIntersectionFormIsometry X Y)
    (alpha : ManifoldH₂ X) :
    ∃ (n : Nat)
      (F : OrientedDiffeomorphism (stabilize X n) (stabilize Y n)),
      inducedH₂ F (stabilizedMarking X alpha n) =
          stabilizedMarking Y (f alpha) n ∧
        TwistedYetter 𝒞η ⟨X, alpha⟩ =
          TwistedYetter 𝒞η
              ⟨stabilize Y n, stabilizedMarking Y (f alpha) n⟩ /
            stabilizationMultiplier 𝒞η 𝒞η.category.globalDimension ^ n := by
  obtain ⟨n, F, markingTransport⟩ :=
    markedStableRealization_of_wall_rubermanStrle
      simplyConnectedX simplyConnectedY f alpha
  refine ⟨n, F, markingTransport, ?_⟩
  have stabilizedEquality :=
    TwistedYetter_diffeomorphism_invariant
      𝒞η F (stabilizedMarking X alpha n)
  rw [markingTransport] at stabilizedEquality
  have sourceStabilization :=
    markedStabilizationFormula_of_connectedSum
      𝒞η 𝒞η.category.globalDimension (markedConnectedSumFormula 𝒞η)
      X alpha n
  apply (eq_div_iff (pow_ne_zero n (stabilizationMultiplier_ne_zero 𝒞η))).2
  simpa only [mul_comm] using sourceStabilization.symm.trans stabilizedEquality

/--
For a twisted premodular category, the homologically twisted Yetter invariant
of a closed simply connected oriented smooth four-manifold depends only on its
marked integral intersection lattice.
-/
theorem TwistedYetter_eq_of_integralIntersectionFormIsometry
    (𝒞η : TwistedPremodularCategory K)
    {X Y : ClosedOrientedSmoothFourManifold}
    (simplyConnectedX : IsSimplyConnected X)
    (simplyConnectedY : IsSimplyConnected Y)
    (f : IntegralIntersectionFormIsometry X Y)
    (alpha : ManifoldH₂ X) :
    TwistedYetter 𝒞η ⟨X, alpha⟩ =
      TwistedYetter 𝒞η ⟨Y, f alpha⟩ := by
  exact
    (premodularMarkedIntersectionFormInvariance_of_core_obligations
      𝒞η
      𝒞η.category.globalDimension
      (markedConnectedSumFormula 𝒞η)
      (stabilizationMultiplier_ne_zero 𝒞η)
      (fun _ _ simplyConnectedX simplyConnectedY f alpha =>
        markedStableRealization_of_wall_rubermanStrle
          simplyConnectedX simplyConnectedY f alpha))
      X Y simplyConnectedX simplyConnectedY f alpha

/-! ## Numerical statement -/

/-- The normalized arbitrary-marking hyperbolic block is the explicit finite
Hopf sum in its canonical THAM coordinates. -/
theorem normalizedTwistedYetter_sphereTwoProduct_eq_markedHyperbolicBlockSum
    (𝒞η : TwistedPremodularCategory K)
    (alpha : ManifoldH₂ sphereTwoProduct) :
    NormalizedTwistedYetter 𝒞η ⟨sphereTwoProduct, alpha⟩ =
      markedHyperbolicBlockSum 𝒞η
        (sphereTwoProductHopfCoordinates alpha).1
        (sphereTwoProductHopfCoordinates alpha).2 := by
  unfold NormalizedTwistedYetter
  rw [twistedYetter_sphereTwoProduct_eq_markedHyperbolicBlockSum]
  rw [← mul_assoc,
    inv_mul_cancel₀ (egno_globalDimension_ne_zero 𝒞η.category), one_mul]

/-- At the zero marking the same normalized block is the literal `(0,0)`
Hopf sum, independently of the noncomputable quotient representative used for
the general coordinate function. -/
theorem normalizedTwistedYetter_sphereTwoProduct_zero_eq_markedHyperbolicBlockSum
    (𝒞η : TwistedPremodularCategory K) :
    NormalizedTwistedYetter 𝒞η ⟨sphereTwoProduct, 0⟩ =
      markedHyperbolicBlockSum 𝒞η 0 0 := by
  unfold NormalizedTwistedYetter
  rw [twistedYetter_sphereTwoProduct_zero_eq,
    markedHyperbolicBlockSum_zero_eq]
  calc
    𝒞η.category.globalDimension⁻¹ *
          (𝒞η.category.globalDimension ^ 2 *
            transparentGlobalDimension 𝒞η.category) =
        (𝒞η.category.globalDimension⁻¹ *
            𝒞η.category.globalDimension) *
          (𝒞η.category.globalDimension *
            transparentGlobalDimension 𝒞η.category) := by ring
    _ = _ := by
      rw [inv_mul_cancel₀
        (egno_globalDimension_ne_zero 𝒞η.category), one_mul]

/-- The product of the normalized invariant values of a marked standard block
list.  This is the proof bridge used by connected-sum multiplicativity. -/
noncomputable def standardK3HBlockProduct
    (𝒞η : TwistedPremodularCategory K) :
    (blocks : List K3HBlock) → K3HBlockMarkings blocks → K
  | [], _ => 1
  | block :: blocks, markings =>
      NormalizedTwistedYetter 𝒞η ⟨block.manifold, markings.1⟩ *
        standardK3HBlockProduct 𝒞η blocks markings.2

/-- The explicit normalized value assigned to one standard even block.  The
two `K3` orientations remain basic marked values; the hyperbolic block is the
finite Hopf sum proved above. -/
noncomputable def explicitK3HBlockValue
    (𝒞η : TwistedPremodularCategory K) :
    (block : K3HBlock) → ManifoldH₂ block.manifold → K
  | .positiveK3, marking =>
      NormalizedTwistedYetter 𝒞η ⟨k3Surface, marking⟩
  | .negativeK3, marking =>
      NormalizedTwistedYetter 𝒞η ⟨reversedK3Surface, marking⟩
  | .hyperbolic, marking =>
      markedHyperbolicBlockSum 𝒞η
        (sphereTwoProductHopfCoordinates marking).1
        (sphereTwoProductHopfCoordinates marking).2

theorem explicitK3HBlockValue_eq_normalizedTwistedYetter
    (𝒞η : TwistedPremodularCategory K)
    (block : K3HBlock) (marking : ManifoldH₂ block.manifold) :
    explicitK3HBlockValue 𝒞η block marking =
      NormalizedTwistedYetter 𝒞η ⟨block.manifold, marking⟩ := by
  cases block with
  | positiveK3 => rfl
  | negativeK3 => rfl
  | hyperbolic =>
      exact
        (normalizedTwistedYetter_sphereTwoProduct_eq_markedHyperbolicBlockSum
          𝒞η marking).symm

/-- The explicit product appearing in the even formula. -/
noncomputable def explicitK3HBlockProduct
    (𝒞η : TwistedPremodularCategory K) :
    (blocks : List K3HBlock) → K3HBlockMarkings blocks → K
  | [], _ => 1
  | block :: blocks, markings =>
      explicitK3HBlockValue 𝒞η block markings.1 *
        explicitK3HBlockProduct 𝒞η blocks markings.2

theorem explicitK3HBlockProduct_eq_standardK3HBlockProduct
    (𝒞η : TwistedPremodularCategory K)
    (blocks : List K3HBlock) (markings : K3HBlockMarkings blocks) :
    explicitK3HBlockProduct 𝒞η blocks markings =
      standardK3HBlockProduct 𝒞η blocks markings := by
  induction blocks with
  | nil => rfl
  | cons block blocks inductionHypothesis =>
      change
        explicitK3HBlockValue 𝒞η block markings.1 *
            explicitK3HBlockProduct 𝒞η blocks markings.2 =
          NormalizedTwistedYetter 𝒞η ⟨block.manifold, markings.1⟩ *
            standardK3HBlockProduct 𝒞η blocks markings.2
      rw [explicitK3HBlockValue_eq_normalizedTwistedYetter,
        inductionHypothesis markings.2]

/-- The explicit shifted-Gauss-sum expression for an odd diagonalization. -/
noncomputable def oddFormula
    (𝒞η : TwistedPremodularCategory K)
    {X : ClosedOrientedSmoothFourManifold}
    (diagonalization : OddDiagonalization X)
    (alpha : ManifoldH₂ X) : K :=
  let coordinates := diagonalization.coordinates alpha
  𝒞η.category.globalDimension *
    (∏ i, positiveShiftedGaussSum 𝒞η (coordinates.1 i)) *
    (∏ j, negativeShiftedGaussSum 𝒞η (coordinates.2 j))

/-- The connected-sum-normalized odd expression. -/
noncomputable def normalizedOddFormula
    (𝒞η : TwistedPremodularCategory K)
    {X : ClosedOrientedSmoothFourManifold}
    (diagonalization : OddDiagonalization X)
    (alpha : ManifoldH₂ X) : K :=
  let coordinates := diagonalization.coordinates alpha
  (∏ i, positiveShiftedGaussSum 𝒞η (coordinates.1 i)) *
    (∏ j, negativeShiftedGaussSum 𝒞η (coordinates.2 j))

/-- The stabilized `K3/H` block expression for a marked even decomposition. -/
noncomputable def evenFormula
    (𝒞η : TwistedPremodularCategory K)
    {X : ClosedOrientedSmoothFourManifold}
    {alpha : ManifoldH₂ X}
    (decomposition : EvenStableK3HDecomposition X alpha) : K :=
  explicitK3HBlockProduct 𝒞η decomposition.blocks decomposition.markings /
    markedHyperbolicBlockSum 𝒞η 0 0 ^
      decomposition.stabilizationCount

/-- The odd numerical formula for one simply connected four-manifold. -/
def SatisfiesOddFormula
    (𝒞η : TwistedPremodularCategory K)
    (X : ClosedOrientedSmoothFourManifold) : Prop :=
  IsSimplyConnected X →
    ∀ (diagonalization : OddDiagonalization X) (alpha : ManifoldH₂ X),
      TwistedYetter 𝒞η ⟨X, alpha⟩ = oddFormula 𝒞η diagonalization alpha

/-- The even stable numerical formula for one simply connected four-manifold. -/
def SatisfiesEvenFormula
    (𝒞η : TwistedPremodularCategory K)
    (X : ClosedOrientedSmoothFourManifold) : Prop :=
  IsSimplyConnected X →
    ∀ (alpha : ManifoldH₂ X)
      (decomposition : EvenStableK3HDecomposition X alpha),
      NormalizedTwistedYetter 𝒞η ⟨X, alpha⟩ = evenFormula 𝒞η decomposition

theorem normalizedTwistedYetter_connectedSumBlocks
    (𝒞η : TwistedPremodularCategory K)
    (blocks : List K3HBlock) (markings : K3HBlockMarkings blocks) :
    NormalizedTwistedYetter 𝒞η
        ⟨connectedSumK3HBlocks blocks,
          connectedSumK3HMarking blocks markings⟩ =
      standardK3HBlockProduct 𝒞η blocks markings := by
  induction blocks with
  | nil =>
      exact normalizedTwistedYetter_fourSphere_zero 𝒞η
  | cons block blocks inductionHypothesis =>
      change
        NormalizedTwistedYetter 𝒞η
            ⟨connectedSum block.manifold (connectedSumK3HBlocks blocks),
              connectedSumMarking markings.1
                (connectedSumK3HMarking blocks markings.2)⟩ =
          NormalizedTwistedYetter 𝒞η ⟨block.manifold, markings.1⟩ *
            standardK3HBlockProduct 𝒞η blocks markings.2
      rw [normalizedTwistedYetter_connectedSum,
        inductionHypothesis markings.2]

theorem k3HBlock_simplyConnected (block : K3HBlock) :
    IsSimplyConnected block.manifold := by
  cases block with
  | positiveK3 => exact k3Surface_simplyConnected
  | negativeK3 => exact reversedK3Surface_simplyConnected
  | hyperbolic => exact sphereTwoProduct_simplyConnected

theorem connectedSumBlocks_simplyConnected
    (blocks : List K3HBlock) :
    IsSimplyConnected (connectedSumK3HBlocks blocks) := by
  induction blocks with
  | nil => exact fourSphere_simplyConnected
  | cons block blocks inductionHypothesis =>
      exact connectedSum_simplyConnected
        (k3HBlock_simplyConnected block) inductionHypothesis

theorem normalizedTwistedYetter_stabilize
    (𝒞η : TwistedPremodularCategory K)
    (X : ClosedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) (n : ℕ) :
    NormalizedTwistedYetter 𝒞η
        ⟨stabilize X n, stabilizedMarking X alpha n⟩ =
      NormalizedTwistedYetter 𝒞η ⟨sphereTwoProduct, 0⟩ ^ n *
        NormalizedTwistedYetter 𝒞η ⟨X, alpha⟩ := by
  unfold NormalizedTwistedYetter
  rw [markedStabilizationFormula_of_connectedSum
    𝒞η 𝒞η.category.globalDimension (markedConnectedSumFormula 𝒞η)
    X alpha n]
  unfold stabilizationMultiplier
  ring

theorem satisfiesEvenFormula
    (𝒞η : TwistedPremodularCategory K)
    (X : ClosedOrientedSmoothFourManifold) :
    SatisfiesEvenFormula 𝒞η X := by
  intro simplyConnectedX alpha decomposition
  have invariantEquality :=
    TwistedYetter_eq_of_integralIntersectionFormIsometry
      𝒞η
      (stabilize_simplyConnected X simplyConnectedX
        decomposition.stabilizationCount)
      (connectedSumBlocks_simplyConnected decomposition.blocks)
      decomposition.isometry
      (stabilizedMarking X alpha decomposition.stabilizationCount)
  rw [decomposition.markingTransport] at invariantEquality
  have normalizedEquality :
      NormalizedTwistedYetter 𝒞η
          ⟨stabilize X decomposition.stabilizationCount,
            stabilizedMarking X alpha decomposition.stabilizationCount⟩ =
      NormalizedTwistedYetter 𝒞η
          ⟨connectedSumK3HBlocks decomposition.blocks,
            connectedSumK3HMarking decomposition.blocks
              decomposition.markings⟩ := by
    unfold NormalizedTwistedYetter
    rw [invariantEquality]
  rw [normalizedTwistedYetter_stabilize,
    normalizedTwistedYetter_connectedSumBlocks] at normalizedEquality
  unfold evenFormula
  rw [explicitK3HBlockProduct_eq_standardK3HBlockProduct,
    ← normalizedTwistedYetter_sphereTwoProduct_zero_eq_markedHyperbolicBlockSum]
  apply (eq_div_iff ?_).2
  · simpa [mul_comm] using normalizedEquality
  · change
      stabilizationMultiplier 𝒞η 𝒞η.category.globalDimension ^
        decomposition.stabilizationCount ≠ 0
    exact pow_ne_zero _ (stabilizationMultiplier_ne_zero 𝒞η)

theorem satisfiesOddFormula
    (𝒞η : TwistedPremodularCategory K)
    (X : ClosedOrientedSmoothFourManifold) :
    SatisfiesOddFormula 𝒞η X := by
  intro simplyConnectedX diagonalization alpha
  let standardIsometry := oddDiagonalIntersectionFormIsometry diagonalization
  have invariantEquality :=
    TwistedYetter_eq_of_integralIntersectionFormIsometry
      𝒞η simplyConnectedX
      (oddDiagonal_simplyConnected diagonalization.positiveRank
        diagonalization.negativeRank)
      standardIsometry alpha
  rw [twistedYetter_oddDiagonal] at invariantEquality
  simpa [oddFormula, standardIsometry,
    oddDiagonalIntersectionFormIsometry] using invariantEquality

/-- The normalized form of the odd numerical formula. -/
theorem normalizedTwistedYetter_eq_normalizedOddFormula
    (𝒞η : TwistedPremodularCategory K)
    {X : ClosedOrientedSmoothFourManifold}
    (simplyConnectedX : IsSimplyConnected X)
    (diagonalization : OddDiagonalization X)
    (alpha : ManifoldH₂ X) :
    NormalizedTwistedYetter 𝒞η ⟨X, alpha⟩ =
      normalizedOddFormula 𝒞η diagonalization alpha := by
  unfold NormalizedTwistedYetter
  rw [(satisfiesOddFormula 𝒞η X) simplyConnectedX diagonalization alpha]
  unfold oddFormula normalizedOddFormula
  dsimp only
  calc
    𝒞η.category.globalDimension⁻¹ *
          ((𝒞η.category.globalDimension *
              ∏ i, positiveShiftedGaussSum 𝒞η
                ((diagonalization.coordinates alpha).1 i)) *
            ∏ j, negativeShiftedGaussSum 𝒞η
              ((diagonalization.coordinates alpha).2 j)) =
        (𝒞η.category.globalDimension⁻¹ *
            𝒞η.category.globalDimension) *
          ((∏ i, positiveShiftedGaussSum 𝒞η
              ((diagonalization.coordinates alpha).1 i)) *
            ∏ j, negativeShiftedGaussSum 𝒞η
              ((diagonalization.coordinates alpha).2 j)) := by ring
    _ = _ := by
      rw [inv_mul_cancel₀
        (egno_globalDimension_ne_zero 𝒞η.category), one_mul]

/--
**Final Theorem (premodular numerical formula).**

For every marked simply connected closed oriented smooth four-manifold, its
integral intersection form is odd or even.  In the odd case an actual integral
diagonalization is supplied and the normalized invariant is the corresponding
product of shifted Gauss sums.  In the even case an actual marked stable
`K3/\bar K3/H` decomposition is supplied and the normalized invariant is the
explicit stabilized block quotient.
-/
theorem TwistedYetter_premodular_numerical_formula
    (𝒞η : TwistedPremodularCategory K)
    {X : ClosedOrientedSmoothFourManifold}
    (simplyConnectedX : IsSimplyConnected X)
    (alpha : ManifoldH₂ X) :
    (HasOddIntersectionForm X ∧
      ∃ diagonalization : OddDiagonalization X,
        NormalizedTwistedYetter 𝒞η ⟨X, alpha⟩ =
          normalizedOddFormula 𝒞η diagonalization alpha) ∨
    (HasEvenIntersectionForm X ∧
      ∃ decomposition : EvenStableK3HDecomposition X alpha,
        NormalizedTwistedYetter 𝒞η ⟨X, alpha⟩ =
          evenFormula 𝒞η decomposition) := by
  rcases odd_or_even_intersectionForm X with odd | even
  · obtain ⟨diagonalization⟩ :=
      oddIntersectionForm_diagonalization X simplyConnectedX odd
    exact Or.inl
      ⟨odd, diagonalization,
        normalizedTwistedYetter_eq_normalizedOddFormula
          𝒞η simplyConnectedX diagonalization alpha⟩
  · obtain ⟨decomposition⟩ :=
      evenStableK3HDecomposition_exists X simplyConnectedX even alpha
    exact Or.inr
      ⟨even, decomposition,
        (satisfiesEvenFormula 𝒞η X)
          simplyConnectedX alpha decomposition⟩

end

end TwistedYetter.StableNoGo
