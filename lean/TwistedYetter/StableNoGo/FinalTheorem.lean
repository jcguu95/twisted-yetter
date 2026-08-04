import TwistedYetter.StableNoGo.Main
import TwistedYetter.StableNoGo.SphereTwoProductEvaluation

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

/-- The normalization for which connected sum is exactly multiplicative. -/
noncomputable def NormalizedTwistedYetter
    (𝒞η : TwistedPremodularCategory K)
    (Xα : Σ X : ClosedOrientedSmoothFourManifold, ManifoldH₂ X) : K :=
  𝒞η.category.globalDimension⁻¹ * TwistedYetter 𝒞η Xα

/-- The scalar by which the ribbon twist acts on a chosen simple object. -/
noncomputable def simpleTwistScalar
    (𝒞η : TwistedPremodularCategory K)
    (simple : 𝒞η.category.Simple) : K :=
  (simpleEndLinearEquiv K (𝒞η.category.simpleObject simple)).symm
    (𝒞η.category.twist.hom.app (𝒞η.category.simpleObject simple))

/-- `Σᵢ dᵢ² θᵢ ηᵢⁿ`. -/
noncomputable def positiveShiftedGaussSum
    (𝒞η : TwistedPremodularCategory K) (n : ℤ) : K :=
  ∑ simple : 𝒞η.category.Simple,
    𝒞η.category.quantumDimension simple ^ 2 *
      simpleTwistScalar 𝒞η simple *
      ((((𝒞η.character.value simple) ^ n : Kˣ) : K))

/-- `Σᵢ dᵢ² θᵢ⁻¹ ηᵢⁿ`. -/
noncomputable def negativeShiftedGaussSum
    (𝒞η : TwistedPremodularCategory K) (n : ℤ) : K :=
  ∑ simple : 𝒞η.category.Simple,
    𝒞η.category.quantumDimension simple ^ 2 *
      (simpleTwistScalar 𝒞η simple)⁻¹ *
      ((((𝒞η.character.value simple) ^ n : Kˣ) : K))

/-- The diagonal pairing with `p` positive and `q` negative generators. -/
def standardOddPairing (p q : ℕ)
    (a b : (Fin p → ℤ) × (Fin q → ℤ)) : ℤ :=
  (∑ i, a.1 i * b.1 i) - ∑ j, a.2 j * b.2 j

/-- A coordinate choice identifying an odd intersection form with `p⟨1⟩ ⊕ q⟨-1⟩`. -/
structure OddDiagonalization
    (X : ClosedOrientedSmoothFourManifold) where
  positiveRank : ℕ
  negativeRank : ℕ
  coordinates :
    ManifoldH₂ X ≃+
      ((Fin positiveRank → ℤ) × (Fin negativeRank → ℤ))
  preservesPairing :
    ∀ a b : ManifoldH₂ X,
      standardOddPairing positiveRank negativeRank
          (coordinates a) (coordinates b) =
        integralIntersectionPairing X a b

/-
These are foundational names for the standard even blocks.  Their handle and
intersection-form realizations belong to the topology proof, not to the
numerical theorem's parameters.
-/
axiom fourSphere : ClosedOrientedSmoothFourManifold
axiom k3Surface : ClosedOrientedSmoothFourManifold
axiom reversedK3Surface : ClosedOrientedSmoothFourManifold

/-- The three standard blocks used in the stable even formula. -/
inductive K3HBlock
  | positiveK3
  | negativeK3
  | hyperbolic

def K3HBlock.manifold : K3HBlock → ClosedOrientedSmoothFourManifold
  | .positiveK3 => k3Surface
  | .negativeK3 => reversedK3Surface
  | .hyperbolic => sphereTwoProduct

/-- A standard block together with its transported homology marking. -/
structure MarkedK3HBlock where
  block : K3HBlock
  marking : ManifoldH₂ block.manifold

/-- The connected sum represented by a finite list of standard blocks. -/
def connectedSumBlocks : List MarkedK3HBlock → ClosedOrientedSmoothFourManifold
  | [] => fourSphere
  | block :: blocks =>
      connectedSum block.block.manifold (connectedSumBlocks blocks)

/-- The corresponding direct-sum marking. -/
def connectedSumBlockMarking :
    (blocks : List MarkedK3HBlock) → ManifoldH₂ (connectedSumBlocks blocks)
  | [] => 0
  | block :: blocks =>
      connectedSumMarking block.marking (connectedSumBlockMarking blocks)

/--
A marked stable `K3/H` decomposition.  It contains only a stabilization count,
standard marked blocks, an intersection-form isometry, and the exact image of
the marking.  It contains no category or evaluator equality.
-/
structure EvenStableK3HDecomposition
    (X : ClosedOrientedSmoothFourManifold) (alpha : ManifoldH₂ X) where
  stabilizationCount : ℕ
  blocks : List MarkedK3HBlock
  isometry : IntegralIntersectionFormIsometry
    (stabilize X stabilizationCount) (connectedSumBlocks blocks)
  markingTransport :
    isometry (stabilizedMarking X alpha stabilizationCount) =
      connectedSumBlockMarking blocks

/-- The product of the normalized numerical values of the marked blocks. -/
noncomputable def standardK3HBlockProduct
    (𝒞η : TwistedPremodularCategory K)
    (blocks : List MarkedK3HBlock) : K :=
  (blocks.map fun block =>
    NormalizedTwistedYetter 𝒞η ⟨block.block.manifold, block.marking⟩).prod

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

/-- The stabilized `K3/H` block expression for a marked even decomposition. -/
noncomputable def evenFormula
    (𝒞η : TwistedPremodularCategory K)
    {X : ClosedOrientedSmoothFourManifold}
    {alpha : ManifoldH₂ X}
    (decomposition : EvenStableK3HDecomposition X alpha) : K :=
  standardK3HBlockProduct 𝒞η decomposition.blocks /
    NormalizedTwistedYetter 𝒞η ⟨sphereTwoProduct, 0⟩ ^
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

/--
**Final Theorem (premodular numerical formula).**

The first conjunct is the explicit shifted-Gauss-sum formula for every odd
diagonalization.  The second is the exact stable `K3/H` block formula for every
marked even decomposition.
-/
theorem TwistedYetter_premodular_numerical_formula
    (𝒞η : TwistedPremodularCategory K) :
    (∀ X, SatisfiesOddFormula 𝒞η X) ∧
    (∀ X, SatisfiesEvenFormula 𝒞η X) := by
  sorry

/-- A twisted premodular category whose Müger centre is trivial. -/
structure TwistedModularCategory (K : Type uK)
    [Field K] [IsAlgClosed K] [CharZero K]
    extends TwistedPremodularCategory K where
  nondegenerate :
    ∀ simple : category.Simple,
      (∀ X : category.C,
        monodromyHom (category.simpleObject simple) X =
          𝟙 (category.simpleObject simple ⊗ X)) →
      Nonempty (category.simpleObject simple ≅ 𝟙_ category.C)

def TwistedModularCategory.toPremodular
    (𝒞η : TwistedModularCategory K) : TwistedPremodularCategory K :=
  𝒞η.toTwistedPremodularCategory

/--
The intrinsic Pontryagin-square correction associated to the invertible object
representing the character.  This must be constructed from modularity; it is
not caller-supplied data.
-/
noncomputable def quadraticCorrection
    (𝒞η : TwistedModularCategory K)
    (X : ClosedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) : K := by
  sorry

/--
**Main Corollary (modular numerical formula).**

For every simply connected closed four-manifold, the twisted value is the
untwisted-marking value times the intrinsic quadratic correction.
-/
theorem TwistedYetter_modular_numerical_formula
    (𝒞η : TwistedModularCategory K)
    {X : ClosedOrientedSmoothFourManifold}
    (simplyConnectedX : IsSimplyConnected X)
    (alpha : ManifoldH₂ X) :
    TwistedYetter 𝒞η.toPremodular ⟨X, alpha⟩ =
      TwistedYetter 𝒞η.toPremodular ⟨X, 0⟩ *
        quadraticCorrection 𝒞η X alpha := by
  sorry

end

end TwistedYetter.StableNoGo
