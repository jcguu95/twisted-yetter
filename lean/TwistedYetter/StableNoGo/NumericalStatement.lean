import TwistedYetter.StableNoGo.NumericalDefinitions
import TwistedYetter.StableNoGo.EntranceAxioms

/-!
# Numerical statement data

Small, proof-free data types used to state the odd numerical formula.
-/

namespace TwistedYetter.StableNoGo

open scoped BigOperators
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

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

/-! ## Even `K3/H` statement data -/

/-- The three standard oriented blocks used in the stable even formula. -/
inductive K3HBlock
  | positiveK3
  | negativeK3
  | hyperbolic

def K3HBlock.manifold : K3HBlock → ClosedOrientedSmoothFourManifold
  | .positiveK3 => k3Surface
  | .negativeK3 => reversedK3Surface
  | .hyperbolic => sphereTwoProduct

/-- The connected sum represented by an unmarked finite block list. -/
def connectedSumK3HBlocks : List K3HBlock → ClosedOrientedSmoothFourManifold
  | [] => fourSphere
  | block :: blocks =>
      connectedSum block.manifold (connectedSumK3HBlocks blocks)

/-- A marking on each block of a finite `K3/\bar K3/H` list. -/
def K3HBlockMarkings : List K3HBlock → Type
  | [] => PUnit
  | block :: blocks =>
      ManifoldH₂ block.manifold × K3HBlockMarkings blocks

/-- The direct-sum marking determined by a block list and its dependent family
of block markings. -/
def connectedSumK3HMarking :
    (blocks : List K3HBlock) →
      K3HBlockMarkings blocks → ManifoldH₂ (connectedSumK3HBlocks blocks)
  | [], _ => 0
  | block :: blocks, markings =>
      connectedSumMarking markings.1
        (connectedSumK3HMarking blocks markings.2)

/--
A marked stable `K3/\bar K3/H` decomposition.  It records only a stabilization
count, standard marked blocks, an integral intersection-form isometry, and the
exact transported marking.  It contains no category or evaluator equality.
-/
structure EvenStableK3HDecomposition
    (X : ClosedOrientedSmoothFourManifold) (alpha : ManifoldH₂ X) where
  stabilizationCount : ℕ
  blocks : List K3HBlock
  markings : K3HBlockMarkings blocks
  isometry : IntegralIntersectionFormIsometry
    (stabilize X stabilizationCount) (connectedSumK3HBlocks blocks)
  markingTransport :
    isometry (stabilizedMarking X alpha stabilizationCount) =
      connectedSumK3HMarking blocks markings

end

end TwistedYetter.StableNoGo
