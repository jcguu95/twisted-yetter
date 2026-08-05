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

end

end TwistedYetter.StableNoGo
