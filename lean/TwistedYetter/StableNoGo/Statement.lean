import TwistedYetter.StableNoGo.StabilizationCancellation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Human statement of the stable no-go theorem

This file fixes the mathematical input and conclusion independently of the
future connected-sum proof.  In particular, an intersection-form isometry is
not represented by an arbitrary relation: it is an additive equivalence that
preserves the integral intersection pairing on every pair of classes.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- The ordinary topological meaning of simply connected. -/
abbrev IsSimplyConnected
    (X : ClosedConnectedOrientedSmoothFourManifold) : Prop :=
  SimplyConnectedSpace (underlyingTopologicalSpace.{0} X)

/--
The integral intersection pairing of a closed oriented smooth four-manifold.

The current frontend has integral singular `H₂` but not the cup/cap-product
machinery needed to construct this pairing.  This is therefore an explicit
foundational topology boundary.  It contains no category or evaluator data.
-/
axiom integralIntersectionPairing
    (X : ClosedConnectedOrientedSmoothFourManifold) :
    ManifoldH₂ X →+ ManifoldH₂ X →+ ℤ

/--
An isometry of integral intersection lattices: an additive equivalence that
preserves the pairing on every ordered pair of homology classes.
-/
structure IntegralIntersectionFormIsometry
    (X Y : ClosedConnectedOrientedSmoothFourManifold) where
  toAddEquiv : ManifoldH₂ X ≃+ ManifoldH₂ Y
  preservesPairing :
    ∀ a b : ManifoldH₂ X,
      integralIntersectionPairing Y (toAddEquiv a) (toAddEquiv b) =
        integralIntersectionPairing X a b

namespace IntegralIntersectionFormIsometry

instance {X Y : ClosedConnectedOrientedSmoothFourManifold} :
    CoeFun (IntegralIntersectionFormIsometry X Y)
      (fun _ => ManifoldH₂ X → ManifoldH₂ Y) where
  coe f := f.toAddEquiv

end IntegralIntersectionFormIsometry

/--
The precise human theorem that the new development is intended to prove.

It says that on closed, simply connected, oriented smooth four-manifolds the
Twisted Yetter value depends only on the marked integral intersection lattice.
-/
def PremodularMarkedIntersectionFormInvariance
    (𝒞η : TwistedPremodularCategory K) : Prop :=
  ∀ (X Y : ClosedConnectedOrientedSmoothFourManifold),
    IsSimplyConnected X →
    IsSimplyConnected Y →
    ∀ (f : IntegralIntersectionFormIsometry X Y)
      (alpha : ManifoldH₂ X),
      TwistedYetter 𝒞η ⟨X, alpha⟩ =
        TwistedYetter 𝒞η ⟨Y, f alpha⟩

end

end TwistedYetter.StableNoGo
