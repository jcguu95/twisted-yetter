import TwistedYetter.StableNoGo.EntranceAxioms

/-!
# Marked stable realization from Wall and Ruberman--Strle

This file contains no evaluator calculation.  It derives the exact marked
stable realization needed by the final cancellation argument from the explicit
topology entrances in `EntranceAxioms`.
-/

namespace TwistedYetter.StableNoGo

open TwistedYetter.Semantics.Independent

noncomputable section

namespace IntegralIntersectionFormIsometry

/-- Identity isometry of an integral intersection form. -/
def refl (X : ClosedOrientedSmoothFourManifold) :
    IntegralIntersectionFormIsometry X X where
  toAddEquiv := AddEquiv.refl (ManifoldH₂ X)
  preservesPairing := by
    intro a b
    rfl

/-- Inverse of an integral intersection-form isometry. -/
def symm {X Y : ClosedOrientedSmoothFourManifold}
    (f : IntegralIntersectionFormIsometry X Y) :
    IntegralIntersectionFormIsometry Y X where
  toAddEquiv := f.toAddEquiv.symm
  preservesPairing := by
    intro a b
    simpa only [f.toAddEquiv.apply_symm_apply] using
      (f.preservesPairing
        (f.toAddEquiv.symm a) (f.toAddEquiv.symm b)).symm

/-- Composite of two integral intersection-form isometries. -/
def trans {X Y Z : ClosedOrientedSmoothFourManifold}
    (f : IntegralIntersectionFormIsometry X Y)
    (g : IntegralIntersectionFormIsometry Y Z) :
    IntegralIntersectionFormIsometry X Z where
  toAddEquiv := f.toAddEquiv.trans g.toAddEquiv
  preservesPairing := by
    intro a b
    change
      integralIntersectionPairing Z
          (g.toAddEquiv (f.toAddEquiv a))
          (g.toAddEquiv (f.toAddEquiv b)) =
        integralIntersectionPairing X a b
    rw [g.preservesPairing, f.preservesPairing]

/-- Orthogonal direct sum of two intersection-form isometries. -/
def connectedSum
    {X X' Y Y' : ClosedOrientedSmoothFourManifold}
    (f : IntegralIntersectionFormIsometry X X')
    (g : IntegralIntersectionFormIsometry Y Y') :
    IntegralIntersectionFormIsometry
      (StableNoGo.connectedSum X Y) (StableNoGo.connectedSum X' Y') where
  toAddEquiv := connectedSumH₂Map f.toAddEquiv g.toAddEquiv
  preservesPairing := by
    intro u v
    let uv := connectedSumH₂ X Y u
    let vv := connectedSumH₂ X Y v
    have hu : connectedSumMarking uv.1 uv.2 = u :=
      (connectedSumH₂ X Y).symm_apply_apply u
    have hv : connectedSumMarking vv.1 vv.2 = v :=
      (connectedSumH₂ X Y).symm_apply_apply v
    rw [← hu, ← hv]
    simp only [connectedSumH₂Map_apply]
    rw [connectedSumH₂_preservesIntersectionPairing]
    rw [connectedSumH₂_preservesIntersectionPairing]
    rw [f.preservesPairing, g.preservesPairing]

end IntegralIntersectionFormIsometry

/-- Every finite `S² × S²` stabilization of a simply connected manifold is simply connected. -/
theorem stabilize_simplyConnected
    (X : ClosedOrientedSmoothFourManifold)
    (simplyConnectedX : IsSimplyConnected X) :
    ∀ n : Nat, IsSimplyConnected (stabilize X n)
  | 0 => simplyConnectedX
  | n + 1 =>
      connectedSum_simplyConnected
        (stabilize_simplyConnected X simplyConnectedX n)
        sphereTwoProduct_simplyConnected

/-- The requested isometry extended by identity over every stabilization summand. -/
def stabilizedIntersectionFormIsometry
    {X Y : ClosedOrientedSmoothFourManifold}
    (f : IntegralIntersectionFormIsometry X Y) :
    ∀ n : Nat,
      IntegralIntersectionFormIsometry (stabilize X n) (stabilize Y n)
  | 0 => f
  | n + 1 =>
      (stabilizedIntersectionFormIsometry f n).connectedSum
        (IntegralIntersectionFormIsometry.refl sphereTwoProduct)

/-- The stabilized isometry sends `alpha ⊕ 0` to `f(alpha) ⊕ 0`. -/
theorem stabilizedIntersectionFormIsometry_apply_marking
    {X Y : ClosedOrientedSmoothFourManifold}
    (f : IntegralIntersectionFormIsometry X Y)
    (alpha : ManifoldH₂ X) :
    ∀ n : Nat,
      stabilizedIntersectionFormIsometry f n
          (stabilizedMarking X alpha n) =
        stabilizedMarking Y (f alpha) n
  | 0 => rfl
  | n + 1 => by
      change
        connectedSumH₂Map
            (stabilizedIntersectionFormIsometry f n).toAddEquiv
            (AddEquiv.refl (ManifoldH₂ sphereTwoProduct))
            (connectedSumMarking (stabilizedMarking X alpha n) 0) =
          connectedSumMarking (stabilizedMarking Y (f alpha) n) 0
      rw [connectedSumH₂Map_apply]
      rw [stabilizedIntersectionFormIsometry_apply_marking f alpha n]
      rfl

/--
Wall supplies an unmarked stable diffeomorphism.  Ruberman--Strle corrects its
homology action after one further stabilization, producing the exact marking
transport needed by the invariant argument.
-/
theorem markedStableRealization_of_wall_rubermanStrle
    {X Y : ClosedOrientedSmoothFourManifold}
    (simplyConnectedX : IsSimplyConnected X)
    (simplyConnectedY : IsSimplyConnected Y)
    (f : IntegralIntersectionFormIsometry X Y)
    (alpha : ManifoldH₂ X) :
    MarkedStableRealization
      stabilize stabilizedMarking alpha (f alpha) := by
  obtain ⟨n, g⟩ := wall_stableClassification simplyConnectedX simplyConnectedY f
  let B := stabilizedIntersectionFormIsometry f n
  let G := intersectionFormIsometryOfDiffeomorphism g
  let A : IntegralIntersectionFormIsometry (stabilize X n) (stabilize X n) :=
    B.trans G.symm
  obtain ⟨h, hAction⟩ :=
    rubermanStrle_oneStableRealization
      (stabilize_simplyConnected X simplyConnectedX n) A
  let gSum := connectedSumOrientedDiffeomorphism g
    (identityOrientedDiffeomorphism sphereTwoProduct)
  let F := composeOrientedDiffeomorphism h gSum
  refine ⟨n + 1, F, ?_⟩
  change
    inducedH₂ F
        (connectedSumMarking (stabilizedMarking X alpha n) 0) =
      connectedSumMarking (stabilizedMarking Y (f alpha) n) 0
  rw [show inducedH₂ F = (inducedH₂ h).trans (inducedH₂ gSum) by
    exact inducedH₂_composeOrientedDiffeomorphism h gSum]
  rw [hAction]
  change
    inducedH₂ gSum
        (connectedSumH₂Map A.toAddEquiv
          (AddEquiv.refl (ManifoldH₂ sphereTwoProduct))
          (connectedSumMarking (stabilizedMarking X alpha n) 0)) =
      connectedSumMarking (stabilizedMarking Y (f alpha) n) 0
  rw [connectedSumH₂Map_apply]
  rw [show inducedH₂ gSum =
      connectedSumH₂Map (inducedH₂ g)
        (inducedH₂ (identityOrientedDiffeomorphism sphereTwoProduct)) by
    exact inducedH₂_connectedSumOrientedDiffeomorphism g
      (identityOrientedDiffeomorphism sphereTwoProduct)]
  rw [connectedSumH₂Map_apply]
  rw [inducedH₂_identityOrientedDiffeomorphism]
  apply congrArg₂ connectedSumMarking
  · change
      G (A (stabilizedMarking X alpha n)) =
        stabilizedMarking Y (f alpha) n
    change
      G (G.toAddEquiv.symm (B (stabilizedMarking X alpha n))) =
        stabilizedMarking Y (f alpha) n
    rw [G.toAddEquiv.apply_symm_apply]
    exact stabilizedIntersectionFormIsometry_apply_marking f alpha n
  · rfl

end

end TwistedYetter.StableNoGo
