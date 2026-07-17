import TwistedYetter.Fusion.FiniteResolution

/-!
# Pairing-preserving transport of finite resolutions

This module isolates the linear-algebraic core of mate transport. A future
pivotal-category layer must construct `PairingTransport` from actual mate maps
and prove `preserves_pairing`; that property is not assumed globally here.
-/

namespace TwistedYetter.Fusion

open scoped BigOperators
open TwistedYetter.Fusion.FiniteResolution

universe uR uV uW uV' uW' uI

variable {R : Type uR}
variable {V : Type uV} {W : Type uW}
variable {V' : Type uV'} {W' : Type uW'}
variable [CommSemiring R]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]
variable [AddCommMonoid V'] [Module R V']
variable [AddCommMonoid W'] [Module R W']

/--
Two linear equivalences form a pairing transport only when the target pairing
of their images is exactly the source pairing. This is the obligation that a
future pivotal mate construction must discharge.
-/
structure PairingTransport
    (source : PerfectPairing R V W)
    (target : PerfectPairing R V' W') where
  primalEquiv : V ≃ₗ[R] V'
  dualEquiv : W ≃ₗ[R] W'
  preserves_pairing :
    (primal : V) → (dual : W) →
      target.pair (primalEquiv primal) (dualEquiv dual) =
        source.pair primal dual

namespace PairingTransport

variable {source : PerfectPairing R V W}
variable {target : PerfectPairing R V' W'}
variable {ι : Type uI} [Fintype ι] [DecidableEq ι]

/-- Transport the primal basis along the supplied linear equivalence. -/
noncomputable def primalBasis
    (transport : PairingTransport source target)
    (data : DualBasisData (ι := ι) source) :
    Module.Basis ι R V' :=
  data.primal.map transport.primalEquiv

/-- Transport the actual vectors representing the source dual basis. -/
def dualVector
    (transport : PairingTransport source target)
    (data : DualBasisData (ι := ι) source)
    (i : ι) : W' :=
  transport.dualEquiv (data.dual i)

/--
The transported primal and dual vectors still satisfy the Kronecker pairing
equations. No change-of-basis scalar may be omitted from this theorem.
-/
theorem pair_primal_dual
    (transport : PairingTransport source target)
    (data : DualBasisData (ι := ι) source)
    (i j : ι) :
    target.pair
        (transport.primalBasis data i)
        (transport.dualVector data j) =
      if i = j then 1 else 0 := by
  rw [primalBasis, Module.Basis.map_apply, dualVector]
  rw [transport.preserves_pairing]
  exact data.pair_primal_dual i j

/--
The transported dual vector is the canonical vector paired with the transported
basis. This packages uniqueness, not merely the pointwise Kronecker equations.
-/
theorem dualVector_eq_canonical
    (transport : PairingTransport source target)
    (data : DualBasisData (ι := ι) source)
    (i : ι) :
    transport.dualVector data i =
      (DualBasisData.ofBasis target (transport.primalBasis data)).dual i := by
  apply target.toDual.injective
  apply (transport.primalBasis data).ext
  intro j
  change target.pair
      (transport.primalBasis data j)
      (transport.dualVector data i) =
    target.pair
      (transport.primalBasis data j)
      ((DualBasisData.ofBasis target (transport.primalBasis data)).dual i)
  calc
    target.pair
          (transport.primalBasis data j)
          (transport.dualVector data i) =
        if j = i then 1 else 0 :=
      transport.pair_primal_dual data j i
    _ =
        target.pair
          (transport.primalBasis data j)
          ((DualBasisData.ofBasis target
            (transport.primalBasis data)).dual i) :=
      ((DualBasisData.ofBasis target
        (transport.primalBasis data)).pair_primal_dual j i).symm

/--
The source dual-basis package transported as actual vectors, together with the
proof that those vectors are the target algebraic dual basis.
-/
noncomputable def dualBasisData
    (transport : PairingTransport source target)
    (data : DualBasisData (ι := ι) source) :
    DualBasisData (ι := ι) target where
  primal := transport.primalBasis data
  dual := transport.dualVector data
  dual_eq i := by
    rw [transport.dualVector_eq_canonical data i]
    exact
      (DualBasisData.ofBasis target
        (transport.primalBasis data)).dual_eq i

/-- Pairing coordinates are unchanged by a pairing-preserving transport. -/
theorem coefficient_eq
    (transport : PairingTransport source target)
    (data : DualBasisData (ι := ι) source)
    (vector : V)
    (i : ι) :
    (transport.dualBasisData data).coefficient
        (transport.primalEquiv vector) i =
      data.coefficient vector i := by
  exact transport.preserves_pairing vector (data.dual i)

/--
Each transported insertion channel agrees with the image of the corresponding
source channel.
-/
theorem channel_eq
    (transport : PairingTransport source target)
    (data : DualBasisData (ι := ι) source)
    (vector : V)
    (i : ι) :
    (transport.dualBasisData data).coefficient
          (transport.primalEquiv vector) i •
        (transport.dualBasisData data).primal i =
      transport.primalEquiv
        (data.coefficient vector i • data.primal i) := by
  rw [transport.coefficient_eq]
  simp [dualBasisData, primalBasis]

/--
The complete transported channel sum reconstructs the transported vector. This
is the finite-resolution calculation used after mate change-of-variables.
-/
theorem reconstruct
    (transport : PairingTransport source target)
    (data : DualBasisData (ι := ι) source)
    (vector : V) :
    ∑ i,
        (transport.dualBasisData data).coefficient
            (transport.primalEquiv vector) i •
          (transport.dualBasisData data).primal i =
      transport.primalEquiv vector :=
  (transport.dualBasisData data).reconstruct (transport.primalEquiv vector)

/--
The mapped source resolution and the target dual-basis resolution have equal
terms and the same target. This is only the linear skeleton of generalized
sliding, not the graphical or fusion-category theorem.
-/
theorem mapped_resolution_term_eq
    (transport : PairingTransport source target)
    (data : DualBasisData (ι := ι) source)
    (vector : V)
    (i : ι) :
    ((LinearResolution.ofDualBasis data vector).map
          transport.primalEquiv.toLinearMap).term i =
      (LinearResolution.ofDualBasis
          (transport.dualBasisData data)
          (transport.primalEquiv vector)).term i :=
  (transport.channel_eq data vector i).symm

end PairingTransport

end TwistedYetter.Fusion
