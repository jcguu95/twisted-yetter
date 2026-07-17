import TwistedYetter.Fusion.PairingTransport

/-!
# Finite biorthogonal families

A pivotal functor need not be full.  Therefore the image of a basis in the
source category need not be a basis of the entire target Hom space.  The
generalized sliding proof only needs the weaker and correct statement that
the two finite image families remain biorthogonal.
-/

namespace TwistedYetter.Fusion

open TwistedYetter.Fusion.FiniteResolution

universe uR uV uW uV' uW' uV'' uW'' uI

variable {R : Type uR} [CommSemiring R]
variable {V : Type uV} {W : Type uW}
variable {V' : Type uV'} {W' : Type uW'}
variable {V'' : Type uV''} {W'' : Type uW''}
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]
variable [AddCommMonoid V'] [Module R V']
variable [AddCommMonoid W'] [Module R W']
variable [AddCommMonoid V''] [Module R V'']
variable [AddCommMonoid W''] [Module R W'']

/-- A finite pair of families with an exact Kronecker pairing. -/
structure BiorthogonalFamily
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (pairing : PerfectPairing R V W) where
  primal : ι → V
  dual : ι → W
  pair_eq : (i j : ι) →
    pairing.pair (primal i) (dual j) = if i = j then 1 else 0

namespace BiorthogonalFamily

variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable {source : PerfectPairing R V W}
variable {target : PerfectPairing R V' W'}

/-- Forget spanning while retaining the exact duality equations. -/
noncomputable def ofDualBasisData (data : DualBasisData (ι := ι) source) :
    BiorthogonalFamily (ι := ι) source where
  primal := data.primal
  dual := data.dual
  pair_eq := data.pair_primal_dual

end BiorthogonalFamily

/--
A pairing-preserving map does not require either linear map to be invertible.
This is the correct interface for the image on Hom spaces of a non-full
pivotal functor.
-/
structure PairingMap
    (source : PerfectPairing R V W)
    (target : PerfectPairing R V' W') where
  primalMap : V →ₗ[R] V'
  dualMap : W →ₗ[R] W'
  preserves_pairing :
    (primal : V) → (dual : W) →
      target.pair (primalMap primal) (dualMap dual) =
        source.pair primal dual

namespace PairingMap

variable {source : PerfectPairing R V W}
variable {middle : PerfectPairing R V' W'}
variable {target : PerfectPairing R V'' W''}
variable {ι : Type uI} [Fintype ι] [DecidableEq ι]

/-- Pairing-preserving maps compose without a fullness assumption. -/
def comp
    (first : PairingMap source middle)
    (second : PairingMap middle target) :
    PairingMap source target where
  primalMap := second.primalMap.comp first.primalMap
  dualMap := second.dualMap.comp first.dualMap
  preserves_pairing primal dual := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [second.preserves_pairing, first.preserves_pairing]

/-- A pairing transport gives a pairing map by forgetting invertibility. -/
def ofTransport
    (transport : PairingTransport source middle) :
    PairingMap source middle where
  primalMap := transport.primalEquiv
  dualMap := transport.dualEquiv
  preserves_pairing := transport.preserves_pairing

/-- Map both sides of a finite biorthogonal family. -/
def mapFamily
    (map : PairingMap source middle)
    (family : BiorthogonalFamily (ι := ι) source) :
    BiorthogonalFamily (ι := ι) middle where
  primal i := map.primalMap (family.primal i)
  dual i := map.dualMap (family.dual i)
  pair_eq i j := by
    rw [map.preserves_pairing]
    exact family.pair_eq i j

/-- The mapped family has the exact target Kronecker pairing. -/
theorem mapFamily_pair_eq
    (map : PairingMap source middle)
    (family : BiorthogonalFamily (ι := ι) source)
    (i j : ι) :
    middle.pair
        ((map.mapFamily family).primal i)
        ((map.mapFamily family).dual j) =
      if i = j then 1 else 0 :=
  (map.mapFamily family).pair_eq i j

end PairingMap

end TwistedYetter.Fusion
