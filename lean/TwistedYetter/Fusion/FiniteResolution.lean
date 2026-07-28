import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Finite linear resolutions for Kirby-colour encircling transport

This module makes the finite sums and dual-basis data used by graphical
insertion arguments explicit. It does not define a fusion category.
-/

namespace TwistedYetter.Fusion.FiniteResolution

open scoped BigOperators

universe uR uV uW uE uX uI uK

variable {R : Type uR}
variable {V : Type uV} {W : Type uW} {E : Type uE}
variable [CommSemiring R]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]
variable [AddCommMonoid E] [Module R E]

/--
A perfect pairing is recorded as an explicit linear equivalence from the
second space to the linear dual of the first.
-/
structure PerfectPairing (R : Type uR) (V : Type uV) (W : Type uW)
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W] where
  toDual : W ≃ₗ[R] Module.Dual R V

namespace PerfectPairing

/-- Evaluate the pairing, with the primal vector written first. -/
def pair (pairing : PerfectPairing R V W) (primal : V) (dual : W) : R :=
  pairing.toDual dual primal

@[simp]
theorem pair_add_left (pairing : PerfectPairing R V W)
    (left₁ left₂ : V) (right : W) :
    pairing.pair (left₁ + left₂) right =
      pairing.pair left₁ right + pairing.pair left₂ right :=
  (pairing.toDual right).map_add left₁ left₂

@[simp]
theorem pair_add_right (pairing : PerfectPairing R V W)
    (left : V) (right₁ right₂ : W) :
    pairing.pair left (right₁ + right₂) =
      pairing.pair left right₁ + pairing.pair left right₂ := by
  simp [pair]

@[simp]
theorem pair_smul_left (pairing : PerfectPairing R V W)
    (scalar : R) (left : V) (right : W) :
    pairing.pair (scalar • left) right =
      scalar * pairing.pair left right := by
  simp [pair]

@[simp]
theorem pair_smul_right (pairing : PerfectPairing R V W)
    (scalar : R) (left : V) (right : W) :
    pairing.pair left (scalar • right) =
      scalar * pairing.pair left right := by
  simp [pair]

end PerfectPairing

/--
A complete finite basis together with actual vectors in the paired space whose
pairing functionals are exactly the algebraic dual basis.
-/
structure DualBasisData
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (pairing : PerfectPairing R V W) where
  primal : Module.Basis ι R V
  dual : ι → W
  dual_eq : (i : ι) → pairing.toDual (dual i) = primal.dualBasis i

namespace DualBasisData

variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable {pairing : PerfectPairing R V W}

/-- Every basis has a uniquely corresponding family in a perfectly paired space. -/
noncomputable def ofBasis
    (pairing : PerfectPairing R V W)
    (basis : Module.Basis ι R V) :
    DualBasisData (ι := ι) pairing where
  primal := basis
  dual i := pairing.toDual.symm (basis.dualBasis i)
  dual_eq i := pairing.toDual.apply_symm_apply (basis.dualBasis i)

/-- The recorded vectors satisfy the Kronecker dual-basis equation. -/
theorem pair_primal_dual
    (data : DualBasisData (ι := ι) pairing) (i j : ι) :
    pairing.pair (data.primal i) (data.dual j) =
      if i = j then 1 else 0 := by
  classical
  rw [PerfectPairing.pair, data.dual_eq]
  exact data.primal.dualBasis_apply_self j i

/-- Coefficient of a vector in the recorded dual basis. -/
def coefficient
    (data : DualBasisData (ι := ι) pairing) (vector : V) (i : ι) : R :=
  pairing.pair vector (data.dual i)

/-- Pairing with the recorded dual vector is the ordinary basis coordinate. -/
theorem coefficient_eq_repr
    (data : DualBasisData (ι := ι) pairing) (vector : V) (i : ι) :
    data.coefficient vector i = data.primal.repr vector i := by
  rw [coefficient, PerfectPairing.pair, data.dual_eq]
  exact data.primal.dualBasis_apply i vector

/--
Finite insertion/reconstruction: the sum of all dual-basis channels is the
original vector.
-/
theorem reconstruct
    (data : DualBasisData (ι := ι) pairing) (vector : V) :
    ∑ i, data.coefficient vector i • data.primal i = vector := by
  simpa only [data.coefficient_eq_repr] using data.primal.sum_repr vector

/-- The inverse-insertion direction is the symmetric reconstruction equality. -/
theorem inverse_reconstruct
    (data : DualBasisData (ι := ι) pairing) (vector : V) :
    vector = ∑ i, data.coefficient vector i • data.primal i :=
  (data.reconstruct vector).symm

end DualBasisData

/--
A finite, proof-carrying linear resolution. It is a reusable certificate, not
a proposition inferred from a family name.
-/
structure LinearResolution
    (R : Type uR) (E : Type uE) (ι : Type uI)
    [CommSemiring R] [AddCommMonoid E] [Module R E] [Fintype ι] where
  term : ι → E
  target : E
  sound : ∑ i, term i = target

namespace LinearResolution

variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable {κ : Type uK} [Fintype κ]

/-- Reindex a resolution without changing its target or finite sum. -/
def reindex (resolution : LinearResolution R E ι) (equiv : κ ≃ ι) :
    LinearResolution R E κ where
  term k := resolution.term (equiv k)
  target := resolution.target
  sound := (equiv.sum_comp resolution.term).trans resolution.sound

/-- A linear map carries a proved resolution to another proved resolution. -/
def map {E' : Type*} [AddCommMonoid E'] [Module R E']
    (resolution : LinearResolution R E ι)
    (linearMap : E →ₗ[R] E') :
    LinearResolution R E' ι where
  term i := linearMap (resolution.term i)
  target := linearMap resolution.target
  sound := by
    simpa using congrArg linearMap resolution.sound

/-- Turn dual-basis reconstruction into a first-class resolution certificate. -/
noncomputable def ofDualBasis
    {pairing : PerfectPairing R V W}
    (data : DualBasisData (ι := ι) pairing)
    (vector : V) :
    LinearResolution R V ι where
  term i := data.coefficient vector i • data.primal i
  target := vector
  sound := data.reconstruct vector

end LinearResolution

/-- A finite dimension-weighted family, such as a formal Kirby colour. -/
structure WeightedFamily
    (R : Type uR) (ι : Type uI) (X : Type uX) where
  item : ι → X
  weight : ι → R

namespace WeightedFamily

variable {ι : Type uI} [Fintype ι]
variable {κ : Type uK} [Fintype κ]
variable {X : Type uX}

/-- Evaluate a weighted family in any module. -/
def total (family : WeightedFamily R ι X) (evaluate : X → E) : E :=
  ∑ i, family.weight i • evaluate (family.item i)

/-- Reindex a family by an explicit equivalence of finite index types. -/
def reindex (family : WeightedFamily R ι X) (equiv : κ ≃ ι) :
    WeightedFamily R κ X where
  item k := family.item (equiv k)
  weight k := family.weight (equiv k)

/-- Reindexing cannot silently change the weighted total. -/
theorem total_reindex
    (family : WeightedFamily R ι X)
    (equiv : κ ≃ ι)
    (evaluate : X → E) :
    (family.reindex equiv).total evaluate = family.total evaluate := by
  exact equiv.sum_comp (fun i => family.weight i • evaluate (family.item i))

end WeightedFamily

end TwistedYetter.Fusion.FiniteResolution
