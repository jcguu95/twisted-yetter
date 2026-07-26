import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import TwistedYetter.Kirby.H2BasisMarkedEvaluator

/-!
# Integral cycle bases for handle-chain second homology

The earlier `H2BasisRealization` is a useful normal-form object, but it asks
for every integral homology basis vector to be the unit vector of one
two-handle.  That is extra Kirby geometry, not a consequence of freeness of
`H₂`.

This module separates the two statements.

* `IntegralH2.CycleBasis` only assumes that the handle-chain `H₂` is a finite
  free abelian group.
* The quotient map from degree-two cycles onto homology is an epimorphism in
  `ModuleCat`, hence a surjective function.  We use that theorem to lift each
  homology basis vector to an actual degree-two cycle.
* The marked cycle for `alpha : H₂` is the corresponding integral linear
  combination, and Lean proves that its homology class is exactly `alpha`.

The lift is deliberately not called canonical.  Two choices can differ by a
degree-three boundary, and the raw twisted cycle-colour expression is not
known to agree on such choices.  Choice independence must come from an
explicit cancellation-safe Kirby movie, not from this algebraic construction.
-/

namespace TwistedYetter.Kirby.IntegralH2

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.H2BasisMarkedEvaluator.CanonicalPresentation
open TwistedYetter.Kirby.KirbyCompleteness

universe uH uM

/-- The integral unit vector at `index`. -/
def coordinateUnit (rank : Nat) (index coordinate : Fin rank) : ℤ :=
  if coordinate = index then 1 else 0

/-- Our readable unit-vector definition agrees with Mathlib's `Pi.single`. -/
theorem coordinateUnit_eq_single
    (rank : Nat) (index : Fin rank) :
    coordinateUnit rank index =
      Pi.single (M := fun _ => ℤ) index 1 := by
  funext coordinate
  simp [coordinateUnit, Pi.single_apply, eq_comm]

/-- Every finite integral vector is the sum of its unit coordinates. -/
theorem eq_sum_coordinateUnit
    (rank : Nat) (vector : Fin rank → ℤ) :
    vector =
      ∑ index, vector index • coordinateUnit rank index := by
  simp_rw [coordinateUnit_eq_single]
  exact pi_eq_sum_univ' vector

/-- A linear map is determined by its values on integral unit vectors. -/
theorem linearMap_apply_eq_sum_coordinateUnit
    {M : Type uM} [AddCommGroup M] [Module ℤ M]
    (rank : Nat)
    (linear : (Fin rank → ℤ) →ₗ[ℤ] M)
    (vector : Fin rank → ℤ) :
    linear vector =
      ∑ index, vector index • linear (coordinateUnit rank index) := by
  simpa only [map_sum, map_zsmul] using
    congrArg linear (eq_sum_coordinateUnit rank vector)

/--
An integral basis of handle-chain `H₂`, together with actual cycle lifts.

Unlike `H2BasisRealization`, the lifted cycles may use arbitrary integral
linear combinations of two-handles.  No selected-handle or zero-on-all-other-
handles statement is included.
-/
structure CycleBasis
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2) where
  rank : Nat
  coordinates :
    presentation.topology.handleChain.SecondHomology ≃+
      (Fin rank → ℤ)
  basisCycle :
    Fin rank → presentation.DegreeTwoCycle
  basis_homology_coordinates :
    (index coordinate : Fin rank) →
      coordinates
          (presentation.topology.handleChain.complex.homologyπ 2
            (basisCycle index))
          coordinate =
        coordinateUnit rank index coordinate

namespace CycleBasis

/-- Integral linear combination of the chosen cycle lifts. -/
noncomputable def cycleLinearMap
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (basis : CycleBasis presentation) :
    (Fin basis.rank → ℤ) →ₗ[ℤ] presentation.DegreeTwoCycle :=
  Fintype.linearCombination ℤ basis.basisCycle

/-- Applying the cycle linear map is the expected finite sum. -/
theorem cycleLinearMap_apply
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (basis : CycleBasis presentation)
    (coefficients : Fin basis.rank → ℤ) :
    basis.cycleLinearMap coefficients =
      ∑ index, coefficients index • basis.basisCycle index :=
  by
    change
      (Fintype.linearCombination ℤ basis.basisCycle) coefficients =
        ∑ index, coefficients index • basis.basisCycle index
    rw [Fintype.linearCombination_apply]
    apply Finset.sum_congr rfl
    intro index _
    exact Int.cast_smul_eq_zsmul ℤ
      (coefficients index) (basis.basisCycle index)

/--
The homology coordinates of an arbitrary integral combination of the lifted
basis cycles are exactly its coefficients.
-/
theorem cycleLinearMap_homology_coordinates
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (basis : CycleBasis presentation)
    (coefficients : Fin basis.rank → ℤ)
    (coordinate : Fin basis.rank) :
    basis.coordinates
        (presentation.topology.handleChain.complex.homologyπ 2
          (basis.cycleLinearMap coefficients))
        coordinate =
      coefficients coordinate := by
  classical
  rw [basis.cycleLinearMap_apply]
  simp [basis.basis_homology_coordinates, coordinateUnit]

/--
Vector form of `cycleLinearMap_homology_coordinates`: taking the homology
class of a lifted integral combination recovers the complete coefficient
vector.
-/
theorem cycleLinearMap_homology_coordinates_eq
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (basis : CycleBasis presentation)
    (coefficients : Fin basis.rank → ℤ) :
    basis.coordinates
        (presentation.topology.handleChain.complex.homologyπ 2
          (basis.cycleLinearMap coefficients)) =
      coefficients := by
  funext coordinate
  exact basis.cycleLinearMap_homology_coordinates
    coefficients coordinate

/--
Every specified integral homology basis vector has an actual cycle lift.

This uses only the categorical epimorphism theorem for `homologyπ` and the
fact that epis in `ModuleCat` are surjective.  It does not choose a handle
normal form.
-/
noncomputable def liftedBasisCycle
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    (rank : Nat)
    (coordinates :
      presentation.topology.handleChain.SecondHomology ≃+
        (Fin rank → ℤ))
    (index : Fin rank) :
    presentation.DegreeTwoCycle :=
  Classical.choose
    ((ModuleCat.epi_iff_surjective
      (presentation.topology.handleChain.complex.homologyπ 2)).mp
        inferInstance
      (coordinates.symm (coordinateUnit rank index)))

/-- The chosen lift represents the requested integral basis class. -/
theorem liftedBasisCycle_class
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    (rank : Nat)
    (coordinates :
      presentation.topology.handleChain.SecondHomology ≃+
        (Fin rank → ℤ))
    (index : Fin rank) :
    presentation.topology.handleChain.complex.homologyπ 2
        (liftedBasisCycle presentation rank coordinates index) =
      coordinates.symm (coordinateUnit rank index) :=
  Classical.choose_spec
    ((ModuleCat.epi_iff_surjective
      (presentation.topology.handleChain.complex.homologyπ 2)).mp
        inferInstance
      (coordinates.symm (coordinateUnit rank index)))

/--
Construct an integral cycle basis from a certified finite-free coordinate
system on `H₂`.

The construction is noncomputable because it chooses preimages under the
homology quotient.  The resulting proof object records the chosen cycles.
-/
noncomputable def ofFreeCoordinates
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    (rank : Nat)
    (coordinates :
      presentation.topology.handleChain.SecondHomology ≃+
        (Fin rank → ℤ)) :
    CycleBasis presentation where
  rank := rank
  coordinates := coordinates
  basisCycle :=
    liftedBasisCycle presentation rank coordinates
  basis_homology_coordinates index coordinate := by
    rw [liftedBasisCycle_class]
    simp

/--
The marked degree-two cycle obtained by expanding `alpha` in the chosen
integral homology basis.
-/
noncomputable def markedCycle
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (basis : CycleBasis presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    presentation.DegreeTwoCycle :=
  basis.cycleLinearMap (basis.coordinates alpha)

/-- The integral marked cycle represents exactly the public `H₂` class. -/
theorem markedCycle_class
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (basis : CycleBasis presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    presentation.topology.handleChain.complex.homologyπ 2
        (basis.markedCycle alpha) =
      alpha := by
  classical
  apply basis.coordinates.injective
  funext coordinate
  exact basis.cycleLinearMap_homology_coordinates
    (basis.coordinates alpha) coordinate

/--
Re-express a cycle basis by an arbitrary integral linear automorphism.

The new basis cycles are literal integral combinations of the old ones.  This
is a change of coordinates inside the same lifted cycle submodule, not a
change by a degree-three boundary.
-/
noncomputable def rebase
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (basis : CycleBasis presentation)
    (change :
      (Fin basis.rank → ℤ) ≃ₗ[ℤ] (Fin basis.rank → ℤ)) :
    CycleBasis presentation where
  rank := basis.rank
  coordinates := basis.coordinates.trans change.toAddEquiv
  basisCycle := fun index =>
    basis.cycleLinearMap
      (change.symm (coordinateUnit basis.rank index))
  basis_homology_coordinates index coordinate := by
    change
      change
          (basis.coordinates
            (presentation.topology.handleChain.complex.homologyπ 2
              (basis.cycleLinearMap
                (change.symm
                  (coordinateUnit basis.rank index)))))
          coordinate =
        coordinateUnit basis.rank index coordinate
    rw [basis.cycleLinearMap_homology_coordinates_eq]
    exact congrFun
      (change.apply_symm_apply (coordinateUnit basis.rank index))
      coordinate

/--
An arbitrary unimodular integral rebasing leaves the actual marked cycle
unchanged, not merely homologous.
-/
theorem rebase_markedCycle
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (basis : CycleBasis presentation)
    (change :
      (Fin basis.rank → ℤ) ≃ₗ[ℤ] (Fin basis.rank → ℤ))
    (alpha : presentation.topology.handleChain.SecondHomology) :
    (basis.rebase change).markedCycle alpha =
      basis.markedCycle alpha := by
  classical
  let oldCoordinates := basis.coordinates alpha
  change
    (basis.rebase change).cycleLinearMap
        (change oldCoordinates) =
      basis.cycleLinearMap oldCoordinates
  rw [(basis.rebase change).cycleLinearMap_apply]
  change
    (∑ index,
      (change oldCoordinates) index •
        basis.cycleLinearMap
          (change.symm (coordinateUnit basis.rank index))) =
      basis.cycleLinearMap oldCoordinates
  calc
    _ =
        (basis.cycleLinearMap.comp change.symm.toLinearMap)
          (change oldCoordinates) := by
      symm
      exact linearMap_apply_eq_sum_coordinateUnit
        basis.rank
        (basis.cycleLinearMap.comp change.symm.toLinearMap)
        (change oldCoordinates)
    _ = basis.cycleLinearMap oldCoordinates := by
      change
        basis.cycleLinearMap (change.symm (change oldCoordinates)) =
          basis.cycleLinearMap oldCoordinates
      rw [change.symm_apply_apply]

/--
The old handle-supported realization is a special case of an integral cycle
basis.  This conversion does not assert that every integral cycle basis is
handle-supported.
-/
def ofHandleSupportedNormalForm
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (normalForm : H2BasisRealization presentation) :
    CycleBasis presentation where
  rank := normalForm.rank
  coordinates := normalForm.coordinates
  basisCycle := normalForm.basisCycle
  basis_homology_coordinates :=
    normalForm.basis_homology_coordinates

/-- The conversion preserves the marked cycle definition literally. -/
theorem ofHandleSupportedNormalForm_markedCycle
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (normalForm : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    (ofHandleSupportedNormalForm normalForm).markedCycle alpha =
      normalForm.markedCycle alpha := by
  rw [markedCycle, cycleLinearMap_apply]
  rfl

/--
A strict comparison of two cycle bases.

The required equality is between actual degree-two cycles, not merely their
homology classes and not their scalar evaluations.  This is strong enough to
be safe, but it intentionally does not cover bases whose lifts differ by an
uncontrolled degree-three boundary.
-/
structure StrictComparison
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (left right : CycleBasis presentation) where
  marked_cycle_eq :
    (alpha : presentation.topology.handleChain.SecondHomology) →
      left.markedCycle alpha = right.markedCycle alpha

/-- Every integral rebasing supplies a strict cycle-basis comparison. -/
noncomputable def rebaseStrictComparison
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation H2}
    (basis : CycleBasis presentation)
    (change :
      (Fin basis.rank → ℤ) ≃ₗ[ℤ] (Fin basis.rank → ℤ)) :
    StrictComparison (basis.rebase change) basis where
  marked_cycle_eq := basis.rebase_markedCycle change

end CycleBasis

end TwistedYetter.Kirby.IntegralH2
