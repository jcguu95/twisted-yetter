import TwistedYetter.Kirby.DualHandleConvention

/-!
# Reduce arbitrary dual boundaries to dotted-handle generators

The degree-three chains in the evaluator's dual handle complex are integral
linear combinations of the basis dual to the primal one-handles.  This file
proves the finite algebraic reduction needed by the graphical compiler:

* every chain is the sum of its individual coordinates;
* adding a sum of boundaries is successive boundary addition; and
* invariance for every integral multiple of every basis generator implies
  invariance under every degree-three boundary.

No category, diagram evaluation, or equality of invariant values is assumed.
The remaining local theorem may therefore be checked once for each primal
dotted one-handle and then lifted here to arbitrary representatives.
-/

namespace TwistedYetter.Kirby.DualBoundaryGeneratorReduction

open scoped BigOperators
open TwistedYetter.Kirby.BoundaryDerivedHandleChain

/-- One coordinate of an integral handle vector, retaining its coefficient. -/
def coordinateTerm {count : Nat}
    (vector : FreeHandleGroup count) (index : Fin count) :
    FreeHandleGroup count :=
  fun coordinate => if coordinate = index then vector index else 0

/-- Every finite handle vector is the sum of its coordinate terms. -/
theorem sum_coordinateTerm {count : Nat}
    (vector : FreeHandleGroup count) :
    (∑ index, coordinateTerm vector index) = vector := by
  classical
  funext coordinate
  simp [coordinateTerm]

variable {h1 h2 h3 : Nat}

/-- Add the degree-three boundary of `chain` to one degree-two cycle. -/
def addBoundary
    (data : ClosedHandleBoundaryData h1 h2 h3)
    (cycle : data.Cycles)
    (chain : FreeHandleGroup h3) : data.Cycles :=
  cycle + data.d3ToCycles chain

@[simp] theorem addBoundary_zero
    (data : ClosedHandleBoundaryData h1 h2 h3)
    (cycle : data.Cycles) :
    addBoundary data cycle 0 = cycle := by
  simp [addBoundary]

/-- Addition of chains becomes successive addition of their boundaries. -/
theorem addBoundary_add
    (data : ClosedHandleBoundaryData h1 h2 h3)
    (cycle : data.Cycles)
    (first second : FreeHandleGroup h3) :
    addBoundary data cycle (first + second) =
      addBoundary data (addBoundary data cycle first) second := by
  simp [addBoundary, add_left_comm, add_comm]

/--
The exact local denominator: one basis dual-three-handle and one arbitrary
integer coefficient, applied in front of an arbitrary existing cycle.
-/
def IntegralGeneratorBoundaryInvariant
    (data : ClosedHandleBoundaryData h1 h2 h3)
    {V : Type*}
    (evaluation : data.Cycles → V) : Prop :=
  ∀ (cycle : data.Cycles) (index : Fin h3) (coefficient : ℤ),
    evaluation
        (addBoundary data cycle
          (coordinateTerm (fun _ => coefficient) index)) =
      evaluation cycle

/-- Invariance for a finite subset of coordinate generators. -/
theorem sum_over_subset_invariant
    (data : ClosedHandleBoundaryData h1 h2 h3)
    {V : Type*}
    (evaluation : data.Cycles → V)
    (generatorLaw : IntegralGeneratorBoundaryInvariant data evaluation)
    (chain : FreeHandleGroup h3)
    (cycle : data.Cycles)
    (subset : Finset (Fin h3)) :
    evaluation
        (addBoundary data cycle
          (∑ index ∈ subset, coordinateTerm chain index)) =
      evaluation cycle := by
  classical
  induction subset using Finset.induction_on generalizing cycle with
  | empty => simp
  | @insert index subset indexNotMem ih =>
      rw [Finset.sum_insert indexNotMem]
      rw [addBoundary_add]
      rw [ih]
      exact generatorLaw cycle index (chain index)

/-- Local integral generator invariance implies arbitrary-boundary invariance. -/
theorem integral_generators_imply_all_boundaries
    (data : ClosedHandleBoundaryData h1 h2 h3)
    {V : Type*}
    (evaluation : data.Cycles → V)
    (generatorLaw : IntegralGeneratorBoundaryInvariant data evaluation)
    (cycle : data.Cycles)
    (chain : FreeHandleGroup h3) :
    evaluation (addBoundary data cycle chain) = evaluation cycle := by
  rw [← sum_coordinateTerm chain]
  simpa using
    sum_over_subset_invariant data evaluation generatorLaw chain cycle Finset.univ

/-- Two cycles differing by a displayed boundary receive the same value. -/
theorem equal_mod_boundary
    (data : ClosedHandleBoundaryData h1 h2 h3)
    {V : Type*}
    (evaluation : data.Cycles → V)
    (generatorLaw : IntegralGeneratorBoundaryInvariant data evaluation)
    (left right : data.Cycles)
    (chain : FreeHandleGroup h3)
    (equation : left = addBoundary data right chain) :
    evaluation left = evaluation right := by
  rw [equation]
  exact integral_generators_imply_all_boundaries
    data evaluation generatorLaw right chain

/-- Machine-visible status of the finite-generator reduction. -/
def currentStatus : String :=
  "PASS_INTEGRAL_DUAL_D3_GENERATORS_IMPLY_ALL_BOUNDARIES"

end TwistedYetter.Kirby.DualBoundaryGeneratorReduction
