import TwistedYetter.Kirby.BoundaryDerivedHandleChain
import TwistedYetter.Kirby.KirbyCancellation

/-!
# Dual handle convention for the Tham 5.11 evaluator

The surgery diagrams evaluated in this project are read upside down.  A
primal handle of index `k` is therefore a Tham handle of index `4 - k`:

* primal 1-handles are Tham 3-handles (the vacuum projectors);
* primal 2-handles remain Tham 2-handles; and
* primal 3-handles are Tham 1-handles (the dimension-normalization maps).

Consequently, the degree-two cycles used to colour link components belong to
the dual handle complex.  If the primal middle differential is

`C3 --d3--> C2 --d2--> C1`,

then the evaluator uses

`C1 --transpose(d2)--> C2 --transpose(d3)--> C3`.

This file makes that convention executable.  It also proves the two local
regression checks that distinguish the primal and dual readings:

* a primal cancelling 2--3 pair becomes a dual cancelling 1--2 pair, so its
  new two-handle coefficient is forced to zero by the cycle condition;
* a primal cancelling 1--2 pair becomes a dual cancelling 2--3 pair, so its
  two-handle generator is a boundary and is handled by the Tham `k = 3`
  vacuum projector on the primal dotted component.
-/

namespace TwistedYetter.Kirby.DualHandleConvention

open scoped BigOperators
open TwistedYetter.Kirby.BoundaryDerivedHandleChain
open TwistedYetter.Kirby.KirbyCancellation

/-- Compatibility name for the core handle-count reversal. -/
abbrev dualCounts (counts : HandleCounts) : HandleCounts :=
  counts.turnedOver

@[simp] theorem dualCounts_h0 (counts : HandleCounts) :
    (dualCounts counts).h0 = counts.h4 := rfl

@[simp] theorem dualCounts_h1 (counts : HandleCounts) :
    (dualCounts counts).h1 = counts.h3 := rfl

@[simp] theorem dualCounts_h2 (counts : HandleCounts) :
    (dualCounts counts).h2 = counts.h2 := rfl

@[simp] theorem dualCounts_h3 (counts : HandleCounts) :
    (dualCounts counts).h3 = counts.h1 := rfl

@[simp] theorem dualCounts_h4 (counts : HandleCounts) :
    (dualCounts counts).h4 = counts.h0 := rfl

/-- Turning a handle decomposition over twice restores every handle count. -/
@[simp] theorem dualCounts_involutive (counts : HandleCounts) :
    dualCounts (dualCounts counts) = counts := by
  exact counts.turnedOver_involutive

/-- A primal 1--2 birth is a dual 2--3 birth. -/
theorem dualCounts_addOneTwo (counts : HandleCounts) :
    dualCounts counts.addOneTwo = (dualCounts counts).addTwoThree :=
  counts.turnedOver_addOneTwo

/-- A primal 2--3 birth is a dual 1--2 birth. -/
theorem dualCounts_addTwoThree (counts : HandleCounts) :
    dualCounts counts.addTwoThree = (dualCounts counts).addOneTwo :=
  counts.turnedOver_addTwoThree

/-- The integral coordinate pairing in a fixed handle basis. -/
def coordinatePairing {count : Nat}
    (left right : FreeHandleGroup count) : ℤ :=
  ∑ index, left index * right index

/-- Integral unit vector in a handle basis. -/
def coordinateUnit (count : Nat) (index coordinate : Fin count) : ℤ :=
  if coordinate = index then 1 else 0

/-- Pairing a unit vector with a coordinate vector reads that coordinate. -/
theorem coordinatePairing_unit_left
    (count : Nat) (index : Fin count)
    (vector : FreeHandleGroup count) :
    coordinatePairing (coordinateUnit count index) vector = vector index := by
  classical
  simp [coordinatePairing, coordinateUnit, eq_comm]

/--
Proof-carrying transpose data for the middle part of a primal handle chain.

The two adjointness equations determine the dual maps in the displayed
finite bases.  The dual chain condition is derived below from these equations
and the primal identity `d2 * d3 = 0`; it is not an additional field.
-/
structure DualBoundaryCertificate
    {h1 h2 h3 : Nat}
    (primal : ClosedHandleBoundaryData h1 h2 h3) where
  dualD2 : FreeHandleGroup h2 →+ FreeHandleGroup h3
  dualD3 : FreeHandleGroup h1 →+ FreeHandleGroup h2
  dualD2_adjoint :
    (threeChain : FreeHandleGroup h3) →
    (twoChain : FreeHandleGroup h2) →
      coordinatePairing (primal.d3 threeChain) twoChain =
        coordinatePairing threeChain (dualD2 twoChain)
  dualD3_adjoint :
    (twoChain : FreeHandleGroup h2) →
    (oneChain : FreeHandleGroup h1) →
      coordinatePairing (primal.d2 twoChain) oneChain =
        coordinatePairing twoChain (dualD3 oneChain)

namespace DualBoundaryCertificate

/-- The transposed middle maps square to zero, derived from primal `d^2=0`. -/
theorem dualD2_dualD3_zero
    {h1 h2 h3 : Nat}
    {primal : ClosedHandleBoundaryData h1 h2 h3}
    (certificate : DualBoundaryCertificate primal)
    (oneChain : FreeHandleGroup h1) :
    certificate.dualD2 (certificate.dualD3 oneChain) = 0 := by
  funext index
  calc
    certificate.dualD2 (certificate.dualD3 oneChain) index =
        coordinatePairing (coordinateUnit h3 index)
          (certificate.dualD2 (certificate.dualD3 oneChain)) :=
      (coordinatePairing_unit_left h3 index _).symm
    _ = coordinatePairing
          (primal.d3 (coordinateUnit h3 index))
          (certificate.dualD3 oneChain) :=
      (certificate.dualD2_adjoint
        (coordinateUnit h3 index) (certificate.dualD3 oneChain)).symm
    _ = coordinatePairing
          (primal.d2 (primal.d3 (coordinateUnit h3 index)))
          oneChain :=
      (certificate.dualD3_adjoint
        (primal.d3 (coordinateUnit h3 index)) oneChain).symm
    _ = 0 := by
      rw [primal.d2_d3_zero]
      simp [coordinatePairing]
    _ = (0 : FreeHandleGroup h3) index := rfl

/-- The actual degree `3 -> 2 -> 1` boundary data seen by the evaluator. -/
def dualBoundaryData
    {h1 h2 h3 : Nat}
    {primal : ClosedHandleBoundaryData h1 h2 h3}
    (certificate : DualBoundaryCertificate primal) :
    ClosedHandleBoundaryData h3 h2 h1 where
  d2 := certificate.dualD2
  d3 := certificate.dualD3
  d2_d3_zero := certificate.dualD2_dualD3_zero

end DualBoundaryCertificate

/-- Identity homomorphism on one integral handle coordinate. -/
def singletonIdentity : FreeHandleGroup 1 →+ FreeHandleGroup 1 :=
  AddMonoidHom.id _

/-- Zero map out of a missing handle degree. -/
def fromNoHandles (count : Nat) : FreeHandleGroup 0 →+ FreeHandleGroup count :=
  0

/-- Zero map into a missing handle degree. -/
def toNoHandles (count : Nat) : FreeHandleGroup count →+ FreeHandleGroup 0 :=
  0

/--
Dual middle complex for a primal cancelling 2--3 pair:

`0 -> Z --id--> Z`.

The evaluator's degree-two cycle condition is therefore `x = 0`.
-/
def dualOfPrimalTwoThreePair : ClosedHandleBoundaryData 1 1 0 where
  d2 := singletonIdentity
  d3 := fromNoHandles 1
  d2_d3_zero := by simp [singletonIdentity, fromNoHandles]

/-- Every legal evaluator cycle on a primal cancelling 2--3 pair is zero. -/
theorem primalTwoThree_dualCycle_forced_zero
    (cycle : dualOfPrimalTwoThreePair.Cycles) :
    (cycle : FreeHandleGroup 1) = 0 := by
  exact cycle.property

/-- In particular, coefficient one cannot be silently coloured as a cycle. -/
theorem primalTwoThree_coefficientOne_not_dualCycle :
    singletonIdentity (fun _ => 1) ≠ 0 := by
  intro equality
  have coordinate := congrFun equality (0 : Fin 1)
  norm_num [singletonIdentity] at coordinate

/--
Dual middle complex for a primal cancelling 1--2 pair:

`Z --id--> Z -> 0`.

Thus all degree-two vectors are cycles and the added generator is a
degree-three boundary.  The categorical realization of this quotient is the
Tham `k = 3` vacuum projector on the primal dotted component.
-/
def dualOfPrimalOneTwoPair : ClosedHandleBoundaryData 0 1 1 where
  d2 := toNoHandles 1
  d3 := singletonIdentity
  d2_d3_zero := by simp [singletonIdentity, toNoHandles]

/-- Every integer coefficient is a legal dual cycle in the 1--2 toy pair. -/
def primalOneTwo_dualCycle (coefficient : ℤ) :
    dualOfPrimalOneTwoPair.Cycles :=
  ⟨fun _ => coefficient, by
    funext index
    exact Fin.elim0 index⟩

/-- The unit generator is exactly the boundary of the unit dual 3-chain. -/
theorem primalOneTwo_unitCycle_is_dualBoundary :
    dualOfPrimalOneTwoPair.d3ToCycles (fun _ => 1) =
      primalOneTwo_dualCycle 1 := by
  apply Subtype.ext
  funext index
  exact Fin.cases rfl (fun impossible => Fin.elim0 impossible) index

/-- Zero and one represent the same evaluator-side `H2` class. -/
theorem primalOneTwo_zero_eq_one_in_dualH2 :
    QuotientAddGroup.mk'
        (AddMonoidHom.range dualOfPrimalOneTwoPair.d3ToCycles)
        (primalOneTwo_dualCycle 0) =
      (QuotientAddGroup.mk'
        (AddMonoidHom.range dualOfPrimalOneTwoPair.d3ToCycles)
        (primalOneTwo_dualCycle 1) :
        dualOfPrimalOneTwoPair.SecondHomology) := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  refine ⟨(fun _ => -1), ?_⟩
  apply Subtype.ext
  funext index
  have index_eq : index = (0 : Fin 1) := Subsingleton.elim _ _
  subst index
  change (-1 : ℤ) = 0 - 1
  norm_num

/-- Machine-visible convention status used by artifact validation. -/
def currentStatus : String :=
  "PASS_DUAL_UPSIDE_DOWN_HANDLE_CONVENTION_AND_CANCELLATION_CHECKS"

end TwistedYetter.Kirby.DualHandleConvention
