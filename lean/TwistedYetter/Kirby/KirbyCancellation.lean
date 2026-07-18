import Mathlib.Algebra.Field.Power
import TwistedYetter.Kirby.KirbyHandleMoves

/-!
# Handle cancellations and global-dimension normalization

This module formalizes the algebraic end of Bärenz--Barrett Theorem 3.9.
Graphical cutting, killing, transparent-twist, and pivotal-dimension equations
remain separate source-backed inputs.  From those local equations Lean derives
the raw cancellation factors, proves the exact normalization recurrences from
Definition 3.6 / equation (3.2.1), and then proves equality of normalized
values.

No constructor accepts a pre-written normalized equality.
-/

namespace TwistedYetter.Kirby.KirbyCancellation

universe uK uH₁ uH₂ uA

/-- Numbers of handles in every index, retained even though the link formula
uses only `h1` and `h2`. -/
structure HandleCounts where
  h0 : Nat
  h1 : Nat
  h2 : Nat
  h3 : Nat
  h4 : Nat
  deriving Repr, BEq, DecidableEq

namespace HandleCounts

/-- Add an isolated cancelling 1--2 pair. -/
def addOneTwo (counts : HandleCounts) : HandleCounts :=
  { counts with h1 := counts.h1 + 1, h2 := counts.h2 + 1 }

/-- Add an isolated cancelling 2--3 pair. -/
def addTwoThree (counts : HandleCounts) : HandleCounts :=
  { counts with h2 := counts.h2 + 1, h3 := counts.h3 + 1 }

/-- Add an empty 0-handle bookkeeping entry. -/
def addEmptyZero (counts : HandleCounts) : HandleCounts :=
  { counts with h0 := counts.h0 + 1 }

/-- Add an empty 4-handle bookkeeping entry. -/
def addEmptyFour (counts : HandleCounts) : HandleCounts :=
  { counts with h4 := counts.h4 + 1 }

end HandleCounts

variable {K : Type uK} [Field K]

/--
The three nonzero dimensions in equation (3.2.1).

`transparentDimension` is the dimension of the transparent part of
`F Ω_C`; it is not silently replaced by the dimension of the complete image.
-/
structure GlobalDimensionProfile where
  cDimension : K
  dDimension : K
  transparentDimension : K
  cDimension_ne_zero : cDimension ≠ 0
  dDimension_ne_zero : dDimension ≠ 0
  transparentDimension_ne_zero : transparentDimension ≠ 0
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Definition 3.6, equation (3.2.1), journal page 685"

namespace GlobalDimensionProfile

/-- Raw factor contributed by an isolated cancelling 1--2 pair. -/
def oneTwoFactor (profile : GlobalDimensionProfile (K := K)) : K :=
  profile.dDimension * profile.transparentDimension

/-- Raw factor contributed by an isolated cancelling 2--3 pair. -/
def twoThreeFactor (profile : GlobalDimensionProfile (K := K)) : K :=
  profile.cDimension

/--
Explicit scalar weight of one 3-handle.

Here `cDimension` is the global dimension `d(C)` in Bärenz--Barrett's
equation (3.2.1).  Authors who instead write `𝒟² = d(C)` should therefore
read this weight as `𝒟⁻²`, not `𝒟⁻¹`.
-/
def threeHandleWeight (profile : GlobalDimensionProfile (K := K)) : K :=
  profile.cDimension⁻¹

theorem oneTwoFactor_ne_zero
    (profile : GlobalDimensionProfile (K := K)) :
    profile.oneTwoFactor ≠ 0 :=
  mul_ne_zero profile.dDimension_ne_zero
    profile.transparentDimension_ne_zero

theorem threeHandleWeight_ne_zero
    (profile : GlobalDimensionProfile (K := K)) :
    profile.threeHandleWeight ≠ 0 :=
  inv_ne_zero profile.cDimension_ne_zero

/--
The isolated 2-handle contributes `d(C)` and its cancelling 3-handle
contributes `d(C)⁻¹`, so their explicit scalar contribution is one.
-/
theorem twoThreeFactor_mul_threeHandleWeight
    (profile : GlobalDimensionProfile (K := K)) :
    profile.twoThreeFactor * profile.threeHandleWeight = 1 := by
  simp [twoThreeFactor, threeHandleWeight, profile.cDimension_ne_zero]

/--
Exact denominator from equation (3.2.1):

`d(C)^(h₂-h₁) * (d(D) d((F Ω_C)'))^h₁`.

Integer powers are essential: the formula is not truncated when `h1 > h2`.
-/
def denominator
    (profile : GlobalDimensionProfile (K := K))
    (counts : HandleCounts) : K :=
  profile.cDimension ^
      (Int.ofNat counts.h2 - Int.ofNat counts.h1) *
    profile.oneTwoFactor ^ (Int.ofNat counts.h1)

theorem denominator_ne_zero
    (profile : GlobalDimensionProfile (K := K))
    (counts : HandleCounts) :
    profile.denominator counts ≠ 0 :=
  mul_ne_zero
    (zpow_ne_zero _ profile.cDimension_ne_zero)
    (zpow_ne_zero _ profile.oneTwoFactor_ne_zero)

/-- Adding a cancelling 1--2 pair multiplies the denominator by its raw factor. -/
theorem denominator_addOneTwo
    (profile : GlobalDimensionProfile (K := K))
    (counts : HandleCounts) :
    profile.denominator counts.addOneTwo =
      profile.oneTwoFactor * profile.denominator counts := by
  simp only [denominator, HandleCounts.addOneTwo]
  have h2succ :
      Int.ofNat (counts.h2 + 1) = Int.ofNat counts.h2 + 1 := by
    simpa only [Int.natCast_one] using
      (Int.natCast_add counts.h2 1)
  have h1succ :
      Int.ofNat (counts.h1 + 1) = Int.ofNat counts.h1 + 1 := by
    simpa only [Int.natCast_one] using
      (Int.natCast_add counts.h1 1)
  rw [h2succ, h1succ]
  have exponent :
      Int.ofNat counts.h2 + 1 - (Int.ofNat counts.h1 + 1) =
        Int.ofNat counts.h2 - Int.ofNat counts.h1 := by omega
  rw [exponent]
  rw [zpow_add₀ profile.oneTwoFactor_ne_zero]
  simp only [zpow_one]
  simp only [mul_left_comm, mul_comm]

/-- Adding a cancelling 2--3 pair multiplies the denominator by `d(C)`. -/
theorem denominator_addTwoThree
    (profile : GlobalDimensionProfile (K := K))
    (counts : HandleCounts) :
    profile.denominator counts.addTwoThree =
      profile.twoThreeFactor * profile.denominator counts := by
  simp only [denominator, HandleCounts.addTwoThree, twoThreeFactor]
  have h2succ :
      Int.ofNat (counts.h2 + 1) = Int.ofNat counts.h2 + 1 := by
    simpa only [Int.natCast_one] using
      (Int.natCast_add counts.h2 1)
  rw [h2succ]
  have exponent :
      Int.ofNat counts.h2 + 1 - Int.ofNat counts.h1 =
        (Int.ofNat counts.h2 - Int.ofNat counts.h1) + 1 := by omega
  rw [exponent, zpow_add₀ profile.cDimension_ne_zero]
  simp only [zpow_one]
  simp only [mul_assoc, mul_comm]

/--
Equivalent inverse-dimension form of the 2--3 normalization recurrence.

The ratio between the old denominator and the denominator after adding a
cancelling 2--3 pair is exactly the explicit 3-handle weight `d(C)⁻¹`.
-/
theorem denominator_ratio_addTwoThree
    (profile : GlobalDimensionProfile (K := K))
    (counts : HandleCounts) :
    profile.denominator counts /
        profile.denominator counts.addTwoThree =
      profile.threeHandleWeight := by
  rw [profile.denominator_addTwoThree]
  rw [div_mul_eq_div_div_swap]
  simp [threeHandleWeight, twoThreeFactor,
    profile.denominator_ne_zero counts]

/-- Empty 0-handles are absent from the link normalization. -/
theorem denominator_addEmptyZero
    (profile : GlobalDimensionProfile (K := K))
    (counts : HandleCounts) :
    profile.denominator counts.addEmptyZero =
      profile.denominator counts :=
  rfl

/-- Empty 4-handles are absent from the link normalization. -/
theorem denominator_addEmptyFour
    (profile : GlobalDimensionProfile (K := K))
    (counts : HandleCounts) :
    profile.denominator counts.addEmptyFour =
      profile.denominator counts :=
  rfl

end GlobalDimensionProfile

/-- Raw numerator together with all handle counts. -/
structure EvaluationState where
  counts : HandleCounts
  rawNumerator : K

namespace EvaluationState

/-- The normalized value of equation (3.2.1). -/
def normalized
    (profile : GlobalDimensionProfile (K := K))
    (state : EvaluationState (K := K)) : K :=
  state.rawNumerator / profile.denominator state.counts

end EvaluationState

/--
Source-backed local calculation for a 1--2 cancellation.

The final factor equation is not a field.  It is derived from disjoint-union
multiplicativity, cutting, killing, and the transparent-twist witness.
-/
structure OneTwoLocalCalculation
    (profile : GlobalDimensionProfile (K := K)) where
  pairValue : K
  cutValue : K
  before : EvaluationState (K := K)
  after : EvaluationState (K := K)
  counts_sound : before.counts = after.counts.addOneTwo
  isolated_from_rest : Prop
  isolated_from_rest_witness : isolated_from_rest
  disjoint_union_sound :
    isolated_from_rest →
      before.rawNumerator = pairValue * after.rawNumerator
  transparent_twist_trivial : Prop
  transparent_twist_witness : transparent_twist_trivial
  cutting_identity :
    transparent_twist_trivial →
      pairValue = profile.dDimension * cutValue
  killing_identity :
    cutValue = profile.transparentDimension
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Theorem 3.9, equation (3.3.2), journal pages 686-687; Lemmas 2.46-2.47"

namespace OneTwoLocalCalculation

theorem raw_factor
    {profile : GlobalDimensionProfile (K := K)}
    (calculation : OneTwoLocalCalculation profile) :
    calculation.before.rawNumerator =
      profile.oneTwoFactor * calculation.after.rawNumerator := by
  rw [calculation.disjoint_union_sound
      calculation.isolated_from_rest_witness,
    calculation.cutting_identity calculation.transparent_twist_witness,
    calculation.killing_identity]
  rfl

theorem normalized_sound
    {profile : GlobalDimensionProfile (K := K)}
    (calculation : OneTwoLocalCalculation profile) :
    calculation.before.normalized profile =
      calculation.after.normalized profile := by
  rw [EvaluationState.normalized, EvaluationState.normalized,
    calculation.raw_factor, calculation.counts_sound,
    profile.denominator_addOneTwo]
  exact mul_div_mul_left _ _ profile.oneTwoFactor_ne_zero

end OneTwoLocalCalculation

/--
Source-backed local calculation for a 2--3 cancellation.

The pivotal dimension equation is mandatory; Remark 3.11 gives a concrete
failure when it is omitted.
-/
structure TwoThreeLocalCalculation
    (profile : GlobalDimensionProfile (K := K)) where
  unknotValue : K
  before : EvaluationState (K := K)
  after : EvaluationState (K := K)
  counts_sound : before.counts = after.counts.addTwoThree
  unlinked_unknotted_zero_framed : Prop
  unlink_witness : unlinked_unknotted_zero_framed
  disjoint_union_sound :
    unlinked_unknotted_zero_framed →
      before.rawNumerator = unknotValue * after.rawNumerator
  pivotal_dimension_preserved :
    unknotValue = profile.cDimension
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Theorem 3.9 and Remark 3.11, journal page 687"

namespace TwoThreeLocalCalculation

theorem raw_factor
    {profile : GlobalDimensionProfile (K := K)}
    (calculation : TwoThreeLocalCalculation profile) :
    calculation.before.rawNumerator =
      profile.twoThreeFactor * calculation.after.rawNumerator := by
  rw [calculation.disjoint_union_sound calculation.unlink_witness,
    calculation.pivotal_dimension_preserved]
  rfl

/--
Handle-by-handle form of the same local calculation: after inserting the
explicit 3-handle weight, the cancelling 2--3 pair contributes no scalar.
-/
theorem raw_with_explicit_three_handle
    {profile : GlobalDimensionProfile (K := K)}
    (calculation : TwoThreeLocalCalculation profile) :
    calculation.before.rawNumerator * profile.threeHandleWeight =
      calculation.after.rawNumerator := by
  rw [calculation.raw_factor]
  calc
    (profile.twoThreeFactor * calculation.after.rawNumerator) *
          profile.threeHandleWeight =
        calculation.after.rawNumerator *
          (profile.twoThreeFactor * profile.threeHandleWeight) := by
            ac_rfl
    _ = calculation.after.rawNumerator := by
      rw [profile.twoThreeFactor_mul_threeHandleWeight, mul_one]

theorem normalized_sound
    {profile : GlobalDimensionProfile (K := K)}
    (calculation : TwoThreeLocalCalculation profile) :
    calculation.before.normalized profile =
      calculation.after.normalized profile := by
  rw [EvaluationState.normalized, EvaluationState.normalized,
    calculation.raw_factor, calculation.counts_sound,
    profile.denominator_addTwoThree]
  exact mul_div_mul_left _ _ profile.cDimension_ne_zero

end TwoThreeLocalCalculation

/--
Closed whitelist of normalized cancellation moves.  It cannot be constructed
from a bare equality of normalized values.
-/
inductive AdmittedCancellation
    (profile : GlobalDimensionProfile (K := K)) :
    EvaluationState (K := K) → EvaluationState (K := K) → Type uK
  | oneTwo (calculation : OneTwoLocalCalculation profile) :
      AdmittedCancellation profile calculation.before calculation.after
  | twoThree (calculation : TwoThreeLocalCalculation profile) :
      AdmittedCancellation profile calculation.before calculation.after

namespace AdmittedCancellation

theorem sound
    {profile : GlobalDimensionProfile (K := K)}
    {before after : EvaluationState (K := K)}
    (move : AdmittedCancellation profile before after) :
    before.normalized profile = after.normalized profile := by
  cases move with
  | oneTwo calculation => exact calculation.normalized_sound
  | twoThree calculation => exact calculation.normalized_sound

end AdmittedCancellation

/--
Cancellation transports homology across an explicit equivalence.  The target
character is derived contravariantly and cannot be handwritten independently.
-/
structure CancellationHomologyTransport
    (HBefore : Type uH₁) (HAfter : Type uH₂) (A : Type uA) where
  homologyEquiv : HBefore ≃ HAfter
  beforeCharacter : HBefore → A

namespace CancellationHomologyTransport

def afterCharacter
    {HBefore : Type uH₁} {HAfter : Type uH₂} {A : Type uA}
    (transport : CancellationHomologyTransport HBefore HAfter A) :
    HAfter → A :=
  transport.beforeCharacter ∘ transport.homologyEquiv.symm

theorem pairing_preserved
    {HBefore : Type uH₁} {HAfter : Type uH₂} {A : Type uA}
    (transport : CancellationHomologyTransport HBefore HAfter A)
    (alpha : HBefore) :
    transport.afterCharacter (transport.homologyEquiv alpha) =
      transport.beforeCharacter alpha := by
  simp [afterCharacter]

end CancellationHomologyTransport

end TwistedYetter.Kirby.KirbyCancellation
