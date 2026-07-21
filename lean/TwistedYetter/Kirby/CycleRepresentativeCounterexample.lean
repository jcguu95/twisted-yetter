import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Regression counterexample to a primal/dual chain mismatch

A primal cancelling 2--3 handle pair has cellular differential

`d3 : Z -> Z,  d3(1) = 1`.

Its second handle homology is therefore zero: the degree-two cycles `0` and
`1` represent the same class.  Nevertheless, directly using the degree-two
coefficient as the exponent in a homologically twisted Kirby colour need not
give the same link evaluation.

The smallest numerical instance has two invertible simple labels, both of
quantum dimension one, and a nontrivial tensor-automorphism character with
values `1` and `-1`.  The zero-framed unknot contribution is

`1^n + (-1)^n`.

It is `2` at representative `n = 0` and `0` at representative `n = 1`.
Consequently this isolated-unknot formula cannot descend through the *primal*
quotient by the image of `d3`.

This calculation remains a useful regression test, but it is not a no-go
theorem for the evaluator used in this repository.  That evaluator reads the
diagram upside down and colours cycles in the dual handle complex.  The same
primal 2--3 pair is then a dual 1--2 pair, whose new degree-two coefficient is
forced to zero by the dual cycle condition.  See `DualHandleConvention`.

The other primal cancellation, a 1--2 pair, becomes a dual 2--3 pair.  Its
representative ambiguity is handled by the Tham `k = 3` vacuum projector on
the primal dotted component.  Omitting both the dual cycle condition and the
dotted component is precisely the convention error detected here.
-/

namespace TwistedYetter.Kirby.CycleRepresentativeCounterexample

/--
The fixed-label sum for a zero-framed unknot in the two-simple pointed test.

Both quantum dimensions are one.  The tensor-automorphism character is
`(1, -1)`, and `exponent` is the coefficient of the two-handle.
-/
def twoSimpleTwistedUnknot (exponent : ℤ) : ℚ :=
  (1 : ℚ) ^ exponent + (-1 : ℚ) ^ exponent

theorem twoSimpleTwistedUnknot_zero :
    twoSimpleTwistedUnknot 0 = 2 := by
  norm_num [twoSimpleTwistedUnknot]

theorem twoSimpleTwistedUnknot_one :
    twoSimpleTwistedUnknot 1 = 0 := by
  norm_num [twoSimpleTwistedUnknot]

/--
The quotient `Z / im(id)` is represented here by `ZMod 1`.  This is the
*primal* quotient used by the wrong adapter.
-/
theorem zero_and_one_same_canceling_pair_class :
    ((0 : ℤ) : ZMod 1) = ((1 : ℤ) : ZMod 1) := by
  exact Subsingleton.elim _ _

/--
The isolated twisted unknot does not factor through that primal quotient.
-/
theorem no_naive_representative_descent :
    ¬ ∃ value : ZMod 1 → ℚ,
        ∀ exponent : ℤ,
          value (exponent : ZMod 1) =
            twoSimpleTwistedUnknot exponent := by
  rintro ⟨value, agrees⟩
  have classEquality :
      ((0 : ℤ) : ZMod 1) = ((1 : ℤ) : ZMod 1) :=
    zero_and_one_same_canceling_pair_class
  have valueEquality :
      value ((0 : ℤ) : ZMod 1) =
        value ((1 : ℤ) : ZMod 1) :=
    congrArg value classEquality
  have impossible :
      twoSimpleTwistedUnknot 0 =
        twoSimpleTwistedUnknot 1 :=
    (agrees 0).symm.trans (valueEquality.trans (agrees 1))
  rw [twoSimpleTwistedUnknot_zero,
    twoSimpleTwistedUnknot_one] at impossible
  norm_num at impossible

/-- Machine-visible scope guard: this theorem diagnoses an adapter error. -/
def scopeStatus : String :=
  "REGRESSION_ONLY_WRONG_PRIMAL_CHAIN_AND_OMITTED_DOTTED_COMPONENT"

end TwistedYetter.Kirby.CycleRepresentativeCounterexample
