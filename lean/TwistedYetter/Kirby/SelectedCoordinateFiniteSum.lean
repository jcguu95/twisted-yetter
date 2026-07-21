import Mathlib.Data.Fintype.BigOperators

/-!
# Splitting one selected coordinate from a finite labeling

This module gives an explicit equivalence between a complete finite labeling
and the selected label together with all remaining labels.  Its sum theorem
is used to isolate one dotted component without changing the denominator.
-/

namespace TwistedYetter.Kirby.SelectedCoordinateFiniteSum

open scoped BigOperators

universe uI uS uV

/-- All indices other than one selected coordinate. -/
abbrev RemainingIndex {I : Type uI} (selected : I) :=
  { index : I // index ≠ selected }

/-- Split a complete labeling at one selected coordinate. -/
def splitAt
    {I : Type uI} [DecidableEq I]
    (selected : I)
    (S : Type uS) :
    (I → S) ≃ (S × (RemainingIndex selected → S)) where
  toFun labeling :=
    (labeling selected, fun index => labeling index.1)
  invFun splitLabeling := fun index =>
    if equal : index = selected then
      splitLabeling.1
    else
      splitLabeling.2 ⟨index, equal⟩
  left_inv labeling := by
    funext index
    by_cases equal : index = selected
    · subst index
      simp
    · simp [equal]
  right_inv splitLabeling := by
    apply Prod.ext
    · simp
    · funext index
      simp [index.property]

/-- Reconstruct a complete labeling from the selected and remaining labels. -/
def combineAt
    {I : Type uI} [DecidableEq I]
    (selected : I)
    {S : Type uS}
    (selectedLabel : S)
    (remaining : RemainingIndex selected → S) : I → S :=
  (splitAt selected S).symm (selectedLabel, remaining)

@[simp] theorem combineAt_selected
    {I : Type uI} [DecidableEq I]
    (selected : I)
    {S : Type uS}
    (selectedLabel : S)
    (remaining : RemainingIndex selected → S) :
    combineAt selected selectedLabel remaining selected = selectedLabel := by
  simp [combineAt, splitAt]

@[simp] theorem combineAt_remaining
    {I : Type uI} [DecidableEq I]
    (selected : I)
    {S : Type uS}
    (selectedLabel : S)
    (remaining : RemainingIndex selected → S)
    (index : RemainingIndex selected) :
    combineAt selected selectedLabel remaining index.1 = remaining index := by
  simp [combineAt, splitAt, index.property]

/--
The complete finite sum is exactly the iterated sum over remaining labels and
the selected label.  This is a reindexing theorem, not an approximation.
-/
theorem sum_splitAt
    {I : Type uI} [Fintype I] [DecidableEq I]
    (selected : I)
    {S : Type uS} [Fintype S]
    {V : Type uV} [AddCommMonoid V]
    (summand : (I → S) → V) :
    (∑ labeling, summand labeling) =
      ∑ remaining : RemainingIndex selected → S,
        ∑ selectedLabel : S,
          summand (combineAt selected selectedLabel remaining) := by
  calc
    (∑ labeling, summand labeling) =
        ∑ splitLabeling : S × (RemainingIndex selected → S),
          summand ((splitAt selected S).symm splitLabeling) :=
      (Equiv.sum_comp (splitAt selected S).symm summand).symm
    _ = ∑ selectedLabel : S,
          ∑ remaining : RemainingIndex selected → S,
            summand (combineAt selected selectedLabel remaining) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ remaining : RemainingIndex selected → S,
          ∑ selectedLabel : S,
            summand (combineAt selected selectedLabel remaining) :=
      Finset.sum_comm

/-- Machine-visible status of the exact denominator split. -/
def currentStatus : String :=
  "PASS_SELECTED_COORDINATE_FINITE_LABEL_SUM_SPLIT"

end TwistedYetter.Kirby.SelectedCoordinateFiniteSum
