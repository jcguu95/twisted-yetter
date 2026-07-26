import TwistedYetter.Kirby.LinearDiagram

/-!
# Denominator-complete transport of role-aware finite sums

Local graphical equalities become evaluator equalities only after every
ordinary-label sector has been accounted for.  This file isolates that
finite reindexing step.  It contains no Kirby-move or category assumption.
-/

namespace TwistedYetter.Kirby.RoleAwareFiniteSumTransport

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.LinearDiagram

universe uK uC vC uι uκ

variable {K : Type uK} [CommSemiring K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]

/--
An exact reindexing of ordinary-label sectors transports the complete
weighted evaluation when both the scalar weight and the evaluated diagram
agree term by term.
-/
theorem eval_weightedSum_equiv
    {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ]
    (reindex : ι ≃ κ)
    {source target : Boundary C}
    (sourceWeight : ι → K)
    (targetWeight : κ → K)
    (sourceDiagram : ι → Diagram C source target)
    (targetDiagram : κ → Diagram C source target)
    (weight_sound :
      (index : ι) →
        sourceWeight index = targetWeight (reindex index))
    (diagram_sound :
      (index : ι) →
        Diagram.eval C (sourceDiagram index) =
          Diagram.eval C (targetDiagram (reindex index))) :
    LinearDiagram.eval
        (weightedSum sourceWeight sourceDiagram) =
      LinearDiagram.eval
        (weightedSum targetWeight targetDiagram) := by
  rw [eval_weightedSum, eval_weightedSum]
  apply Fintype.sum_equiv reindex
  intro index
  rw [weight_sound index, diagram_sound index]

/--
The common special case where the index type itself is unchanged.
-/
theorem eval_weightedSum_pointwise
    {ι : Type uι} [Fintype ι]
    {source target : Boundary C}
    (sourceWeight targetWeight : ι → K)
    (sourceDiagram targetDiagram : ι → Diagram C source target)
    (weight_sound :
      (index : ι) → sourceWeight index = targetWeight index)
    (diagram_sound :
      (index : ι) →
        Diagram.eval C (sourceDiagram index) =
          Diagram.eval C (targetDiagram index)) :
    LinearDiagram.eval
        (weightedSum sourceWeight sourceDiagram) =
      LinearDiagram.eval
        (weightedSum targetWeight targetDiagram) :=
  eval_weightedSum_equiv
    (Equiv.refl ι)
    sourceWeight targetWeight sourceDiagram targetDiagram
    weight_sound diagram_sound

end TwistedYetter.Kirby.RoleAwareFiniteSumTransport
