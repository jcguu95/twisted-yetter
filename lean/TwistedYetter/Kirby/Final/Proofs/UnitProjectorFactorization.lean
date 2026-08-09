import TwistedYetter.Kirby.Final.Semantics.Independent.Graphical

/-!
# Tensor-unit projector factorization

This file exposes the elementary factorization hidden in the definition of
`tensorUnitProjector`.  Every summand is first projected to its chosen simple
summand.  If that summand is isomorphic to the tensor unit, the chosen
isomorphism turns the term into a composite

`X ⟶ 𝟙 ⟶ X`.

No Kirby-diagram orientation, dotted-disk incidence, character, or evaluator
occurs here.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- A chosen identification of one unit summand with the tensor unit. -/
noncomputable def tensorUnitSummandIso
    (𝒸 : BundledPremodularCategory K)
    (X : 𝒸.C)
    (i : (𝒸.decomposition X).SummandIndex)
    (isUnit : IsTensorUnitSummand 𝒸 X i) :
    (𝒸.decomposition X).summandObject i ≅ 𝟙_ 𝒸.C :=
  Classical.choice isUnit

/-- The `X ⟶ 𝟙` half of one conditional unit-channel term. -/
noncomputable def tensorUnitFactorProjection
    (𝒸 : BundledPremodularCategory K)
    (X : 𝒸.C)
    (i : (𝒸.decomposition X).SummandIndex) :
    X ⟶ 𝟙_ 𝒸.C := by
  classical
  exact if isUnit : IsTensorUnitSummand 𝒸 X i then
    (𝒸.decomposition X).projection i ≫
      (tensorUnitSummandIso 𝒸 X i isUnit).hom
  else
    0

/-- The `𝟙 ⟶ X` half of one conditional unit-channel term. -/
noncomputable def tensorUnitFactorInclusion
    (𝒸 : BundledPremodularCategory K)
    (X : 𝒸.C)
    (i : (𝒸.decomposition X).SummandIndex) :
    𝟙_ 𝒸.C ⟶ X := by
  classical
  exact if isUnit : IsTensorUnitSummand 𝒸 X i then
    (tensorUnitSummandIso 𝒸 X i isUnit).inv ≫
      (𝒸.decomposition X).inclusion i
  else
    0

/-- The single summand appearing in the defining sum for the projector. -/
noncomputable def tensorUnitProjectorTerm
    (𝒸 : BundledPremodularCategory K)
    (X : 𝒸.C)
    (i : (𝒸.decomposition X).SummandIndex) :
    X ⟶ X := by
  classical
  exact if IsTensorUnitSummand 𝒸 X i then
    (𝒸.decomposition X).projection i ≫
      (𝒸.decomposition X).inclusion i
  else
    0

/-- One conditional projector term factors through the tensor unit. -/
theorem tensorUnitFactorProjection_comp_inclusion
    (𝒸 : BundledPremodularCategory K)
    (X : 𝒸.C)
    (i : (𝒸.decomposition X).SummandIndex) :
    tensorUnitFactorProjection 𝒸 X i ≫
        tensorUnitFactorInclusion 𝒸 X i =
      tensorUnitProjectorTerm 𝒸 X i := by
  classical
  by_cases isUnit : IsTensorUnitSummand 𝒸 X i
  · simp [tensorUnitFactorProjection, tensorUnitFactorInclusion,
      tensorUnitProjectorTerm, isUnit, Category.assoc]
  · simp [tensorUnitFactorProjection, tensorUnitFactorInclusion,
      tensorUnitProjectorTerm, isUnit]

/-- The full tensor-unit projector is a finite sum of maps through `𝟙`. -/
theorem tensorUnitProjector_eq_sum_unitFactorizations
    (𝒸 : BundledPremodularCategory K)
    (X : 𝒸.C) :
    tensorUnitProjector 𝒸 X =
      ∑ i : (𝒸.decomposition X).SummandIndex,
        tensorUnitFactorProjection 𝒸 X i ≫
          tensorUnitFactorInclusion 𝒸 X i := by
  classical
  unfold tensorUnitProjector
  apply Finset.sum_congr rfl
  intro i _
  exact (tensorUnitFactorProjection_comp_inclusion 𝒸 X i).symm

end

end TwistedYetter.Kirby.Final.Proofs
