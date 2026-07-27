import TwistedYetter.Kirby.EGNOCategoryBoundSliding

/-!
# Character-weighted endpoints for a premodular 2/2 band slide

For one fixed moving simple label `x`, the two endpoints are the
channel-weighted Bärenz--Barrett stages (3.1.4) and (3.1.8).  The stationary
Kirby colour and every intermediate fusion channel remain explicit inside
the `SlidingFamily` calculation.

This module contains no axiom and no field asserting endpoint equality.
Equality is inherited from the kernel-checked generalized-sliding
calculation and is then lifted to the complete outer sum over `x`.
-/

namespace TwistedYetter.Kirby.PremodularTwoOverTwoBandEndpoints

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.EGNOCategoryBoundSliding
open TwistedYetter.Kirby.GeneralizedSliding
open TwistedYetter.Kirby.LinearDiagram

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
One unchanged exterior context closing the channel-weighted generalized
sliding calculation for every moving simple label.

No endpoint equality is stored here.
-/
structure ChannelWeightedClosedWindow
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data}
    {mateLaw : SphericalMateTraceLaw (K := K) data.spherical}
    (movies : LabelIndexedSlidingMovies data insertionLaw mateLaw) where
  strand : C
  closure :
    (movingLabel : S) →
      ((data.simple movingLabel ⊗ strand) ⟶
          (data.simple movingLabel ⊗ strand)) →ₗ[K]
        ((𝟙_ C) ⟶ (𝟙_ C))

namespace ChannelWeightedClosedWindow

variable
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data}
    {mateLaw : SphericalMateTraceLaw (K := K) data.spherical}
    {movies : LabelIndexedSlidingMovies data insertionLaw mateLaw}
    (window : ChannelWeightedClosedWindow movies)

/-- Evaluation of one moving-label sector at the weighted source stage. -/
noncomputable def beforeEval
    (channelWeight : S → K)
    (movingLabel : S) :
    (𝟙_ C) ⟶ (𝟙_ C) :=
  window.closure movingLabel
    (LinearDiagram.eval
      ((movies.family movingLabel).fiber window.strand
        |>.channelWeightedStage314 channelWeight))

/-- Evaluation of one moving-label sector at the weighted target stage. -/
noncomputable def afterEval
    (channelWeight : S → K)
    (movingLabel : S) :
    (𝟙_ C) ⟶ (𝟙_ C) :=
  window.closure movingLabel
    (LinearDiagram.eval
      ((movies.family movingLabel).fiber window.strand
        |>.channelWeightedStage318 channelWeight))

/-- The internal channel weight survives in every closed moving-label sector. -/
theorem fixedMovingLabel_eval_eq
    (channelWeight : S → K)
    (movingLabel : S) :
    window.beforeEval channelWeight movingLabel =
      window.afterEval channelWeight movingLabel :=
  congrArg
    (window.closure movingLabel)
    (((movies.family movingLabel).fiber window.strand)
      |>.channelWeighted_transport channelWeight)

/-- Complete source evaluation, retaining the outer moving-label sum. -/
noncomputable def linearBeforeEval
    (movingCoefficient channelWeight : S → K) :
    (𝟙_ C) ⟶ (𝟙_ C) :=
  ∑ movingLabel : S,
    movingCoefficient movingLabel •
      window.beforeEval channelWeight movingLabel

/-- Complete target evaluation, retaining the outer moving-label sum. -/
noncomputable def linearAfterEval
    (movingCoefficient channelWeight : S → K) :
    (𝟙_ C) ⟶ (𝟙_ C) :=
  ∑ movingLabel : S,
    movingCoefficient movingLabel •
      window.afterEval channelWeight movingLabel

/-- The complete channel-weighted closed endpoints evaluate equally. -/
theorem linear_eval_eq
    (movingCoefficient channelWeight : S → K) :
    window.linearBeforeEval movingCoefficient channelWeight =
      window.linearAfterEval movingCoefficient channelWeight := by
  apply Finset.sum_congr rfl
  intro movingLabel _
  exact congrArg
    (fun value => movingCoefficient movingLabel • value)
    (window.fixedMovingLabel_eval_eq channelWeight movingLabel)

end ChannelWeightedClosedWindow

end TwistedYetter.Kirby.PremodularTwoOverTwoBandEndpoints
