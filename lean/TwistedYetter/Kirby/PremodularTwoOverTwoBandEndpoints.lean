import TwistedYetter.Kirby.EGNOCategoryBoundSliding

/-!
# Explicit finite-sum endpoints for a premodular 2/2 band slide

The two endpoints below are not arbitrary diagrams.  For one fixed moving
simple label `x`, they are exactly Bärenz--Barrett's stages (3.1.3) and
(3.1.8).  The stationary Kirby colour and every intermediate fusion channel
remain inside the `SlidingFamily` calculation.

This module contains no axiom and no field asserting endpoint equality.
Equality is inherited from the kernel-checked generalized-sliding
calculation and is then lifted to the complete outer sum over `x`.
-/

namespace TwistedYetter.Kirby.PremodularTwoOverTwoBandEndpoints

open scoped BigOperators
open CategoryTheory
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

/-- The two mathematically distinct ends of the standard band movie. -/
inductive Side
  | before
  | after
  deriving DecidableEq, Repr

namespace Side

/--
The exact closed endpoint for one fixed moving simple label.

For `before` this is stage (3.1.3); for `after` it is stage (3.1.8).
The stationary Kirby colour is still a finite sum inside the selected
`SlidingFamily`.
-/
noncomputable def diagram
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data}
    {mateLaw : SphericalMateTraceLaw (K := K) data.spherical}
    {movies : LabelIndexedSlidingMovies data insertionLaw mateLaw}
    (side : Side)
    (window : LabelIndexedSlidingMovies.ClosedWindow movies)
    (movingLabel : S) :
    Diagram C .unit .unit :=
  match side with
  | .before => window.before movingLabel
  | .after => window.after movingLabel

@[simp]
theorem diagram_before
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data}
    {mateLaw : SphericalMateTraceLaw (K := K) data.spherical}
    {movies : LabelIndexedSlidingMovies data insertionLaw mateLaw}
    (window : LabelIndexedSlidingMovies.ClosedWindow movies)
    (movingLabel : S) :
    Side.before.diagram window movingLabel = window.before movingLabel :=
  rfl

@[simp]
theorem diagram_after
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data}
    {mateLaw : SphericalMateTraceLaw (K := K) data.spherical}
    {movies : LabelIndexedSlidingMovies data insertionLaw mateLaw}
    (window : LabelIndexedSlidingMovies.ClosedWindow movies)
    (movingLabel : S) :
    Side.after.diagram window movingLabel = window.after movingLabel :=
  rfl

end Side

/--
One fixed moving-label sector is invariant.

This is not a fixed `(x,y)` statement: `y` and the fusion channels
`(z, μ)` remain summed inside `movies.family movingLabel`.
-/
theorem fixedMovingLabel_eval_eq
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data}
    {mateLaw : SphericalMateTraceLaw (K := K) data.spherical}
    {movies : LabelIndexedSlidingMovies data insertionLaw mateLaw}
    (window : LabelIndexedSlidingMovies.ClosedWindow movies)
    (movingLabel : S) :
    Diagram.eval C (Side.before.diagram window movingLabel) =
      Diagram.eval C (Side.after.diagram window movingLabel) :=
  window.term_sound movingLabel

/-- The explicit outer sum over all moving simple labels. -/
noncomputable def linearEndpoint
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data}
    {mateLaw : SphericalMateTraceLaw (K := K) data.spherical}
    {movies : LabelIndexedSlidingMovies data insertionLaw mateLaw}
    (side : Side)
    (window : LabelIndexedSlidingMovies.ClosedWindow movies)
    (movingCoefficient : S → K) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum movingCoefficient (side.diagram window)

/--
The complete explicit band endpoints have equal evaluation.

The coefficient may contain the moving component's quantum dimension,
character scalar, and every factor independent of the stationary label.
-/
theorem linearEndpoint_eval_eq
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data}
    {mateLaw : SphericalMateTraceLaw (K := K) data.spherical}
    {movies : LabelIndexedSlidingMovies data insertionLaw mateLaw}
    (window : LabelIndexedSlidingMovies.ClosedWindow movies)
    (movingCoefficient : S → K) :
    LinearDiagram.eval
        (linearEndpoint Side.before window movingCoefficient) =
      LinearDiagram.eval
        (linearEndpoint Side.after window movingCoefficient) := by
  simp only [linearEndpoint, eval_weightedSum]
  apply Finset.sum_congr rfl
  intro movingLabel _
  exact congrArg (fun value => movingCoefficient movingLabel • value)
    (fixedMovingLabel_eval_eq window movingLabel)

end TwistedYetter.Kirby.PremodularTwoOverTwoBandEndpoints
