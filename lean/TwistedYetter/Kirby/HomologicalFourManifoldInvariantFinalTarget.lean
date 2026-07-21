import TwistedYetter.Kirby.BoundaryStandardization

/-!
# Final target for a homologically marked four-manifold invariant

This module pins the public statement in the form used by the paper.

The public input is exactly a closed oriented smooth four-manifold `X` and a
class `alpha : H2(X; Z)`.  Handle presentations, handle-chain classes,
homology-basis realizations, and Kirby movies are internal witnesses.

The construction has two sharply separated inputs:

1. a presentation formula together with a proof that it is unchanged along
   every admitted movie; and
2. the topology theorem that admissible presentations exist and that any two
   presentations related by a marked oriented diffeomorphism are connected by
   an admitted movie.

The second input contains no scalar, category, evaluator, or equality of
evaluations.  Thus the final descent theorem cannot hide the desired
invariance inside a topology assumption.
-/

namespace TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget

open TwistedYetter.Kirby.BoundaryStandardization

universe uK uX uH uD uP uMovie

/--
Closed oriented smooth four-manifolds together with their integral second
homology and the action of oriented diffeomorphisms on that homology.

This is the literature boundary for smooth manifolds and singular homology.
It contains no handle presentation and no invariant value.
-/
structure HomologicalFourManifoldTheory where
  FourManifold : Type uX
  SecondHomology : FourManifold → Type uH
  secondHomologyAddCommGroup :
    (X : FourManifold) → AddCommGroup (SecondHomology X)
  orientedDiffeomorphism :
    OrientedDiffeomorphismGroupoid.{uX, uD} FourManifold
  homologyMap :
    {X Y : FourManifold} →
      orientedDiffeomorphism.Hom X Y →
        SecondHomology X ≃+ SecondHomology Y
  homologyMap_identity :
    (X : FourManifold) →
      homologyMap (orientedDiffeomorphism.identity X) =
        AddEquiv.refl (SecondHomology X)
  homologyMap_compose :
    {X Y Z : FourManifold} →
    (first : orientedDiffeomorphism.Hom X Y) →
    (second : orientedDiffeomorphism.Hom Y Z) →
      homologyMap (orientedDiffeomorphism.compose first second) =
        (homologyMap first).trans (homologyMap second)

attribute [instance]
  HomologicalFourManifoldTheory.secondHomologyAddCommGroup

namespace HomologicalFourManifoldTheory

/-- A public pair `(X, alpha)` with `alpha` in the actual `H2` of `X`. -/
structure MarkedManifold
    (geometry : HomologicalFourManifoldTheory.{uX, uH, uD}) where
  manifold : geometry.FourManifold
  alpha : geometry.SecondHomology manifold

/--
An oriented diffeomorphism that transports the displayed `H2` class.
-/
structure MarkedDiffeomorphism
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (source target : geometry.MarkedManifold) where
  underlying :
    geometry.orientedDiffeomorphism.Hom
      source.manifold target.manifold
  alpha_transport :
    geometry.homologyMap underlying source.alpha = target.alpha

/-- The identity diffeomorphism preserves every displayed homology class. -/
def MarkedDiffeomorphism.identity
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (marked : geometry.MarkedManifold) :
    geometry.MarkedDiffeomorphism marked marked where
  underlying :=
    geometry.orientedDiffeomorphism.identity marked.manifold
  alpha_transport := by
    rw [geometry.homologyMap_identity]
    rfl

end HomologicalFourManifoldTheory

/--
The internal syntax of admissible presentations and their movies.

`Presentation` may contain handle-chain coordinates and a certified
two-handle-sphere basis realization.  Those data are indexed by the public
pair and therefore cannot leak into the type of the final evaluator.
-/
structure AdmissibleHandlePresentationTheory
    (geometry : HomologicalFourManifoldTheory.{uX, uH, uD}) where
  Presentation : geometry.MarkedManifold → Type uP
  Movie :
    {source target : geometry.MarkedManifold} →
      geometry.MarkedDiffeomorphism source target →
      Presentation source → Presentation target → Type uMovie

/--
The imported topology theorem needed after the local Kirby calculations.

It says only that admissible presentations exist and are connected by the
declared movie calculus.  It has no field in the scalar type `K`, and no field
may assert equality of evaluator values.
-/
structure AdmissibleKirbyCerfTheorem
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (calculus :
      AdmissibleHandlePresentationTheory.{uX, uH, uD, uP, uMovie}
        geometry) where
  presentationExists :
    (marked : geometry.MarkedManifold) →
      Nonempty (calculus.Presentation marked)
  presentationsConnected :
    {source target : geometry.MarkedManifold} →
    (diffeomorphism :
      geometry.MarkedDiffeomorphism source target) →
    (sourcePresentation : calculus.Presentation source) →
    (targetPresentation : calculus.Presentation target) →
      Nonempty
        (calculus.Movie diffeomorphism
          sourcePresentation targetPresentation)

/-- The scalar formula on one internal admissible presentation. -/
structure PresentationFormula
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (calculus :
      AdmissibleHandlePresentationTheory.{uX, uH, uD, uP, uMovie}
        geometry)
    (K : Type uK) where
  value :
    {marked : geometry.MarkedManifold} →
      calculus.Presentation marked → K

/--
The exact result supplied by the categorical Kirby calculation.

This is intentionally a separate proposition, not a field of the topology
theorem.
-/
def IsInvariantAlongAdmissibleMovies
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    {calculus :
      AdmissibleHandlePresentationTheory.{uX, uH, uD, uP, uMovie}
        geometry}
    {K : Type uK}
    (formula : PresentationFormula calculus K) : Prop :=
  ∀ {source target : geometry.MarkedManifold}
    {diffeomorphism :
      geometry.MarkedDiffeomorphism source target}
    {sourcePresentation : calculus.Presentation source}
    {targetPresentation : calculus.Presentation target},
    calculus.Movie diffeomorphism
        sourcePresentation targetPresentation →
      formula.value sourcePresentation =
        formula.value targetPresentation

/--
The paper-facing result.

All construction and proof inputs have been discharged before an inhabitant
of this structure is produced.  Its evaluator itself accepts only a manifold
`X` and a class `alpha : H2(X; Z)`.
-/
structure HomologicalFourManifoldInvariant
    (geometry : HomologicalFourManifoldTheory.{uX, uH, uD})
    (K : Type uK) where
  EvalC :
    (X : geometry.FourManifold) →
      geometry.SecondHomology X → K
  diffeomorphismInvariant :
    {X Y : geometry.FourManifold} →
    (diffeomorphism :
      geometry.orientedDiffeomorphism.Hom X Y) →
    (alpha : geometry.SecondHomology X) →
      EvalC X alpha =
        EvalC Y (geometry.homologyMap diffeomorphism alpha)

namespace AdmissibleKirbyCerfTheorem

/-- One internal presentation selected only for the definition of `EvalC`. -/
noncomputable def chosenPresentation
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    {calculus :
      AdmissibleHandlePresentationTheory.{uX, uH, uD, uP, uMovie}
        geometry}
    (topology : AdmissibleKirbyCerfTheorem calculus)
    (marked : geometry.MarkedManifold) :
    calculus.Presentation marked :=
  Classical.choice (topology.presentationExists marked)

/--
The public invariant candidate.

Once the category, its twisting automorphism, the presentation formula, and
the two proved boundaries above are fixed, the only arguments are `X` and
`alpha : H2(X; Z)`.
-/
noncomputable def EvalC
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    {calculus :
      AdmissibleHandlePresentationTheory.{uX, uH, uD, uP, uMovie}
        geometry}
    {K : Type uK}
    (topology : AdmissibleKirbyCerfTheorem calculus)
    (formula : PresentationFormula calculus K)
    (X : geometry.FourManifold)
    (alpha : geometry.SecondHomology X) : K :=
  formula.value
    (topology.chosenPresentation
      {
        manifold := X
        alpha := alpha
      })

/--
The chosen internal presentation is immaterial.

This is the proof that prevents `Classical.choice` from becoming a hidden
choice in the mathematical invariant.
-/
theorem EvalC_eq_presentation
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    {calculus :
      AdmissibleHandlePresentationTheory.{uX, uH, uD, uP, uMovie}
        geometry}
    {K : Type uK}
    (topology : AdmissibleKirbyCerfTheorem calculus)
    (formula : PresentationFormula calculus K)
    (movieInvariant : IsInvariantAlongAdmissibleMovies formula)
    (X : geometry.FourManifold)
    (alpha : geometry.SecondHomology X)
    (presentation :
      calculus.Presentation
        {
          manifold := X
          alpha := alpha
        }) :
    topology.EvalC formula X alpha =
      formula.value presentation := by
  let marked : geometry.MarkedManifold :=
    {
      manifold := X
      alpha := alpha
    }
  let chosen := topology.chosenPresentation marked
  obtain ⟨movie⟩ :=
    topology.presentationsConnected
      (HomologicalFourManifoldTheory.MarkedDiffeomorphism.identity marked)
      chosen presentation
  exact movieInvariant movie

/--
Pinned final statement: `EvalC(X, alpha)` is invariant under every
orientation-preserving diffeomorphism, with `alpha` transported by the
induced map on integral second homology.
-/
theorem EvalC_diffeomorphism_invariant
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    {calculus :
      AdmissibleHandlePresentationTheory.{uX, uH, uD, uP, uMovie}
        geometry}
    {K : Type uK}
    (topology : AdmissibleKirbyCerfTheorem calculus)
    (formula : PresentationFormula calculus K)
    (movieInvariant : IsInvariantAlongAdmissibleMovies formula)
    {X Y : geometry.FourManifold}
    (diffeomorphism :
      geometry.orientedDiffeomorphism.Hom X Y)
    (alpha : geometry.SecondHomology X) :
    topology.EvalC formula X alpha =
      topology.EvalC formula Y
        (geometry.homologyMap diffeomorphism alpha) := by
  let source : geometry.MarkedManifold :=
    {
      manifold := X
      alpha := alpha
    }
  let target : geometry.MarkedManifold :=
    {
      manifold := Y
      alpha := geometry.homologyMap diffeomorphism alpha
    }
  let markedDiffeomorphism :
      geometry.MarkedDiffeomorphism source target :=
    {
      underlying := diffeomorphism
      alpha_transport := rfl
    }
  obtain ⟨movie⟩ :=
    topology.presentationsConnected markedDiffeomorphism
      (topology.chosenPresentation source)
      (topology.chosenPresentation target)
  exact movieInvariant movie

/--
The completed descent construction as a genuine invariant object.

Unlike the internal `EvalC` helper above, the resulting public evaluator has
exactly the type

`(X : FourManifold) -> SecondHomology X -> K`.
-/
noncomputable def constructInvariant
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    {calculus :
      AdmissibleHandlePresentationTheory.{uX, uH, uD, uP, uMovie}
        geometry}
    {K : Type uK}
    (topology : AdmissibleKirbyCerfTheorem calculus)
    (formula : PresentationFormula calculus K)
    (movieInvariant : IsInvariantAlongAdmissibleMovies formula) :
    HomologicalFourManifoldInvariant geometry K where
  EvalC := topology.EvalC formula
  diffeomorphismInvariant :=
    topology.EvalC_diffeomorphism_invariant formula movieInvariant

/-- The public invariant agrees with every admissible presentation formula. -/
theorem constructInvariant_EvalC_eq_presentation
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    {calculus :
      AdmissibleHandlePresentationTheory.{uX, uH, uD, uP, uMovie}
        geometry}
    {K : Type uK}
    (topology : AdmissibleKirbyCerfTheorem calculus)
    (formula : PresentationFormula calculus K)
    (movieInvariant : IsInvariantAlongAdmissibleMovies formula)
    (X : geometry.FourManifold)
    (alpha : geometry.SecondHomology X)
    (presentation :
      calculus.Presentation
        {
          manifold := X
          alpha := alpha
        }) :
    (topology.constructInvariant formula movieInvariant).EvalC X alpha =
      formula.value presentation :=
  topology.EvalC_eq_presentation formula movieInvariant
    X alpha presentation

end AdmissibleKirbyCerfTheorem

end TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget
