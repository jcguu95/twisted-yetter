import TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget
import TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget

/-!
# Literature boundary from handle presentations to homologically marked manifolds

This module is the explicit semantic bridge between two different kinds of
objects:

* finite handle-presentation data, whose marking is computed from its handle
  chain complex; and
* an actual closed oriented smooth four-manifold `X` together with a class in
  `H₂(X; ℤ)`.

Lean does not reconstruct smooth manifolds, singular homology, Morse theory,
or Cerf theory here.  Those standard topology results enter through the four
fields of `HomologicalFourManifoldTopologyBoundary`.  The bridge nevertheless
keeps the crucial semantics visible: every presentation has an underlying
manifold, and its handle-chain marking is identified with the actual second
homology of that manifold.

No field below mentions a category, an evaluator, a scalar value, or equality
of scalar values.
-/

namespace TwistedYetter.Kirby.LiteratureBackedHomologicalFourManifoldTopology

open TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget
open TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget

universe uK uP uM uMove uX uH uD

/--
The geometric meaning of one unmarked handle presentation, including the
identification between handle-chain `H₂` and manifold `H₂`.
-/
structure HandlePresentationRealization
    (theory : HandlePresentationTheory.{uP, uM, uMove})
    (geometry : HomologicalFourManifoldTheory.{uX, uH, uD}) where
  markingAddCommGroup :
    (presentation : theory.Presentation) →
      AddCommGroup (theory.Marking presentation)
  underlyingManifold :
    theory.Presentation → geometry.FourManifold
  secondHomologyEquiv :
    (presentation : theory.Presentation) →
      theory.Marking presentation ≃+
        geometry.SecondHomology (underlyingManifold presentation)

attribute [instance]
  HandlePresentationRealization.markingAddCommGroup

namespace HandlePresentationRealization

/-- Realize a handle-chain class as a class in the actual manifold's `H₂`. -/
def realizeMarkedPresentation
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (realization : HandlePresentationRealization theory geometry)
    (marked : theory.MarkedPresentation) :
    geometry.MarkedManifold where
  manifold := realization.underlyingManifold marked.presentation
  alpha :=
    realization.secondHomologyEquiv marked.presentation marked.marking

end HandlePresentationRealization

/--
A concrete marked handle presentation of the public pair `(X, alpha)`.

The diffeomorphism and the final equality say exactly how the handle-chain
class is identified with the displayed class in `H₂(X; ℤ)`.
-/
structure MarkedPresentationOf
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (realization : HandlePresentationRealization theory geometry)
    (markedManifold : geometry.MarkedManifold) where
  markedPresentation : theory.MarkedPresentation
  diffeomorphism :
    geometry.orientedDiffeomorphism.Hom
      (realization.underlyingManifold markedPresentation.presentation)
      markedManifold.manifold
  marking_transport :
    geometry.homologyMap diffeomorphism
        (realization.secondHomologyEquiv
          markedPresentation.presentation markedPresentation.marking) =
      markedManifold.alpha

namespace HandlePresentationRealization

/--
Every marked presentation canonically presents the marked manifold obtained
by realizing that same presentation.
-/
def selfPresentation
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (realization : HandlePresentationRealization theory geometry)
    (marked : theory.MarkedPresentation) :
    MarkedPresentationOf realization
      (realization.realizeMarkedPresentation marked) where
  markedPresentation := marked
  diffeomorphism :=
    geometry.orientedDiffeomorphism.identity
      (realization.underlyingManifold marked.presentation)
  marking_transport := by
    change
      geometry.homologyMap
          (geometry.orientedDiffeomorphism.identity
            (realization.underlyingManifold marked.presentation))
          (realization.secondHomologyEquiv
            marked.presentation marked.marking) =
        realization.secondHomologyEquiv
          marked.presentation marked.marking
    rw [geometry.homologyMap_identity]
    rfl

end HandlePresentationRealization

/--
Each elementary marked Kirby move realizes a marked oriented
diffeomorphism.  In particular, the induced map on actual `H₂` agrees with
the handle-chain transport attached to the move.
-/
structure ElementaryMoveHomologicalSoundness
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (realization : HandlePresentationRealization theory geometry) where
  markedDiffeomorphism :
    {source target : theory.Presentation} →
    (move : theory.ElementaryMove source target) →
    (marking : theory.Marking source) →
      geometry.MarkedDiffeomorphism
        (realization.realizeMarkedPresentation ⟨source, marking⟩)
        (realization.realizeMarkedPresentation
          ⟨target, theory.transport move marking⟩)

/-- Every public pair `(X, alpha)` has an admissible marked presentation. -/
structure MarkedPresentationExistence
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (realization : HandlePresentationRealization theory geometry) where
  presentation :
    (markedManifold : geometry.MarkedManifold) →
      Nonempty (MarkedPresentationOf realization markedManifold)

/--
Marked Kirby--Cerf completeness.

Presentations of marked-diffeomorphic pairs are connected by a finite movie
whose marking transport is the handle-chain transport.
-/
structure MarkedKirbyCerfCompleteness
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (realization : HandlePresentationRealization theory geometry) where
  connected :
    {source target : geometry.MarkedManifold} →
    (diffeomorphism : geometry.MarkedDiffeomorphism source target) →
    (sourcePresentation : MarkedPresentationOf realization source) →
    (targetPresentation : MarkedPresentationOf realization target) →
      Nonempty
        (theory.KirbyMovie
          sourcePresentation.markedPresentation
          targetPresentation.markedPresentation)

/--
The complete, category-neutral topology trust boundary used by the public
homological invariant.
-/
structure HomologicalFourManifoldTopologyBoundary
    (theory : HandlePresentationTheory.{uP, uM, uMove})
    (geometry : HomologicalFourManifoldTheory.{uX, uH, uD}) where
  realization : HandlePresentationRealization theory geometry
  elementaryMoveSoundness :
    ElementaryMoveHomologicalSoundness realization
  markedPresentationExistence :
    MarkedPresentationExistence realization
  markedKirbyCerfCompleteness :
    MarkedKirbyCerfCompleteness realization

namespace HomologicalFourManifoldTopologyBoundary

/-- The dependent presentation calculus induced by the topology boundary. -/
def admissibleCalculus
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (topology :
      HomologicalFourManifoldTopologyBoundary theory geometry) :
    AdmissibleHandlePresentationTheory geometry where
  Presentation := MarkedPresentationOf topology.realization
  Movie := fun _ sourcePresentation targetPresentation =>
    theory.KirbyMovie
      sourcePresentation.markedPresentation
      targetPresentation.markedPresentation

/-- The standard Kirby--Cerf theorem in the dependent presentation language. -/
def admissibleKirbyCerfTheorem
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (topology :
      HomologicalFourManifoldTopologyBoundary theory geometry) :
    AdmissibleKirbyCerfTheorem topology.admissibleCalculus where
  presentationExists :=
    topology.markedPresentationExistence.presentation
  presentationsConnected :=
    topology.markedKirbyCerfCompleteness.connected

/-- Turn a formula on marked handle data into the dependent formula. -/
def admissibleFormula
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    {K : Type uK}
    (topology :
      HomologicalFourManifoldTopologyBoundary theory geometry)
    (evaluation : PresentationEvaluation theory K) :
    PresentationFormula topology.admissibleCalculus K where
  value := fun presentation =>
    evaluation.markedValue presentation.markedPresentation

/--
Local invariance along elementary moves proves invariance along every movie
used by the homological topology boundary.
-/
theorem admissibleFormula_movieInvariant
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    {K : Type uK}
    (topology :
      HomologicalFourManifoldTopologyBoundary theory geometry)
    (evaluation : PresentationEvaluation theory K)
    (localInvariant : IsInvariantUnderElementaryMoves evaluation) :
    IsInvariantAlongAdmissibleMovies
      (topology.admissibleFormula evaluation) := by
  intro source target diffeomorphism sourcePresentation targetPresentation
    movie
  exact evaluation.respectsKirbyMovie localInvariant movie

/--
Any locally invariant presentation formula therefore constructs a genuine
invariant whose public arguments are exactly `X` and `alpha : H₂(X; ℤ)`.
-/
noncomputable def constructInvariant
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    {K : Type uK}
    (topology :
      HomologicalFourManifoldTopologyBoundary theory geometry)
    (evaluation : PresentationEvaluation theory K)
    (localInvariant : IsInvariantUnderElementaryMoves evaluation) :
    HomologicalFourManifoldInvariant geometry K :=
  topology.admissibleKirbyCerfTheorem.constructInvariant
    (topology.admissibleFormula evaluation)
    (topology.admissibleFormula_movieInvariant evaluation localInvariant)

/-- The manifold-level invariant recovers the original presentation formula. -/
theorem constructInvariant_on_presentation
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    {K : Type uK}
    (topology :
      HomologicalFourManifoldTopologyBoundary theory geometry)
    (evaluation : PresentationEvaluation theory K)
    (localInvariant : IsInvariantUnderElementaryMoves evaluation)
    (marked : theory.MarkedPresentation) :
    (topology.constructInvariant evaluation localInvariant).EvalC
        (topology.realization.underlyingManifold marked.presentation)
        (topology.realization.secondHomologyEquiv
          marked.presentation marked.marking) =
      evaluation.markedValue marked := by
  exact
    topology.admissibleKirbyCerfTheorem.constructInvariant_EvalC_eq_presentation
      (topology.admissibleFormula evaluation)
      (topology.admissibleFormula_movieInvariant evaluation localInvariant)
      (topology.realization.underlyingManifold marked.presentation)
      (topology.realization.secondHomologyEquiv
        marked.presentation marked.marking)
      (topology.realization.selfPresentation marked)

end HomologicalFourManifoldTopologyBoundary

end TwistedYetter.Kirby.LiteratureBackedHomologicalFourManifoldTopology
