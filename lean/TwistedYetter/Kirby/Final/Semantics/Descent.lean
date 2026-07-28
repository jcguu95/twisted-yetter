import TwistedYetter.Kirby.Final.Semantics.Evaluator

/-!
# Formal descent to a diffeomorphism invariant

This layer contains only the finite-movie induction and choice-independent
descent from the explicitly named semantic obligations.
-/

namespace TwistedYetter.Kirby.Final.SemanticSpecification

universe uX uH uD uP uK uM

variable {K : Type uK} [Field K]
variable {S : Type} [Fintype S] [DecidableEq S]

/-! ## Formal descent from the semantic obligations -/

/-- Elementary invariance extends to every finite Kirby movie. -/
theorem preservesKirbyMovie
    {topology : ClosedFourManifoldSemantics}
    {AlgebraicInput : Type uM}
    {Presentation : PresentationFamily.{uX, uP} topology}
    (realization : PresentationRealization topology Presentation)
    (view : ExactPresentationView realization)
    (evaluator :
      RoleAwareEvaluator
        (K := K) (S := S) AlgebraicInput Presentation realization)
    (elementaryInvariant :
      PreservesElementaryMoves realization view evaluator)
    (algebra : AlgebraicInput)
    {X : topology.Manifold}
    {source target : Presentation X}
    (movie : KirbyMovie view source target)
    (α : topology.H₂ X) :
    evaluator.value algebra source α =
      evaluator.value algebra target α := by
  induction movie with
  | refl => rfl
  | elementary move =>
      exact elementaryInvariant algebra move α
  | symm _ inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

/-- Choose one admissible presentation and evaluate it. -/
noncomputable def descendedValue
    {topology : ClosedFourManifoldSemantics}
    {AlgebraicInput : Type uM}
    {Presentation : PresentationFamily.{uX, uP} topology}
    (existence : PresentationExistence Presentation)
    (realization : PresentationRealization topology Presentation)
    (evaluator :
      RoleAwareEvaluator
        (K := K) (S := S) AlgebraicInput Presentation realization)
    (algebra : AlgebraicInput)
    (Xα : HomologicalFourManifold topology) :
    K :=
  evaluator.value algebra (Classical.choice (existence Xα.1)) Xα.2

/--
Presentation existence, honest reindexing, marked Kirby--Cerf completeness,
and the local calculations imply an intrinsic diffeomorphism invariant.
-/
theorem descendedValue_diffeomorphism_invariant
    {topology : ClosedFourManifoldSemantics}
    {AlgebraicInput : Type uM}
    {Presentation : PresentationFamily.{uX, uP} topology}
    (existence : PresentationExistence Presentation)
    (realization : PresentationRealization topology Presentation)
    (view : ExactPresentationView realization)
    (reindexing : PresentationReindexing Presentation)
    (kirbyCerf : KirbyCerfComplete view reindexing)
    (evaluator :
      RoleAwareEvaluator
        (K := K) (S := S) AlgebraicInput Presentation realization)
    (reindexInvariant :
      PreservesReindexing realization reindexing evaluator)
    (elementaryInvariant :
      PreservesElementaryMoves realization view evaluator) :
    DiffeomorphismInvariant topology AlgebraicInput K
      (descendedValue existence realization evaluator) := by
  intro algebra X Y f α
  let source : Presentation X := Classical.choice (existence X)
  let target : Presentation Y := Classical.choice (existence Y)
  rcases kirbyCerf f source target α with ⟨markedMovie⟩
  calc
    evaluator.value algebra source α =
        evaluator.value algebra (reindexing.reindex f source)
          (topology.inducedH₂ f α) :=
      reindexInvariant algebra f source α
    _ = evaluator.value algebra target (topology.inducedH₂ f α) :=
      preservesKirbyMovie realization view evaluator elementaryInvariant
        algebra markedMovie.movie (topology.inducedH₂ f α)

end TwistedYetter.Kirby.Final.SemanticSpecification

