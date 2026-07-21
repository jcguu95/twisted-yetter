import TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget

/-!
# Literature boundary for closed four-manifold topology

This module records exactly where the formalization stops before rebuilding
smooth manifolds, Morse functions, and Cerf theory from foundations.

The four fields below are the topology statements imported from the standard
literature:

1. a marked special handle presentation realizes a marked closed oriented
   smooth four-manifold;
2. every elementary marked Kirby move realizes an oriented diffeomorphism;
3. every marked closed oriented smooth four-manifold has a special handle
   presentation; and
4. two presentations of diffeomorphic marked manifolds are connected by a
   Kirby--Cerf movie.

They are deliberately assumptions in the theorem signature rather than one
omnibus project axiom.  In particular, none of them may mention a category,
an evaluator, a scalar value, or equality of scalar values.

Source boundary:

* Gompf--Stipsicz, Theorem 4.2.12 and Section 5.1;
* Bärenz--Barrett, paragraph before Theorem 3.9, Theorem 3.9,
  Table 2, and Remark 3.10, journal pages 685--687;
* de Sá, *A link calculus for 4-manifolds*, pages 16--30;
* Laudenbach--Poénaru, *A note on 4-dimensional handlebodies*.

Lean proves all descent, quotient, and diffeomorphism-invariance statements
after this boundary.  Lean does not prove the four imported differential
topology statements in this module.
-/

namespace TwistedYetter.Kirby.LiteratureBackedFourManifoldTopology

open TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget

universe uK uP uM uMove uX uXHom

/-- The four separately reviewable topology assumptions used in the paper. -/
inductive AssumptionClass where
  | markedRealization
  | elementaryMoveSoundness
  | markedPresentationExistence
  | markedKirbyCerfCompleteness
  deriving Repr, BEq, DecidableEq

/-- Machine-visible denominator of the imported topology statements. -/
def requiredAssumptionClasses : List AssumptionClass :=
  [
    .markedRealization,
    .elementaryMoveSoundness,
    .markedPresentationExistence,
    .markedKirbyCerfCompleteness
  ]

theorem required_assumption_class_count :
    requiredAssumptionClasses.length = 4 := by
  rfl

theorem required_assumption_classes_unique :
    requiredAssumptionClasses.Nodup := by
  decide

/-- Stable source references for the four imported topology statements. -/
def sourceRefs : List String :=
  [
    "ref:gompf-stipsicz-4-manifolds-kirby-calculus",
    "ref:baerenz-barrett-dichromatic-2018",
    "ref:de-sa-link-calculus-1979",
    "ref:laudenbach-poenaru-4d-handlebodies-1972"
  ]

/--
One reviewable citation for one imported topology statement.

This is audit metadata, not mathematical evidence inside `Assumptions`.
In particular, a citation cannot manufacture a realization, a move, a
diffeomorphism, or a Kirby movie.
-/
structure AssumptionCitation where
  assumptionClass : AssumptionClass
  sourceRef : String
  sourceLocator : String
  exactImportedStatement : String
  deriving Repr

/-- Exact source locator selected for each of the four imported statements. -/
def assumptionCitations : List AssumptionCitation :=
  [
    {
      assumptionClass := .markedRealization
      sourceRef := "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
      sourceLocator :=
        "Definition 4.2.1, Proposition 4.2.13, and Section 5.1"
      exactImportedStatement :=
        "A marked special handle presentation has a geometric realization "
          ++ "as a marked closed oriented smooth four-manifold."
    },
    {
      assumptionClass := .elementaryMoveSoundness
      sourceRef := "ref:baerenz-barrett-dichromatic-2018"
      sourceLocator :=
        "Table 2 and Theorem 3.9, journal pages 685-687"
      exactImportedStatement :=
        "Each listed elementary special-Kirby move induces an "
          ++ "orientation-preserving diffeomorphism of the realization."
    },
    {
      assumptionClass := .markedPresentationExistence
      sourceRef := "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
      sourceLocator :=
        "Morse handle existence and Proposition 4.2.13"
      exactImportedStatement :=
        "Every marked closed oriented smooth four-manifold in scope admits "
          ++ "a marked special handle presentation."
    },
    {
      assumptionClass := .markedKirbyCerfCompleteness
      sourceRef := "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
      sourceLocator :=
        "Theorem 4.2.12 and Section 5.1; compare "
          ++ "Bärenz-Barrett Theorem 3.9 and de Sá pages 16-30"
      exactImportedStatement :=
        "An oriented diffeomorphism between marked realizations is "
          ++ "represented by a finite movie of the admitted marked moves."
    }
  ]

theorem assumption_citation_count :
    assumptionCitations.length = 4 := by
  rfl

/-- Every required statement class has exactly one selected primary locator. -/
theorem assumption_citations_cover_required_classes :
    assumptionCitations.map AssumptionCitation.assumptionClass =
      requiredAssumptionClasses := by
  rfl

/--
The exact topology boundary accepted by the final modular theorem.

This structure is intentionally mathematical data only.  It has no
provenance metadata and no evaluator field.  The source locators live in the
module documentation and the repository reference ledger.
-/
structure Assumptions
    (theory : HandlePresentationTheory.{uP, uM, uMove}) where
  realization :
    MarkedFourManifoldRealization.{uP, uM, uMove, uX, uXHom} theory
  elementaryMoveSoundness :
    ElementaryMoveGeometricSoundness realization
  markedPresentationExistence :
    MarkedPresentationExistence realization
  markedKirbyCerfCompleteness :
    MarkedKirbyCerfCompleteness realization

namespace Assumptions

/--
The literature boundary identifies marked Kirby classes with oriented
diffeomorphism classes.  The equivalence itself is derived in Lean.
-/
def kirbyClassEquivDiffeomorphismClass
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    (topology : Assumptions.{uP, uM, uMove, uX, uXHom} theory) :
    theory.KirbyClass ≃ topology.realization.DiffeomorphismClass :=
  TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget.kirbyClassEquivDiffeomorphismClass
    topology.elementaryMoveSoundness
    topology.markedPresentationExistence
    topology.markedKirbyCerfCompleteness

/--
Any locally Kirby-invariant presentation evaluation therefore defines an
actual invariant of marked closed oriented smooth four-manifolds.
-/
def fourManifoldInvariant
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    (topology : Assumptions.{uP, uM, uMove, uX, uXHom} theory)
    (evaluation : PresentationEvaluation theory K)
    (localInvariant : IsInvariantUnderElementaryMoves evaluation) :
    topology.realization.MarkedClosedOrientedSmoothFourManifold → K :=
  TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget.fourManifoldInvariant
    topology.elementaryMoveSoundness
    topology.markedPresentationExistence
    topology.markedKirbyCerfCompleteness
    evaluation localInvariant

/-- The resulting function is constant under oriented diffeomorphism. -/
theorem fourManifoldInvariant_diffeomorphism_invariant
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    (topology : Assumptions.{uP, uM, uMove, uX, uXHom} theory)
    (evaluation : PresentationEvaluation theory K)
    (localInvariant : IsInvariantUnderElementaryMoves evaluation)
    {left right :
      topology.realization.MarkedClosedOrientedSmoothFourManifold}
    (diffeomorphism :
      topology.realization.orientedDiffeomorphism.Hom left right) :
    topology.fourManifoldInvariant evaluation localInvariant left =
      topology.fourManifoldInvariant evaluation localInvariant right :=
  TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget.fourManifoldInvariant_diffeomorphism_invariant
    topology.elementaryMoveSoundness
    topology.markedPresentationExistence
    topology.markedKirbyCerfCompleteness
    evaluation localInvariant diffeomorphism

/-- Pullback along realization recovers the original presentation formula. -/
theorem fourManifoldInvariant_on_presentation
    {theory : HandlePresentationTheory.{uP, uM, uMove}}
    (topology : Assumptions.{uP, uM, uMove, uX, uXHom} theory)
    (evaluation : PresentationEvaluation theory K)
    (localInvariant : IsInvariantUnderElementaryMoves evaluation)
    (marked : theory.MarkedPresentation) :
    topology.fourManifoldInvariant evaluation localInvariant
        (topology.realization.realize marked) =
      evaluation.markedValue marked :=
  TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget.fourManifoldInvariant_on_presentation
    topology.elementaryMoveSoundness
    topology.markedPresentationExistence
    topology.markedKirbyCerfCompleteness
    evaluation localInvariant marked

end Assumptions

end TwistedYetter.Kirby.LiteratureBackedFourManifoldTopology
