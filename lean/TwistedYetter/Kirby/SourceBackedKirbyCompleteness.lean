import TwistedYetter.Kirby.KirbyCompleteness

/-!
# Source-backed special Kirby completeness

This module isolates one topology domain axiom from all evaluator and marked
homology data.

Bärenz--Barrett, immediately before Theorem 3.9, state that two handle
decompositions of the same manifold are related by handle slides and
cancellations, and that the relevant four-dimensional link moves are exactly
those in their Table 2.  Their proof of Theorem 3.9 checks those five move
families, and Remark 3.10 concludes independence of the special framed link.
They cite Gompf--Stipsicz Theorem 4.2.12 and Section 5.1, and de Sá's link
calculus.

Lean does not re-prove that topology theorem.  The sole custom axiom below
returns only an unmarked topology movie.  It does not provide:

* an evaluator equality;
* a chain map or a map on `H2`;
* a marked-class compatibility proof; or
* a Crane--Yetter identification.

An independent enrichment compiler must add chain-derived `H2` data before
the existing R11 presentation-independence theorem can be applied.
-/

namespace TwistedYetter.Kirby.SourceBackedKirbyCompleteness

open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uH

/-- Stable source IDs for the single topology domain axiom. -/
def sourceRefs : List String :=
  [
    "ref:baerenz-barrett-dichromatic-2018",
    "ref:gompf-stipsicz-4-manifolds-kirby-calculus",
    "ref:de-sa-link-calculus-1979"
  ]

/-- Exact source locator used for the domain axiom. -/
def sourceLocator : String :=
  "Bärenz-Barrett, paragraph before Theorem 3.9, Theorem 3.9, "
    ++ "Table 2, and Remark 3.10, journal pages 685-687; "
    ++ "Gompf-Stipsicz Theorem 4.2.12 and Section 5.1; "
    ++ "de Sá, A link calculus for 4-manifolds, pages 16-30"

/-- The scope deliberately excludes arbitrary links and relative manifolds. -/
def exactScope : String :=
  "Special framed links obtained from handle decompositions of smooth, "
    ++ "oriented, closed, connected four-manifolds, with one 0-handle and "
    ++ "one 4-handle; framed isotopy, 1-over-1, 2-over-1, 2-over-2, "
    ++ "1-2 cancellation, and 2-3 cancellation."

/-- The exact limitation of the imported topology fact. -/
def sourceScopeCaveat : String :=
  "This axiom asserts only connectivity by the listed topology moves. "
    ++ "It does not assert evaluator invariance, chain-level H2 transport, "
    ++ "or correctness of any concrete presentation certificate."

/--
The five Table 2 topology families plus framed-link presentation isotopy,
without marked-homology transport.
-/
inductive TopologicalTableTwoMove
    {H2 : Type uH} [AddCommGroup H2] :
    SpecialKirbyPresentation H2 →
      SpecialKirbyPresentation H2 → Type (uH + 1)
  | framedIsotopy
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .framedIsotopy source target)
      (counts_sound : source.counts = target.counts) :
      TopologicalTableTwoMove source target
  | oneOverOne
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .oneOverOne source target)
      (counts_sound : source.counts = target.counts) :
      TopologicalTableTwoMove source target
  | twoOverOne
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .twoOverOne source target)
      (counts_sound : source.counts = target.counts) :
      TopologicalTableTwoMove source target
  | twoOverTwo
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .twoOverTwo source target)
      (counts_sound : source.counts = target.counts) :
      TopologicalTableTwoMove source target
  | oneTwoBirth
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .oneTwoBirth source target)
      (counts_sound : target.counts = source.counts.addOneTwo) :
      TopologicalTableTwoMove source target
  | oneTwoDeath
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .oneTwoDeath source target)
      (counts_sound : source.counts = target.counts.addOneTwo) :
      TopologicalTableTwoMove source target
  | twoThreeBirth
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .twoThreeBirth source target)
      (counts_sound : target.counts = source.counts.addTwoThree) :
      TopologicalTableTwoMove source target
  | twoThreeDeath
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .twoThreeDeath source target)
      (counts_sound : source.counts = target.counts.addTwoThree) :
      TopologicalTableTwoMove source target

/-- A finite movie made only from the source-backed topology whitelist. -/
inductive TopologicalTableTwoMovie
    {H2 : Type uH} [AddCommGroup H2] :
    SpecialKirbyPresentation H2 →
      SpecialKirbyPresentation H2 → Type (uH + 1)
  | refl (presentation : SpecialKirbyPresentation H2) :
      TopologicalTableTwoMovie presentation presentation
  | step
      {source target : SpecialKirbyPresentation H2}
      (move : TopologicalTableTwoMove source target) :
      TopologicalTableTwoMovie source target
  | trans
      {source middle target : SpecialKirbyPresentation H2}
      (first : TopologicalTableTwoMovie source middle)
      (second : TopologicalTableTwoMovie middle target) :
      TopologicalTableTwoMovie source target

/-- Forget the chain-derived marked-homology enrichment of one move. -/
def forgetMoveTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (move : TableTwoMove source target) :
    TopologicalTableTwoMove source target := by
  cases move with
  | framedIsotopy metadata counts _ =>
      exact .framedIsotopy metadata counts
  | oneOverOne metadata counts _ =>
      exact .oneOverOne metadata counts
  | twoOverOne metadata counts _ =>
      exact .twoOverOne metadata counts
  | twoOverTwo metadata counts _ =>
      exact .twoOverTwo metadata counts
  | oneTwoBirth metadata counts _ =>
      exact .oneTwoBirth metadata counts
  | oneTwoDeath metadata counts _ =>
      exact .oneTwoDeath metadata counts
  | twoThreeBirth metadata counts _ =>
      exact .twoThreeBirth metadata counts
  | twoThreeDeath metadata counts _ =>
      exact .twoThreeDeath metadata counts

/-- Forget marked-homology enrichment throughout a movie. -/
noncomputable def forgetMovieTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (movie : TableTwoMovie source target) :
    TopologicalTableTwoMovie source target :=
  match movie with
  | .refl presentation =>
      .refl presentation
  | .step move =>
      .step (forgetMoveTransport move)
  | .trans first second =>
      .trans (forgetMovieTransport first) (forgetMovieTransport second)

/--
The sole imported special-Kirby topology axiom.

This is the formal boundary corresponding to the cited standard theorem.  It
returns no chain equivalence and no evaluator statement.
-/
axiom standardSpecialKirbyPresentationsConnected
    {H2 : Type uH} [AddCommGroup H2]
    (source target : SpecialKirbyPresentation H2) :
    TopologicalTableTwoMovie source target

/-- The source-backed topology interface, containing no evaluator field. -/
structure TopologicalTableTwoCompleteness
    (H2 : Type uH) [AddCommGroup H2] where
  connected :
    (source target : SpecialKirbyPresentation H2) →
      TopologicalTableTwoMovie source target

/-- The canonical instance backed by the single visible domain axiom. -/
noncomputable def sourceBackedTopologicalCompleteness
    (H2 : Type uH) [AddCommGroup H2] :
    TopologicalTableTwoCompleteness H2 where
  connected := standardSpecialKirbyPresentationsConnected

/--
The concrete assembly boundary for marked homology, reduced to one local
obligation per topology move.

The output is an actual `MarkedH2Transport`, so its map on second homology is
forced by a chain homotopy equivalence.
-/
structure LocalMarkedH2Compiler
    (H2 : Type uH) [AddCommGroup H2] where
  transport :
    {source target : SpecialKirbyPresentation H2} →
      TopologicalTableTwoMove source target →
        MarkedH2Transport source target

/-- Reattach chain-derived marked-homology data to one topology move. -/
def enrichMove
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : LocalMarkedH2Compiler H2)
    {source target : SpecialKirbyPresentation H2}
    (move : TopologicalTableTwoMove source target) :
    TableTwoMove source target := by
  cases move with
  | framedIsotopy metadata counts =>
      exact .framedIsotopy metadata counts
        (compiler.transport (.framedIsotopy metadata counts))
  | oneOverOne metadata counts =>
      exact .oneOverOne metadata counts
        (compiler.transport (.oneOverOne metadata counts))
  | twoOverOne metadata counts =>
      exact .twoOverOne metadata counts
        (compiler.transport (.twoOverOne metadata counts))
  | twoOverTwo metadata counts =>
      exact .twoOverTwo metadata counts
        (compiler.transport (.twoOverTwo metadata counts))
  | oneTwoBirth metadata counts =>
      exact .oneTwoBirth metadata counts
        (compiler.transport (.oneTwoBirth metadata counts))
  | oneTwoDeath metadata counts =>
      exact .oneTwoDeath metadata counts
        (compiler.transport (.oneTwoDeath metadata counts))
  | twoThreeBirth metadata counts =>
      exact .twoThreeBirth metadata counts
        (compiler.transport (.twoThreeBirth metadata counts))
  | twoThreeDeath metadata counts =>
      exact .twoThreeDeath metadata counts
        (compiler.transport (.twoThreeDeath metadata counts))

/-- Local enrichment preserves the exact topology constructor and metadata. -/
theorem forget_enrichMove
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : LocalMarkedH2Compiler H2)
    {source target : SpecialKirbyPresentation H2}
    (move : TopologicalTableTwoMove source target) :
    forgetMoveTransport (enrichMove compiler move) = move := by
  cases move <;> rfl

/-- Recursively enrich a whole source-backed topology movie. -/
noncomputable def enrichMovie
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : LocalMarkedH2Compiler H2)
    {source target : SpecialKirbyPresentation H2}
    (movie : TopologicalTableTwoMovie source target) :
    TableTwoMovie source target :=
  match movie with
  | .refl presentation =>
      .refl presentation
  | .step move =>
      .step (enrichMove compiler move)
  | .trans first second =>
      .trans (enrichMovie compiler first) (enrichMovie compiler second)

/-- Whole-movie enrichment leaves the source topology movie unchanged. -/
theorem forget_enrichMovie
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : LocalMarkedH2Compiler H2)
    {source target : SpecialKirbyPresentation H2}
    (movie : TopologicalTableTwoMovie source target) :
    forgetMovieTransport (enrichMovie compiler movie) = movie := by
  induction movie with
  | refl presentation =>
      rfl
  | step move =>
      simp only [enrichMovie, forgetMovieTransport, forget_enrichMove]
  | trans first second firstIH secondIH =>
      simp only [enrichMovie, forgetMovieTransport, firstIH, secondIH]

/--
The still-open bridge from a topology movie to a movie carrying actual handle
chain equivalences.  Its law prevents changing the underlying topology movie.
-/
structure TableTwoMovieEnrichment
    (H2 : Type uH) [AddCommGroup H2] where
  enrich :
    {source target : SpecialKirbyPresentation H2} →
      TopologicalTableTwoMovie source target →
        TableTwoMovie source target
  forget_sound :
    {source target : SpecialKirbyPresentation H2} →
    (movie : TopologicalTableTwoMovie source target) →
      forgetMovieTransport (enrich movie) = movie

/-- Build the whole-movie enrichment from local chain data. -/
noncomputable def movieEnrichmentOfLocalCompiler
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : LocalMarkedH2Compiler H2) :
    TableTwoMovieEnrichment H2 where
  enrich := enrichMovie compiler
  forget_sound := forget_enrichMovie compiler

/--
Combine the source-backed topology axiom with independently constructed chain
enrichment.  No evaluator data enters this construction.
-/
noncomputable def buildTableTwoLinkCompleteness
    {H2 : Type uH} [AddCommGroup H2]
    (general : GeneralCerfCompleteness)
    (enrichment : TableTwoMovieEnrichment H2) :
    TableTwoLinkCompleteness H2 where
  generalCerf := general
  tableTwoConnected := fun source target =>
    enrichment.enrich
      (standardSpecialKirbyPresentationsConnected source target)
  link_calculus_source_refs := sourceRefs
  link_calculus_source_locator := sourceLocator
  normal_form_statement := exactScope
  exact_move_scope := exactScope
  source_scope_caveat := sourceScopeCaveat

end TwistedYetter.Kirby.SourceBackedKirbyCompleteness
