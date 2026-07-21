import TwistedYetter.Kirby.LiteratureBackedFourManifoldTopology
import TwistedYetter.Kirby.SourceBackedHandleChainNaturality

/-!
# Complete literature boundary for the modular Kirby route

This module gives one machine-visible denominator for all external
four-manifold and handle-homology statements used by the canonical modular
route.

There are two deliberately different groups:

* four smooth-topology correspondence statements, passed explicitly through
  `LiteratureBackedFourManifoldTopology.Assumptions`; and
* one handle-chain naturality statement, isolated as
  `SourceBackedHandleChainNaturality.standardHandleChainNaturalityInput`.

The fifth item does not say that an evaluator is invariant.  It supplies an
actual chain-homotopy equivalence and its coordinate-naturality square for
each source-bound topology move.  Lean derives the resulting map on second
homology and proves that it is the identity in the common geometric
coordinates.

Lean does not reconstruct smooth manifolds, Morse functions, attaching maps,
boundary matrices, or Cerf movies below this boundary.
-/

namespace TwistedYetter.Kirby.LiteratureBackedFourManifoldInputs

/-- Complete external-statement denominator, with layer distinctions visible. -/
inductive ImportedStatementClass where
  | markedRealization
  | elementaryMoveSoundness
  | markedPresentationExistence
  | markedKirbyCerfCompleteness
  | handleChainNaturality
  deriving Repr, BEq, DecidableEq

/-- Every external four-manifold/handle-homology statement used downstream. -/
def requiredImportedStatementClasses : List ImportedStatementClass :=
  [
    .markedRealization,
    .elementaryMoveSoundness,
    .markedPresentationExistence,
    .markedKirbyCerfCompleteness,
    .handleChainNaturality
  ]

theorem required_imported_statement_class_count :
    requiredImportedStatementClasses.length = 5 := by
  rfl

theorem required_imported_statement_classes_unique :
    requiredImportedStatementClasses.Nodup := by
  decide

/-- The first four items are smooth-topology correspondence statements. -/
def smoothTopologyStatementClasses : List ImportedStatementClass :=
  [
    .markedRealization,
    .elementaryMoveSoundness,
    .markedPresentationExistence,
    .markedKirbyCerfCompleteness
  ]

theorem smooth_topology_statement_class_count :
    smoothTopologyStatementClasses.length = 4 := by
  rfl

/-- The fifth item is homological naturality, not a fifth Cerf theorem. -/
def handleHomologyStatementClasses : List ImportedStatementClass :=
  [.handleChainNaturality]

theorem handle_homology_statement_class_count :
    handleHomologyStatementClasses.length = 1 := by
  rfl

/-- The fifth imported statement and its exact, separately audited locator. -/
def handleChainNaturalitySourceLocator : String :=
  "Gompf-Stipsicz, handle chain complex in Section 4.2 and elementary "
    ++ "handle moves in Theorem 4.2.12; Bärenz-Barrett Table 2, "
    ++ "journal page 686"

/--
The complete five-item denominator is the four smooth statements followed by
the one handle-chain statement.  This theorem prevents the fifth item from
being silently folded into the four-manifold realization assumption.
-/
theorem complete_imported_statement_partition :
    smoothTopologyStatementClasses ++ handleHomologyStatementClasses =
      requiredImportedStatementClasses := by
  rfl

/-- Stable references covering the complete imported boundary. -/
def sourceRefs : List String :=
  [
    "ref:gompf-stipsicz-4-manifolds-kirby-calculus",
    "ref:baerenz-barrett-dichromatic-2018",
    "ref:de-sa-link-calculus-1979",
    "ref:laudenbach-poenaru-4d-handlebodies-1972"
  ]

end TwistedYetter.Kirby.LiteratureBackedFourManifoldInputs
