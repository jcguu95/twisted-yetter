import TwistedYetter.Kirby.SourceBoundGeometricH2Compiler

/-!
# Source-backed handle-chain naturality

This module isolates the standard homology-domain input needed by the marked
Kirby construction.

For an admitted local Kirby move, the cellular handle complexes before and
after the move are related by the familiar basis change or by insertion /
removal of a contractible adjacent-handle summand.  The induced map agrees
with the common geometric `H2(X)` coordinates.

That handle-theoretic statement is not reconstructed here from attaching
maps.  It is one explicit domain axiom below.  In particular, the axiom
returns the actual chain homotopy equivalence and its coordinate-naturality
square; it does not return the final identity map on `H2`.

The downstream identity is still a kernel-checked consequence of
`SourceBoundChainMoveCertificate.transport_homologyAddEquiv_eq_refl`.
-/

namespace TwistedYetter.Kirby.SourceBackedHandleChainNaturality

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness
open TwistedYetter.Kirby.SourceBoundGeometricH2Compilation
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uH

/-- The cycle obtained from the forward map of a handle-chain equivalence. -/
noncomputable def forwardDegreeTwoCycle
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (equivalence :
      HandleChainEquivalence source.handleChain target.handleChain)
    (cycle : source.DegreeTwoCycle) :
    target.DegreeTwoCycle :=
  (HomologicalComplex.cyclesMap equivalence.homotopyEquiv.hom 2) cycle

/-- The cycle obtained from the inverse map of a handle-chain equivalence. -/
noncomputable def backwardDegreeTwoCycle
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (equivalence :
      HandleChainEquivalence source.handleChain target.handleChain)
    (cycle : target.DegreeTwoCycle) :
    source.DegreeTwoCycle :=
  (HomologicalComplex.cyclesMap equivalence.homotopyEquiv.inv 2) cycle

/--
Exact degree-two coordinate law for inserting a cancelling handle summand.

This is topology data: the old coordinates are retained and every newly
inserted two-handle coordinate is zero on the transported cycle.
-/
structure ForwardAddedDegreeTwoNaturality
    {H2 : Type uH} [AddCommGroup H2]
    (source target : SpecialKirbyPresentation H2)
    (addedCount : Nat)
    (change :
      AddedComponentIndexChange source.formal target.formal addedCount)
    (equivalence :
      HandleChainEquivalence source.handleChain target.handleChain) where
  common_exponent_sound :
    (sourceCycle : source.DegreeTwoCycle) →
    (sourceIndex : ComponentIndex source.formal) →
      target.cycleComponentExponent
          (forwardDegreeTwoCycle equivalence sourceCycle)
          (componentAt target.formal
            (change.targetDecomposition.symm (Sum.inl sourceIndex))) =
        source.cycleComponentExponent sourceCycle
          (componentAt source.formal sourceIndex)
  added_exponent_zero :
    (sourceCycle : source.DegreeTwoCycle) →
    (addedIndex : Fin addedCount) →
      target.cycleComponentExponent
          (forwardDegreeTwoCycle equivalence sourceCycle)
          (componentAt target.formal
            (change.targetDecomposition.symm (Sum.inr addedIndex))) =
        0

/--
Exact degree-two coordinate law for deleting a cancelling handle summand,
read backwards along the inverse chain equivalence.
-/
structure BackwardRemovedDegreeTwoNaturality
    {H2 : Type uH} [AddCommGroup H2]
    (source target : SpecialKirbyPresentation H2)
    (removedCount : Nat)
    (change :
      RemovedComponentIndexChange source.formal target.formal removedCount)
    (equivalence :
      HandleChainEquivalence source.handleChain target.handleChain) where
  common_exponent_sound :
    (targetCycle : target.DegreeTwoCycle) →
    (targetIndex : ComponentIndex target.formal) →
      source.cycleComponentExponent
          (backwardDegreeTwoCycle equivalence targetCycle)
          (componentAt source.formal
            (change.sourceDecomposition.symm (Sum.inl targetIndex))) =
        target.cycleComponentExponent targetCycle
          (componentAt target.formal targetIndex)
  removed_exponent_zero :
    (targetCycle : target.DegreeTwoCycle) →
    (removedIndex : Fin removedCount) →
      source.cycleComponentExponent
          (backwardDegreeTwoCycle equivalence targetCycle)
          (componentAt source.formal
            (change.sourceDecomposition.symm (Sum.inr removedIndex))) =
        0

/--
Exact degree-two coordinate law for a framed isotopy with unchanged
components.

The component correspondence is supplied by the source-bound recipe.  The
transported cycle retains the coefficient attached to each corresponding
two-handle component.
-/
structure ForwardSameDegreeTwoNaturality
    {H2 : Type uH} [AddCommGroup H2]
    (source target : SpecialKirbyPresentation H2)
    (change : SameComponentIndexChange source.formal target.formal)
    (equivalence :
      HandleChainEquivalence source.handleChain target.handleChain) where
  exponent_sound :
    (sourceCycle : source.DegreeTwoCycle) →
    (targetIndex : ComponentIndex target.formal) →
      target.cycleComponentExponent
          (forwardDegreeTwoCycle equivalence sourceCycle)
          (componentAt target.formal targetIndex) =
        source.cycleComponentExponent sourceCycle
          (componentAt source.formal
            (change.targetToSource targetIndex))

/-- Extract the unchanged-component correspondence from a framed isotopy. -/
def framedIsotopySameChangeOfEdit
    {source target : FormalPresentation}
    (edit : HandleEdit .framedIsotopy)
    (change : ComponentIndexChange source target edit) :
    SameComponentIndexChange source target :=
  match edit, change with
  | .framedIsotopy _ _,
      .framedIsotopy _ _ same =>
      same

/-- Unchanged-component correspondence retained by a framed-isotopy recipe. -/
def framedIsotopySameChange
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (metadata :
      TableTwoMoveMetadata .framedIsotopy source target) :
    SameComponentIndexChange source.formal target.formal :=
  framedIsotopySameChangeOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- Extract the unchanged-component correspondence from a 2-over-2 slide. -/
def twoOverTwoSameChangeOfEdit
    {source target : FormalPresentation}
    (edit : HandleEdit .twoOverTwo)
    (change : ComponentIndexChange source target edit) :
    SameComponentIndexChange source target :=
  match edit, change with
  | .twoOverTwo _ _ _ _,
      .twoOverTwo _ _ _ _ same _ _ _ =>
      same

/-- Unchanged-component correspondence retained by a 2-over-2 recipe. -/
def twoOverTwoSameChange
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source target) :
    SameComponentIndexChange source.formal target.formal :=
  twoOverTwoSameChangeOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- Extract the added-component correspondence from a 1--2 birth edit. -/
def oneTwoBirthAddedChangeOfEdit
    {source target : FormalPresentation}
    (edit : HandleEdit .oneTwoBirth)
    (change : ComponentIndexChange source target edit) :
    AddedComponentIndexChange source target 2 :=
  match edit, change with
  | .oneTwoBirth _ _ _,
      .oneTwoBirth _ _ _ added _ _ _ _ =>
      added

/-- Added-component correspondence retained by a 1--2 birth recipe. -/
def oneTwoBirthAddedChange
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth source target) :
    AddedComponentIndexChange source.formal target.formal 2 :=
  oneTwoBirthAddedChangeOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- Extract the removed-component correspondence from a 1--2 death edit. -/
def oneTwoDeathRemovedChangeOfEdit
    {source target : FormalPresentation}
    (edit : HandleEdit .oneTwoDeath)
    (change : ComponentIndexChange source target edit) :
    RemovedComponentIndexChange source target 2 :=
  match edit, change with
  | .oneTwoDeath _ _ _,
      .oneTwoDeath _ _ _ removed _ _ _ _ =>
      removed

/-- Removed-component correspondence retained by a 1--2 death recipe. -/
def oneTwoDeathRemovedChange
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath source target) :
    RemovedComponentIndexChange source.formal target.formal 2 :=
  oneTwoDeathRemovedChangeOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- Extract the added-component correspondence from a 2--3 birth edit. -/
def twoThreeBirthAddedChangeOfEdit
    {source target : FormalPresentation}
    (edit : HandleEdit .twoThreeBirth)
    (change : ComponentIndexChange source target edit) :
    AddedComponentIndexChange source target 1 :=
  match edit, change with
  | .twoThreeBirth _,
      .twoThreeBirth _ added _ _ =>
      added

/-- Added-component correspondence retained by a 2--3 birth recipe. -/
def twoThreeBirthAddedChange
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth source target) :
    AddedComponentIndexChange source.formal target.formal 1 :=
  twoThreeBirthAddedChangeOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- Extract the removed-component correspondence from a 2--3 death edit. -/
def twoThreeDeathRemovedChangeOfEdit
    {source target : FormalPresentation}
    (edit : HandleEdit .twoThreeDeath)
    (change : ComponentIndexChange source target edit) :
    RemovedComponentIndexChange source target 1 :=
  match edit, change with
  | .twoThreeDeath _,
      .twoThreeDeath _ removed _ _ =>
      removed

/-- Removed-component correspondence retained by a 2--3 death recipe. -/
def twoThreeDeathRemovedChange
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath source target) :
    RemovedComponentIndexChange source.formal target.formal 1 :=
  twoThreeDeathRemovedChangeOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- Stable references delimiting the imported handle-homology fact. -/
def sourceRefs : List String :=
  [
    "ref:gompf-stipsicz-4-manifolds-kirby-calculus",
    "ref:baerenz-barrett-dichromatic-2018"
  ]

/-- Exact mathematical content imported at this boundary. -/
def exactScope : String :=
  "For each certified framed-isotopy, handle-slide, or adjacent cancelling "
    ++ "pair move between special handle presentations of one fixed closed "
    ++ "oriented four-manifold, the associated integral handle chain "
    ++ "complexes are chain-homotopy equivalent and the induced H2 map is "
    ++ "natural in the presentations' certified geometric H2 coordinates. "
    ++ "For framed isotopy, corresponding two-handle coordinates agree. "
    ++ "For an adjacent 1--2 or 2--3 cancellation, the chain map also has "
    ++ "the standard explicit degree-two basis action: retained coordinates "
    ++ "agree and the inserted cancelling two-handle coordinate is zero."

/-- What this domain axiom deliberately does not establish. -/
def sourceScopeCaveat : String :=
  "Lean does not reconstruct attaching maps, boundary matrices, elementary "
    ++ "basis changes, or contractible summand homotopies from the serialized "
    ++ "Kirby diagram in this module. The geometric meaning of each "
    ++ "presentation's H2 model certificate remains external input. This "
    ++ "axiom supplies the standard cancellation basis action, but no ribbon "
    ++ "diagram isotopy, categorical evaluator equality, or final handwritten "
    ++ "identity map on H2."

/--
The imported mathematical handle-homology statement.

Every result is indexed by the exact move and its shared recipe identity.  It
contains an actual `HandleChainEquivalence` and the geometric-coordinate
naturality square.  Provenance metadata is deliberately absent: it is ordinary
repository data below, not part of the mathematical axiom.
-/
structure StandardHandleChainNaturality
    (H2 : Type uH) [AddCommGroup H2] where
  compile :
    {source target : SpecialKirbyPresentation H2} →
    (move : TopologicalTableTwoMove source target) →
      SourceBoundChainMoveCertificate move
  framedIsotopyCoordinates :
    {source target : SpecialKirbyPresentation H2} →
    (metadata :
      TableTwoMoveMetadata .framedIsotopy source target) →
    (countsSound : source.counts = target.counts) →
      ForwardSameDegreeTwoNaturality source target
        (framedIsotopySameChange metadata)
        (compile
          (.framedIsotopy metadata countsSound)).chainEquivalence
  twoOverTwoCoordinates :
    {source target : SpecialKirbyPresentation H2} →
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source target) →
    (countsSound : source.counts = target.counts) →
      ForwardSameDegreeTwoNaturality source target
        (twoOverTwoSameChange metadata)
        (compile
          (.twoOverTwo metadata countsSound)).chainEquivalence
  oneTwoBirthCoordinates :
    {source target : SpecialKirbyPresentation H2} →
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth source target) →
    (countsSound : target.counts = source.counts.addOneTwo) →
      ForwardAddedDegreeTwoNaturality source target 2
        (oneTwoBirthAddedChange metadata)
        (compile
          (.oneTwoBirth metadata countsSound)).chainEquivalence
  oneTwoDeathCoordinates :
    {source target : SpecialKirbyPresentation H2} →
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath source target) →
    (countsSound : source.counts = target.counts.addOneTwo) →
      BackwardRemovedDegreeTwoNaturality source target 2
        (oneTwoDeathRemovedChange metadata)
        (compile
          (.oneTwoDeath metadata countsSound)).chainEquivalence
  twoThreeBirthCoordinates :
    {source target : SpecialKirbyPresentation H2} →
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth source target) →
    (countsSound : target.counts = source.counts.addTwoThree) →
      ForwardAddedDegreeTwoNaturality source target 1
        (twoThreeBirthAddedChange metadata)
        (compile
          (.twoThreeBirth metadata countsSound)).chainEquivalence
  twoThreeDeathCoordinates :
    {source target : SpecialKirbyPresentation H2} →
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath source target) →
    (countsSound : source.counts = target.counts.addTwoThree) →
      BackwardRemovedDegreeTwoNaturality source target 1
        (twoThreeDeathRemovedChange metadata)
        (compile
          (.twoThreeDeath metadata countsSound)).chainEquivalence

/--
The sole handle-homology domain axiom.

It imports standard chain naturality and the explicit cancellation-summand
basis action. It does not import provenance, a ribbon movie, an evaluator
equality, or a final identity map on `H2`.
-/
axiom standardHandleChainNaturality
    (H2 : Type uH) [AddCommGroup H2] :
    StandardHandleChainNaturality H2

/--
Canonical marked-homology compiler relative to the one explicit standard
handle-chain naturality axiom.
-/
noncomputable def sourceBackedGeometricH2Compiler
    (H2 : Type uH) [AddCommGroup H2] :
    SourceBoundGeometricH2Compiler H2 where
  compile := (standardHandleChainNaturality H2).compile

/--
Every local ambient transport produced by the source-backed compiler is the
identity in the common geometric coordinates.

This theorem depends on the visible handle-chain domain axiom, but the
identity itself is derived rather than assumed.
-/
theorem local_transport_is_identity
    (H2 : Type uH) [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (move : TopologicalTableTwoMove source target) :
    ((sourceBackedGeometricH2Compiler H2).localCompiler.transport
      move).homologyAddEquiv =
        AddEquiv.refl H2 :=
  (sourceBackedGeometricH2Compiler H2).local_transport_is_identity
    move

end TwistedYetter.Kirby.SourceBackedHandleChainNaturality
