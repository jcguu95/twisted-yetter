import TwistedYetter.Kirby.HandleChainHomology

/-!
# Kirby completeness as an explicit topology boundary

This module does not re-prove Cerf theory.  It exposes two different
source-backed topology inputs and keeps both independent of every evaluator.

* `GeneralCerfCompleteness` is the scope of Gompf--Stipsicz Theorem 4.2.12:
  compact relative handle decompositions, all same-index slides, all adjacent
  handle-pair births/deaths, and level isotopies.
* `TableTwoLinkCompleteness` is the stronger four-dimensional link-calculus
  refinement used by Bärenz--Barrett Theorem 3.9: for closed, connected,
  smooth, oriented four-manifolds in the special one-zero/one-four-handle
  presentation class, the exact Table 2 link moves suffice.

The second input is not derived from the first in Lean.  In particular,
zero--one and three--four births/deaths and three-handle slides exist in the
general Cerf whitelist but have no constructor in `TableTwoMove`.

Every Table 2 move carries an explicit equivalence on the presentation's
chosen `H2` model.  Movies compose these equivalences, and marked classes and
characters are transported rather than rewritten by hand.  No topology
completeness structure contains an evaluator value or evaluator equality.
-/

namespace TwistedYetter.Kirby.KirbyCompleteness

open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.HandleChainHomology

universe uH uA

/-- Boundary modes retained in the general Cerf interface. -/
inductive BoundaryMode
  | closed
  | relative
  deriving Repr, BEq, DecidableEq

/-- Orientation policy of the admitted manifold class. -/
inductive OrientationMode
  | oriented
  deriving Repr, BEq, DecidableEq

/--
Machine-visible scope of the R10 invariant route.

Gompf--Stipsicz Theorem 4.2.12 is more general, but the downstream twisted
invariant is deliberately restricted to this exact class.
-/
structure ManifoldScope where
  dimension : Nat
  smooth : Bool
  compact : Bool
  connected : Bool
  boundaryMode : BoundaryMode
  orientationMode : OrientationMode
  deriving Repr, BEq, DecidableEq

/-- Exact scope admitted by the special Kirby-diagram route. -/
def requiredClosedFourScope : ManifoldScope where
  dimension := 4
  smooth := true
  compact := true
  connected := true
  boundaryMode := .closed
  orientationMode := .oriented

/--
An external input asserting that one content-addressed manifold belongs to
the exact R10 scope.  This is an interface to manifold topology, not a
replacement definition of a smooth manifold.
-/
structure ClosedConnectedSmoothOrientedFourManifoldInput where
  manifoldId : String
  manifoldSnapshotHash : String
  manifold_snapshot_hash_shape :
    RawPresentation.sha256Shape manifoldSnapshotHash = true
  scope : ManifoldScope
  scope_sound : scope = requiredClosedFourScope
  scopeCertificateHash : String
  scope_certificate_hash_shape :
    RawPresentation.sha256Shape scopeCertificateHash = true

/-- Handle indices appearing in a four-dimensional Cerf movie. -/
inductive HandleIndex
  | zero
  | one
  | two
  | three
  | four
  deriving Repr, BEq, DecidableEq

/-- Direction of a cancelling-pair move. -/
inductive PairDirection
  | birth
  | death
  deriving Repr, BEq, DecidableEq

/-- Add a cancelling zero--one pair. -/
def addZeroOneCounts (counts : HandleCounts) : HandleCounts :=
  { counts with h0 := counts.h0 + 1, h1 := counts.h1 + 1 }

/-- Add a cancelling three--four pair. -/
def addThreeFourCounts (counts : HandleCounts) : HandleCounts :=
  { counts with h3 := counts.h3 + 1, h4 := counts.h4 + 1 }

/--
A general ordered relative handle presentation of one fixed compact
four-manifold.  No unique-zero/unique-four normal form is assumed here.
-/
structure GeneralHandlePresentation
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput) where
  presentationId : String
  presentationSnapshotHash : String
  presentation_snapshot_hash_shape :
    RawPresentation.sha256Shape presentationSnapshotHash = true
  counts : HandleCounts
  orderedByIncreasingIndex : Prop
  ordering_witness : orderedByIncreasingIndex
  representsFixedManifold : Prop
  representation_witness : representsFixedManifold
  representationCertificateHash : String
  representation_certificate_hash_shape :
    RawPresentation.sha256Shape representationCertificateHash = true

/-- Hash-bound metadata for one general Cerf step. -/
structure GeneralCerfStepMetadata
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    (source target : GeneralHandlePresentation manifold) where
  stepId : String
  sourcePresentationHash : String
  targetPresentationHash : String
  source_hash_sound :
    sourcePresentationHash = source.presentationSnapshotHash
  target_hash_sound :
    targetPresentationHash = target.presentationSnapshotHash
  localTopologyCertificateHash : String
  local_certificate_hash_shape :
    RawPresentation.sha256Shape localTopologyCertificateHash = true
  locallyRealizesCerfMove : Prop
  local_topology_witness : locallyRealizesCerfMove

/--
The complete four-dimensional move whitelist in the general Cerf theorem.

Slides of index zero or four are absent, as in the standard definition of
handle slide.  Every adjacent cancelling pair is present in both directions.
-/
inductive GeneralCerfMove
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput} :
    GeneralHandlePresentation manifold →
      GeneralHandlePresentation manifold → Type
  | levelIsotopy
      {source target : GeneralHandlePresentation manifold}
      (index : HandleIndex)
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts) :
      GeneralCerfMove source target
  | oneSlide
      {source target : GeneralHandlePresentation manifold}
      (orientation : BandOrientation)
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts) :
      GeneralCerfMove source target
  | twoSlide
      {source target : GeneralHandlePresentation manifold}
      (orientation : BandOrientation)
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts) :
      GeneralCerfMove source target
  | threeSlide
      {source target : GeneralHandlePresentation manifold}
      (orientation : BandOrientation)
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts) :
      GeneralCerfMove source target
  | zeroOneBirth
      {source target : GeneralHandlePresentation manifold}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : target.counts = addZeroOneCounts source.counts) :
      GeneralCerfMove source target
  | zeroOneDeath
      {source target : GeneralHandlePresentation manifold}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = addZeroOneCounts target.counts) :
      GeneralCerfMove source target
  | oneTwoBirth
      {source target : GeneralHandlePresentation manifold}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : target.counts = source.counts.addOneTwo) :
      GeneralCerfMove source target
  | oneTwoDeath
      {source target : GeneralHandlePresentation manifold}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts.addOneTwo) :
      GeneralCerfMove source target
  | twoThreeBirth
      {source target : GeneralHandlePresentation manifold}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : target.counts = source.counts.addTwoThree) :
      GeneralCerfMove source target
  | twoThreeDeath
      {source target : GeneralHandlePresentation manifold}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts.addTwoThree) :
      GeneralCerfMove source target
  | threeFourBirth
      {source target : GeneralHandlePresentation manifold}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : target.counts = addThreeFourCounts source.counts) :
      GeneralCerfMove source target
  | threeFourDeath
      {source target : GeneralHandlePresentation manifold}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = addThreeFourCounts target.counts) :
      GeneralCerfMove source target

/-- Typed finite composition of general Cerf moves. -/
inductive GeneralCerfMovie
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput} :
    GeneralHandlePresentation manifold →
      GeneralHandlePresentation manifold → Type
  | refl (presentation : GeneralHandlePresentation manifold) :
      GeneralCerfMovie presentation presentation
  | step
      {source target : GeneralHandlePresentation manifold}
      (move : GeneralCerfMove source target) :
      GeneralCerfMovie source target
  | trans
      {source middle target : GeneralHandlePresentation manifold}
      (first : GeneralCerfMovie source middle)
      (second : GeneralCerfMovie middle target) :
      GeneralCerfMovie source target

/--
Visible external form of Gompf--Stipsicz Theorem 4.2.12.

The source theorem concerns compact relative handle decompositions and does
not itself say that the five Bärenz--Barrett Table 2 link families suffice.
-/
structure GeneralCerfCompleteness
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput) where
  connected :
    (source target : GeneralHandlePresentation manifold) →
      GeneralCerfMovie source target
  source_ref : String
  source_locator : String
  exact_scope : String
  source_scope_caveat : String

/--
Special closed Kirby presentation used by the link evaluator.

The unique zero- and four-handle conditions are mandatory.  All presentations
of one movie use a fixed ambient `H2` model; each presentation separately pins
the certificate identifying its handle-chain coordinates with that model.
-/
structure SpecialKirbyPresentation
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  formal : FormalPresentation
  counts : HandleCounts
  uniqueZeroHandle : counts.h0 = 1
  uniqueFourHandle : counts.h4 = 1
  orderedByIncreasingIndex : Prop
  ordering_witness : orderedByIncreasingIndex
  representedManifoldHash : String
  represented_manifold_hash_sound :
    representedManifoldHash = manifold.manifoldSnapshotHash
  representsFixedManifold : Prop
  representation_witness : representsFixedManifold
  representationCertificateHash : String
  representation_certificate_hash_shape :
    RawPresentation.sha256Shape representationCertificateHash = true
  h2ModelCertificateHash : String
  h2_model_certificate_hash_shape :
    RawPresentation.sha256Shape h2ModelCertificateHash = true
  handleChain : HandleChainModel counts
  h2ModelEquiv : handleChain.SecondHomology ≃+ H2

/-- Hash-bound metadata for one special Table 2 link move. -/
structure TableTwoMoveMetadata
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : SpecialKirbyPresentation manifold H2) where
  moveId : String
  sourcePresentationHash : String
  targetPresentationHash : String
  source_hash_sound :
    sourcePresentationHash = source.formal.pinnedSourceHash
  target_hash_sound :
    targetPresentationHash = target.formal.pinnedSourceHash
  localTopologyCertificateHash : String
  local_certificate_hash_shape :
    RawPresentation.sha256Shape localTopologyCertificateHash = true
  locallyRealizesTableTwoMove : Prop
  local_topology_witness : locallyRealizesTableTwoMove

/--
Presentation-to-presentation chain data.

The map on `H2` is not a field.  It is forced by the chain homotopy
equivalence and the two presentations' pinned coordinate identifications.
-/
structure MarkedH2Transport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : SpecialKirbyPresentation manifold H2) where
  chainEquivalence :
    HandleChainEquivalence source.handleChain target.handleChain

namespace MarkedH2Transport

/-- The ambient additive `H2` equivalence derived from concrete chain data. -/
noncomputable def homologyAddEquiv
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (transport : MarkedH2Transport source target) :
    H2 ≃+ H2 :=
  source.h2ModelEquiv.symm.trans
    (transport.chainEquivalence.secondHomologyAddEquiv.trans
      target.h2ModelEquiv)

/-- The underlying type equivalence; it cannot be supplied independently. -/
noncomputable def homologyEquiv
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (transport : MarkedH2Transport source target) :
    H2 ≃ H2 :=
  transport.homologyAddEquiv.toEquiv

/-- Transport a marked homology class covariantly. -/
noncomputable def targetClass
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (transport : MarkedH2Transport source target)
    (alpha : H2) : H2 :=
  transport.homologyEquiv alpha

/-- Derive the target character contravariantly. -/
noncomputable def targetCharacter
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (transport : MarkedH2Transport source target)
    (character : H2 → A) : H2 → A :=
  character ∘ transport.homologyEquiv.symm

/-- Simultaneous transport of class and character preserves evaluation. -/
theorem pairing_preserved
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (transport : MarkedH2Transport source target)
    (character : H2 → A)
    (alpha : H2) :
    transport.targetCharacter character (transport.targetClass alpha) =
      character alpha := by
  simp [targetCharacter, targetClass]

/-- The chain-derived ambient transport preserves addition. -/
theorem targetClass_add
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (transport : MarkedH2Transport source target)
    (alpha beta : H2) :
    transport.targetClass (alpha + beta) =
      transport.targetClass alpha + transport.targetClass beta :=
  transport.homologyAddEquiv.map_add alpha beta

end MarkedH2Transport

/--
Exact special-link whitelist corresponding to Bärenz--Barrett Table 2 plus
framed-link presentation isotopy.

There is deliberately no constructor for zero--one, three--four, or
three-over-three moves, and no constructor from a bare evaluator equality.
-/
inductive TableTwoMove
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2] :
    SpecialKirbyPresentation manifold H2 →
      SpecialKirbyPresentation manifold H2 → Type (uH + 1)
  | framedIsotopy
      {source target : SpecialKirbyPresentation manifold H2}
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | oneOverOne
      {source target : SpecialKirbyPresentation manifold H2}
      (orientation : BandOrientation)
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | twoOverOne
      {source target : SpecialKirbyPresentation manifold H2}
      (orientation : BandOrientation)
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | twoOverTwo
      {source target : SpecialKirbyPresentation manifold H2}
      (orientation : BandOrientation)
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | oneTwoBirth
      {source target : SpecialKirbyPresentation manifold H2}
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : target.counts = source.counts.addOneTwo)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | oneTwoDeath
      {source target : SpecialKirbyPresentation manifold H2}
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts.addOneTwo)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | twoThreeBirth
      {source target : SpecialKirbyPresentation manifold H2}
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : target.counts = source.counts.addTwoThree)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | twoThreeDeath
      {source target : SpecialKirbyPresentation manifold H2}
      (metadata : TableTwoMoveMetadata source target)
      (counts_sound : source.counts = target.counts.addTwoThree)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target

namespace TableTwoMove

/-- Extract the mandatory `H2` transport from any admitted move. -/
def homologyTransport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TableTwoMove source target) :
    MarkedH2Transport source target := by
  cases move with
  | framedIsotopy _ _ transport => exact transport
  | oneOverOne _ _ _ transport => exact transport
  | twoOverOne _ _ _ transport => exact transport
  | twoOverTwo _ _ _ transport => exact transport
  | oneTwoBirth _ _ transport => exact transport
  | oneTwoDeath _ _ transport => exact transport
  | twoThreeBirth _ _ transport => exact transport
  | twoThreeDeath _ _ transport => exact transport

end TableTwoMove

/-- Typed finite Table 2 movie. -/
inductive TableTwoMovie
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2] :
    SpecialKirbyPresentation manifold H2 →
      SpecialKirbyPresentation manifold H2 → Type (uH + 1)
  | refl (presentation : SpecialKirbyPresentation manifold H2) :
      TableTwoMovie presentation presentation
  | step
      {source target : SpecialKirbyPresentation manifold H2}
      (move : TableTwoMove source target) :
      TableTwoMovie source target
  | trans
      {source middle target :
        SpecialKirbyPresentation manifold H2}
      (first : TableTwoMovie source middle)
      (second : TableTwoMovie middle target) :
      TableTwoMovie source target

namespace TableTwoMovie

/-- Compose all local `H2` equivalences along a movie. -/
noncomputable def homologyEquiv
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (movie : TableTwoMovie source target) :
    H2 ≃+ H2 := by
  induction movie with
  | refl _ => exact AddEquiv.refl H2
  | step move => exact move.homologyTransport.homologyAddEquiv
  | trans _ _ firstEquiv secondEquiv =>
      exact firstEquiv.trans secondEquiv

/-- Transport a marked `H2` class through the complete movie. -/
noncomputable def targetClass
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (movie : TableTwoMovie source target)
    (alpha : H2) : H2 :=
  movie.homologyEquiv alpha

/-- Derive the target character through the inverse movie transport. -/
noncomputable def targetCharacter
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (movie : TableTwoMovie source target)
    (character : H2 → A) : H2 → A :=
  character ∘ movie.homologyEquiv.symm

/-- The marked pairing is unchanged across an arbitrary composed movie. -/
theorem pairing_preserved
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (movie : TableTwoMovie source target)
    (character : H2 → A)
    (alpha : H2) :
    movie.targetCharacter character (movie.targetClass alpha) =
      character alpha := by
  simp [targetCharacter, targetClass]

/-- A whole Table 2 movie transports `H2` additively. -/
theorem targetClass_add
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (movie : TableTwoMovie source target)
    (alpha beta : H2) :
    movie.targetClass (alpha + beta) =
      movie.targetClass alpha + movie.targetClass beta :=
  movie.homologyEquiv.map_add alpha beta
/-- Composition computes the same `H2` map as composing the two movies. -/
theorem homologyEquiv_trans
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source middle target :
      SpecialKirbyPresentation manifold H2}
    (first : TableTwoMovie source middle)
    (second : TableTwoMovie middle target) :
    homologyEquiv (.trans first second) =
      (homologyEquiv first).trans (homologyEquiv second) :=
  rfl

end TableTwoMovie

/--
The exact topology assumption needed after R7--R9.

`generalCerf` records the broad theorem.  `tableTwoConnected` separately
imports the link-calculus refinement.  The latter must carry its own sources
and caveat because it is not proved from `generalCerf` in this module.
-/
structure TableTwoLinkCompleteness
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  generalCerf : GeneralCerfCompleteness manifold
  tableTwoConnected :
    (source target : SpecialKirbyPresentation manifold H2) →
      TableTwoMovie source target
  link_calculus_source_refs : List String
  link_calculus_source_locator : String
  normal_form_statement : String
  exact_move_scope : String
  source_scope_caveat : String

namespace TableTwoLinkCompleteness

/--
Completeness supplies only a topology movie and its induced `H2` map.
Evaluator invariance is intentionally deferred to R11.
-/
noncomputable def markedTransport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (completeness :
      TableTwoLinkCompleteness manifold H2)
    (source target : SpecialKirbyPresentation manifold H2) :
    H2 ≃+ H2 :=
  (completeness.tableTwoConnected source target).homologyEquiv

end TableTwoLinkCompleteness

end TwistedYetter.Kirby.KirbyCompleteness
