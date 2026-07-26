import TwistedYetter.Kirby.HandleChainHomology
import TwistedYetter.Kirby.PresentationExecutionTrace
import TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

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
open TwistedYetter.Kirby.PresentationExecutionTrace
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

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
A content-addressed repository artifact.

This is reproducibility metadata, not a mathematical manifold, category, or
presentation.  Keeping it in a separate structure prevents a hash-bearing
record from masquerading as one of those mathematical objects.
-/
structure ContentAddressedArtifact where
  logicalId : String
  snapshotHash : String
  snapshot_hash_shape :
    RawPresentation.sha256Shape snapshotHash = true

/--
External certification that an artifact lies in the exact closed,
connected, smooth, oriented four-dimensional scope used by this calculus.

The certificate is provenance.  The mathematical scope is fixed by
`requiredClosedFourScope`; it is not a caller-selectable field.
-/
structure ClosedFourManifoldScopeCertificate where
  artifact : ContentAddressedArtifact
  certifiedScope : ManifoldScope
  certifies_required_scope :
    certifiedScope = requiredClosedFourScope

/-- Repository provenance for one stored special-Kirby artifact. -/
structure SpecialKirbyArtifactProvenance where
  representedManifoldArtifact : ContentAddressedArtifact
  scopeCertificate : ClosedFourManifoldScopeCertificate

/--
Attach repository provenance to a mathematical payload.

The wrapper is deliberately absent from presentations, moves, movies, and
evaluators.  Forgetting `.provenance` recovers the complete mathematical
payload, so content hashes cannot affect any theorem in the Kirby kernel.
-/
structure StoredArtifact (A : Type uH) where
  payload : A
  provenance : SpecialKirbyArtifactProvenance

namespace StoredArtifact

def logicalId (artifact : StoredArtifact A) : String :=
  artifact.provenance.representedManifoldArtifact.logicalId

def snapshotHash (artifact : StoredArtifact A) : String :=
  artifact.provenance.representedManifoldArtifact.snapshotHash

theorem snapshot_hash_shape (artifact : StoredArtifact A) :
    RawPresentation.sha256Shape artifact.snapshotHash = true :=
  artifact.provenance.representedManifoldArtifact.snapshot_hash_shape

def certifiedScope (artifact : StoredArtifact A) : ManifoldScope :=
  artifact.provenance.scopeCertificate.certifiedScope

theorem certified_scope_sound (artifact : StoredArtifact A) :
    artifact.certifiedScope = requiredClosedFourScope :=
  artifact.provenance.scopeCertificate.certifies_required_scope

def scopeCertificateHash (artifact : StoredArtifact A) : String :=
  artifact.provenance.scopeCertificate.artifact.snapshotHash

theorem scope_certificate_hash_shape
    (artifact : StoredArtifact A) :
    RawPresentation.sha256Shape artifact.scopeCertificateHash = true :=
  artifact.provenance.scopeCertificate.artifact.snapshot_hash_shape

end StoredArtifact

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
structure GeneralHandlePresentation where
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
    (source target : GeneralHandlePresentation) where
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
    : GeneralHandlePresentation →
      GeneralHandlePresentation → Type
  | levelIsotopy
      {source target : GeneralHandlePresentation}
      (index : HandleIndex)
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts) :
      GeneralCerfMove source target
  | oneSlide
      {source target : GeneralHandlePresentation}
      (orientation : BandOrientation)
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts) :
      GeneralCerfMove source target
  | twoSlide
      {source target : GeneralHandlePresentation}
      (orientation : BandOrientation)
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts) :
      GeneralCerfMove source target
  | threeSlide
      {source target : GeneralHandlePresentation}
      (orientation : BandOrientation)
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts) :
      GeneralCerfMove source target
  | zeroOneBirth
      {source target : GeneralHandlePresentation}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : target.counts = addZeroOneCounts source.counts) :
      GeneralCerfMove source target
  | zeroOneDeath
      {source target : GeneralHandlePresentation}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = addZeroOneCounts target.counts) :
      GeneralCerfMove source target
  | oneTwoBirth
      {source target : GeneralHandlePresentation}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : target.counts = source.counts.addOneTwo) :
      GeneralCerfMove source target
  | oneTwoDeath
      {source target : GeneralHandlePresentation}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts.addOneTwo) :
      GeneralCerfMove source target
  | twoThreeBirth
      {source target : GeneralHandlePresentation}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : target.counts = source.counts.addTwoThree) :
      GeneralCerfMove source target
  | twoThreeDeath
      {source target : GeneralHandlePresentation}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = target.counts.addTwoThree) :
      GeneralCerfMove source target
  | threeFourBirth
      {source target : GeneralHandlePresentation}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : target.counts = addThreeFourCounts source.counts) :
      GeneralCerfMove source target
  | threeFourDeath
      {source target : GeneralHandlePresentation}
      (metadata : GeneralCerfStepMetadata source target)
      (counts_sound : source.counts = addThreeFourCounts target.counts) :
      GeneralCerfMove source target

/-- Typed finite composition of general Cerf moves. -/
inductive GeneralCerfMovie
    : GeneralHandlePresentation →
      GeneralHandlePresentation → Type
  | refl (presentation : GeneralHandlePresentation) :
      GeneralCerfMovie presentation presentation
  | step
      {source target : GeneralHandlePresentation}
      (move : GeneralCerfMove source target) :
      GeneralCerfMovie source target
  | trans
      {source middle target : GeneralHandlePresentation}
      (first : GeneralCerfMovie source middle)
      (second : GeneralCerfMovie middle target) :
      GeneralCerfMovie source target

/--
Visible external form of Gompf--Stipsicz Theorem 4.2.12.

The source theorem concerns compact relative handle decompositions and does
not itself say that the five Bärenz--Barrett Table 2 link families suffice.
-/
structure GeneralCerfCompleteness where
  connected :
    (source target : GeneralHandlePresentation) →
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
    (H2 : Type uH) [AddCommGroup H2] where
  formal : FormalPresentation
  execution : ClosedExecutionCertificate formal
  counts : HandleCounts
  /--
  The exact framed-link component representing each degree-two handle basis
  vector.  Ordinary and specially-dotted components are both two-handle
  bearing; dotted components represent one-handles and are excluded.
  -/
  twoHandleComponent : Fin counts.h2 → ComponentSpec
  two_handle_component_mem :
    (index : Fin counts.h2) →
      twoHandleComponent index ∈ formal.raw.components
  two_handle_component_role :
    (index : Fin counts.h2) →
      (twoHandleComponent index).role ≠ .dotted
  twoHandleIndex? : String → Option (Fin counts.h2)
  two_handle_index_roundtrip :
    (index : Fin counts.h2) →
      twoHandleIndex? (twoHandleComponent index).componentId = some index
  two_handle_index_sound :
    (componentId : String) →
    (index : Fin counts.h2) →
      twoHandleIndex? componentId = some index →
        componentId = (twoHandleComponent index).componentId
  every_two_handle_component_indexed :
    (component : ComponentSpec) →
      component ∈ formal.raw.components →
      component.role ≠ .dotted →
        ∃ index, twoHandleIndex? component.componentId = some index
  dotted_component_unindexed :
    (component : ComponentSpec) →
      component.role = .dotted →
        twoHandleIndex? component.componentId = none
  componentIndexCertificateHash : String
  component_index_certificate_hash_shape :
    RawPresentation.sha256Shape componentIndexCertificateHash = true
  uniqueZeroHandle : counts.h0 = 1
  uniqueFourHandle : counts.h4 = 1
  orderedByIncreasingIndex : Prop
  ordering_witness : orderedByIncreasingIndex
  h2ModelCertificateHash : String
  h2_model_certificate_hash_shape :
    RawPresentation.sha256Shape h2ModelCertificateHash = true
  /--
  The homology marking uses the upside-down handle decomposition.  The
  primal `counts` remain unchanged because they also control the Kirby-link
  normalization and the names of primal moves.
  -/
  handleChain : HandleChainModel counts.turnedOver
  h2ModelEquiv : handleChain.SecondHomology ≃+ H2

namespace SpecialKirbyPresentation

/-- Degree-two cycles in the presentation's certified handle chain. -/
noncomputable abbrev DegreeTwoCycle
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : SpecialKirbyPresentation H2) :=
  presentation.handleChain.complex.cycles 2

/-- Coordinates of an explicit cycle in the certified two-handle basis. -/
noncomputable def cycleHandleCoefficients
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : SpecialKirbyPresentation H2)
    (cycle : presentation.DegreeTwoCycle) :
    Fin presentation.counts.h2 → ℤ :=
  presentation.handleChain.degreeTwoBasis.hom
    (presentation.handleChain.complex.iCycles 2 cycle)

/--
Coefficient of an explicit cycle on the two-handle represented by one link
component. Dotted one-handle components have coefficient zero.
-/
noncomputable def cycleComponentExponent
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : SpecialKirbyPresentation H2)
    (cycle : presentation.DegreeTwoCycle)
    (component : ComponentSpec) : ℤ :=
  match presentation.twoHandleIndex? component.componentId with
  | none => 0
  | some index => presentation.cycleHandleCoefficients cycle index

end SpecialKirbyPresentation

/--
Typed metadata for one special Table 2 link move.

The old arbitrary proposition `locallyRealizesTableTwoMove` has been removed.
The sole field is now a source-bound, kind-indexed local recipe containing a
literal component/event window replacement and a closed handle-edit program.
-/
structure TableTwoMoveMetadata
    {H2 : Type uH} [AddCommGroup H2]
    (kind : RecipeKind)
    (source target : SpecialKirbyPresentation H2) where
  recipe : SourceBoundRecipe kind source.formal target.formal

namespace TableTwoMoveMetadata

def moveId
    {H2 : Type uH} [AddCommGroup H2]
    {kind : RecipeKind}
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata kind source target) : String :=
  metadata.recipe.recipeId

def sourcePresentationHash
    {H2 : Type uH} [AddCommGroup H2]
    {kind : RecipeKind}
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata kind source target) : String :=
  metadata.recipe.sourcePresentationHash

def targetPresentationHash
    {H2 : Type uH} [AddCommGroup H2]
    {kind : RecipeKind}
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata kind source target) : String :=
  metadata.recipe.targetPresentationHash

def localTopologyCertificateHash
    {H2 : Type uH} [AddCommGroup H2]
    {kind : RecipeKind}
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata kind source target) : String :=
  metadata.recipe.recipeSnapshotHash

theorem source_hash_sound
    {H2 : Type uH} [AddCommGroup H2]
    {kind : RecipeKind}
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata kind source target) :
    metadata.sourcePresentationHash =
      source.formal.pinnedSourceHash :=
  metadata.recipe.source_hash_sound

theorem target_hash_sound
    {H2 : Type uH} [AddCommGroup H2]
    {kind : RecipeKind}
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata kind source target) :
    metadata.targetPresentationHash =
      target.formal.pinnedSourceHash :=
  metadata.recipe.target_hash_sound

theorem local_certificate_hash_shape
    {H2 : Type uH} [AddCommGroup H2]
    {kind : RecipeKind}
    {source target : SpecialKirbyPresentation H2}
    (metadata : TableTwoMoveMetadata kind source target) :
    RawPresentation.sha256Shape
        metadata.localTopologyCertificateHash = true :=
  metadata.recipe.recipe_snapshot_hash_shape

end TableTwoMoveMetadata

/--
Presentation-to-presentation chain data.

The map on `H2` is not a field.  It is forced by the chain homotopy
equivalence and the two presentations' pinned coordinate identifications.
-/
structure MarkedH2Transport
    {H2 : Type uH} [AddCommGroup H2]
    (source target : SpecialKirbyPresentation H2) where
  chainEquivalence :
    HandleChainEquivalence source.handleChain target.handleChain

namespace MarkedH2Transport

/-- The ambient additive `H2` equivalence derived from concrete chain data. -/
noncomputable def homologyAddEquiv
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (transport : MarkedH2Transport source target) :
    H2 ≃+ H2 :=
  source.h2ModelEquiv.symm.trans
    (transport.chainEquivalence.secondHomologyAddEquiv.trans
      target.h2ModelEquiv)

/-- The underlying type equivalence; it cannot be supplied independently. -/
noncomputable def homologyEquiv
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (transport : MarkedH2Transport source target) :
    H2 ≃ H2 :=
  transport.homologyAddEquiv.toEquiv

/-- Transport a marked homology class covariantly. -/
noncomputable def targetClass
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (transport : MarkedH2Transport source target)
    (alpha : H2) : H2 :=
  transport.homologyEquiv alpha

/-- Derive the target character contravariantly. -/
noncomputable def targetCharacter
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (transport : MarkedH2Transport source target)
    (character : H2 → A) : H2 → A :=
  character ∘ transport.homologyEquiv.symm

/-- Simultaneous transport of class and character preserves evaluation. -/
theorem pairing_preserved
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (transport : MarkedH2Transport source target)
    (character : H2 → A)
    (alpha : H2) :
    transport.targetCharacter character (transport.targetClass alpha) =
      character alpha := by
  simp [targetCharacter, targetClass]

/-- The chain-derived ambient transport preserves addition. -/
theorem targetClass_add
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
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
    {H2 : Type uH} [AddCommGroup H2] :
    SpecialKirbyPresentation H2 →
      SpecialKirbyPresentation H2 → Type (uH + 1)
  | framedIsotopy
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .framedIsotopy source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | oneOverOne
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .oneOverOne source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | twoOverOne
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .twoOverOne source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | twoOverTwo
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .twoOverTwo source target)
      (counts_sound : source.counts = target.counts)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | oneTwoBirth
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .oneTwoBirth source target)
      (counts_sound : target.counts = source.counts.addOneTwo)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | oneTwoDeath
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .oneTwoDeath source target)
      (counts_sound : source.counts = target.counts.addOneTwo)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | twoThreeBirth
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .twoThreeBirth source target)
      (counts_sound : target.counts = source.counts.addTwoThree)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target
  | twoThreeDeath
      {source target : SpecialKirbyPresentation H2}
      (metadata : TableTwoMoveMetadata .twoThreeDeath source target)
      (counts_sound : source.counts = target.counts.addTwoThree)
      (transport : MarkedH2Transport source target) :
      TableTwoMove source target

namespace TableTwoMove

/-- Extract the mandatory `H2` transport from any admitted move. -/
def homologyTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (move : TableTwoMove source target) :
    MarkedH2Transport source target := by
  cases move with
  | framedIsotopy _ _ transport => exact transport
  | oneOverOne _ _ transport => exact transport
  | twoOverOne _ _ transport => exact transport
  | twoOverTwo _ _ transport => exact transport
  | oneTwoBirth _ _ transport => exact transport
  | oneTwoDeath _ _ transport => exact transport
  | twoThreeBirth _ _ transport => exact transport
  | twoThreeDeath _ _ transport => exact transport

end TableTwoMove

/-- Typed finite Table 2 movie. -/
inductive TableTwoMovie
    {H2 : Type uH} [AddCommGroup H2] :
    SpecialKirbyPresentation H2 →
      SpecialKirbyPresentation H2 → Type (uH + 1)
  | refl (presentation : SpecialKirbyPresentation H2) :
      TableTwoMovie presentation presentation
  | step
      {source target : SpecialKirbyPresentation H2}
      (move : TableTwoMove source target) :
      TableTwoMovie source target
  | trans
      {source middle target :
        SpecialKirbyPresentation H2}
      (first : TableTwoMovie source middle)
      (second : TableTwoMovie middle target) :
      TableTwoMovie source target

namespace TableTwoMovie

/-- Compose all local `H2` equivalences along a movie. -/
noncomputable def homologyEquiv
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (movie : TableTwoMovie source target) :
    H2 ≃+ H2 := by
  induction movie with
  | refl _ => exact AddEquiv.refl H2
  | step move => exact move.homologyTransport.homologyAddEquiv
  | trans _ _ firstEquiv secondEquiv =>
      exact firstEquiv.trans secondEquiv

/-- Transport a marked `H2` class through the complete movie. -/
noncomputable def targetClass
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (movie : TableTwoMovie source target)
    (alpha : H2) : H2 :=
  movie.homologyEquiv alpha

/-- Derive the target character through the inverse movie transport. -/
noncomputable def targetCharacter
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (movie : TableTwoMovie source target)
    (character : H2 → A) : H2 → A :=
  character ∘ movie.homologyEquiv.symm

/-- The marked pairing is unchanged across an arbitrary composed movie. -/
theorem pairing_preserved
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (movie : TableTwoMovie source target)
    (character : H2 → A)
    (alpha : H2) :
    movie.targetCharacter character (movie.targetClass alpha) =
      character alpha := by
  simp [targetCharacter, targetClass]

/-- A whole Table 2 movie transports `H2` additively. -/
theorem targetClass_add
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (movie : TableTwoMovie source target)
    (alpha beta : H2) :
    movie.targetClass (alpha + beta) =
      movie.targetClass alpha + movie.targetClass beta :=
  movie.homologyEquiv.map_add alpha beta
/-- Composition computes the same `H2` map as composing the two movies. -/
theorem homologyEquiv_trans
    {H2 : Type uH} [AddCommGroup H2]
    {source middle target :
      SpecialKirbyPresentation H2}
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
    (H2 : Type uH) [AddCommGroup H2] where
  generalCerf : GeneralCerfCompleteness
  tableTwoConnected :
    (source target : SpecialKirbyPresentation H2) →
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
    {H2 : Type uH} [AddCommGroup H2]
    (completeness :
      TableTwoLinkCompleteness H2)
    (source target : SpecialKirbyPresentation H2) :
    H2 ≃+ H2 :=
  (completeness.tableTwoConnected source target).homologyEquiv

end TableTwoLinkCompleteness

end TwistedYetter.Kirby.KirbyCompleteness
