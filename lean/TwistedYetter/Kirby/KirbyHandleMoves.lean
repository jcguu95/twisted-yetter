import TwistedYetter.Kirby.FramedSliding
import TwistedYetter.Kirby.Presentation

/-!
# Typed Kirby handle slides

This module separates two logically different certificates.

* The graphical certificate is a closed whitelist.  Slides over a one-handle
  use the original sliding property (Bärenz--Barrett Lemma 3.1); a two-handle
  over a two-handle uses the `SlidingFamily` calculation behind Lemmas 3.3 and
  3.4.  No constructor accepts an arbitrary `CertifiedMove`.
* Framing, component lineage, and homological marking transport are explicit
  bookkeeping data.  Matrix congruence is not used as a substitute for the
  graphical evaluator proof.

The original sliding property remains a visible, source-backed standard input.
The generalized two-over-two slide is derived from the finite calculation in
`GeneralizedSliding`.
-/

namespace TwistedYetter.Kirby.KirbyHandleMoves

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.CategoricalMovie
open TwistedYetter.Kirby.FramedSliding
open TwistedYetter.Kirby.GeneralizedSliding
open TwistedYetter.Kirby.HandleSlide
open TwistedYetter.Kirby.Presentation

universe u v uR uS uI uH uA

/-- The three handle-slide types in Bärenz--Barrett Table 2. -/
inductive SlideKind
  | oneOverOne
  | twoOverOne
  | twoOverTwo
  deriving Repr, BEq, DecidableEq

/-- Orientation of the band sum; both signs must be represented explicitly. -/
inductive BandOrientation
  | positive
  | negative
  deriving Repr, BEq, DecidableEq

namespace BandOrientation

/-- Integral coefficient in the elementary basis change. -/
def coefficient : BandOrientation → Int
  | .positive => 1
  | .negative => -1

end BandOrientation

namespace SlideKind

/-- Role of the component being moved. -/
def slidingRole : SlideKind → ComponentRole
  | .oneOverOne => .dotted
  | .twoOverOne => .ordinary
  | .twoOverTwo => .ordinary

/-- Role of the stationary component over which the move is made. -/
def stationaryRole : SlideKind → ComponentRole
  | .oneOverOne => .dotted
  | .twoOverOne => .dotted
  | .twoOverTwo => .ordinary

end SlideKind

/--
Framing bookkeeping is indexed by the move kind.

There is no integer framing on a dotted 1-handle.  A 2-over-1 move records the
two integer framings and pins the diagram-level tracking witness, without
pretending it is a congruence of a 2-handle linking matrix.  Only the
2-over-2 constructor carries the familiar diagonal congruence formula.
-/
inductive FramingBookkeeping : SlideKind → Type
  | oneOverOne :
      FramingBookkeeping .oneOverOne
  | twoOverOne
      (sourceFraming targetFraming : Int)
      (diagramTrackingWitnessHash : String) :
      FramingBookkeeping .twoOverOne
  | twoOverTwo
      (orientation : BandOrientation)
      (sourceSlidingFraming stationaryFraming mutualLinking
        targetSlidingFraming : Int)
      (sound :
        targetSlidingFraming =
          sourceSlidingFraming +
            2 * orientation.coefficient * mutualLinking +
            stationaryFraming) :
      FramingBookkeeping .twoOverTwo

/--
Fail-closed combinatorial metadata for one oriented handle slide.

For a two-over-two move, the framing equation inside `framing` is the diagonal
part of `Q' = Pᵀ Q P` for
`e_sliding' = e_sliding + sign * e_stationary`.  The other two move kinds are
not misrepresented as linking-form congruences.
-/
structure SlideMetadata where
  moveId : String
  kind : SlideKind
  orientation : BandOrientation
  sourcePresentationHash : String
  targetPresentationHash : String
  slidingComponentId : String
  stationaryComponentId : String
  slidingRole : ComponentRole
  stationaryRole : ComponentRole
  framing : FramingBookkeeping kind
  component_ids_distinct :
    slidingComponentId ≠ stationaryComponentId
  roles_sound :
    slidingRole = kind.slidingRole ∧
      stationaryRole = kind.stationaryRole
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Theorem 3.9, Table 2, equations (3.3.1)-(3.3.2), journal pages 685-687"

/--
Component IDs move through a handle slide by an explicit equivalence.  The two
participating IDs cannot silently disappear or swap.
-/
structure ComponentLineage (metadata : SlideMetadata) where
  componentChange : String ≃ String
  sliding_preserved :
    componentChange metadata.slidingComponentId =
      metadata.slidingComponentId
  stationary_preserved :
    componentChange metadata.stationaryComponentId =
      metadata.stationaryComponentId

/--
Transport a homological character contravariantly along an admitted change of
coordinates.  This is the abstract form of the matrix rule dual to class
coordinates transforming by `P⁻¹`.
-/
def transportCharacter
    {H : Type uH} {A : Type uA}
    (basisChange : H ≃ H) (character : H → A) : H → A :=
  character ∘ basisChange.symm

/-- Character evaluation is unchanged when both class and character move. -/
theorem transportCharacter_apply
    {H : Type uH} {A : Type uA}
    (basisChange : H ≃ H) (character : H → A) (alpha : H) :
    transportCharacter basisChange character (basisChange alpha) =
      character alpha := by
  simp [transportCharacter]

/--
The complete homological transport certificate.  Its soundness is a theorem,
not a user-provided equality for one selected class.
-/
structure HomologicalTransport (H : Type uH) (A : Type uA) where
  basisChange : H ≃ H
  sourceCharacter : H → A

namespace HomologicalTransport

def targetCharacter
    {H : Type uH} {A : Type uA}
    (transport : HomologicalTransport H A) : H → A :=
  transportCharacter transport.basisChange transport.sourceCharacter

theorem pairing_preserved
    {H : Type uH} {A : Type uA}
    (transport : HomologicalTransport H A) (alpha : H) :
    transport.targetCharacter (transport.basisChange alpha) =
      transport.sourceCharacter alpha :=
  transportCharacter_apply transport.basisChange
    transport.sourceCharacter alpha

end HomologicalTransport

section OrdinarySliding

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/-- Expose an atomic object as its explicit parenthesized boundary. -/
def exposeBoundary (boundary : Boundary C) :
    Diagram C (.atom boundary.denote) boundary :=
  Diagram.coupon "expose-ordinary-slide-boundary" (𝟙 _)

/-- Pack an explicit boundary back into its denoting atomic object. -/
def packBoundary (boundary : Boundary C) :
    Diagram C boundary (.atom boundary.denote) :=
  Diagram.coupon "pack-ordinary-slide-boundary" (𝟙 _)

/-- Retain the complete external tangle between two ordinary slide windows. -/
def liftOrdinaryExterior
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Diagram C (.atom source.denote) (.atom target.denote) :=
  exposeBoundary source ≫ᵈ exterior ≫ᵈ packBoundary target

theorem liftOrdinaryExterior_eval
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Diagram.eval C (liftOrdinaryExterior exterior) =
      Diagram.eval C exterior := by
  simp [liftOrdinaryExterior, exposeBoundary, packBoundary, Diagram.eval,
    Boundary.denote]

def ordinaryBefore
    (law : SourcedSlidingLaw C)
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Diagram C (.atom source.denote) (.atom target.denote) :=
  law.before_diagram source.denote ≫ᵈ liftOrdinaryExterior exterior

def ordinaryAfter
    (law : SourcedSlidingLaw C)
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Diagram C (.atom source.denote) (.atom target.denote) :=
  liftOrdinaryExterior exterior ≫ᵈ law.after_diagram target.denote

/--
The original sliding property transports an arbitrary typed exterior.  The
proof uses only the supplied Lemma 3.1 endpoint equality and naturality.
-/
theorem ordinary_exterior_transport_sound
    (law : SourcedSlidingLaw C)
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Diagram.eval C (ordinaryBefore law exterior) =
      Diagram.eval C (ordinaryAfter law exterior) := by
  change Diagram.eval C (law.before_diagram source.denote) ≫
      Diagram.eval C (liftOrdinaryExterior exterior) =
    Diagram.eval C (liftOrdinaryExterior exterior) ≫
      Diagram.eval C (law.after_diagram target.denote)
  rw [law.before_eval, law.after_eval, liftOrdinaryExterior_eval]
  rw [law.core_sound]
  exact (law.after.naturality (Diagram.eval C exterior)).symm

/--
Closed whitelist for slides over a one-handle.  There is deliberately no
constructor from an arbitrary `CertifiedMove`.
-/
inductive OrdinaryHandleSlide :
    {source target : Boundary C} →
    Diagram C source target → Diagram C source target → Type (max u v)
  | oneOverOne
      (metadata : SlideMetadata)
      (kind_sound : metadata.kind = .oneOverOne)
      (lineage : ComponentLineage metadata)
      (law : SourcedSlidingLaw C)
      {source target wholeSource wholeTarget : Boundary C}
      (exterior : Diagram C source target)
      (context :
        Context C (.atom source.denote) (.atom target.denote)
          wholeSource wholeTarget) :
      OrdinaryHandleSlide
        (Context.plug C context (ordinaryBefore law exterior))
        (Context.plug C context (ordinaryAfter law exterior))
  | twoOverOne
      (metadata : SlideMetadata)
      (kind_sound : metadata.kind = .twoOverOne)
      (lineage : ComponentLineage metadata)
      (law : SourcedSlidingLaw C)
      {source target wholeSource wholeTarget : Boundary C}
      (exterior : Diagram C source target)
      (context :
        Context C (.atom source.denote) (.atom target.denote)
          wholeSource wholeTarget) :
      OrdinaryHandleSlide
        (Context.plug C context (ordinaryBefore law exterior))
        (Context.plug C context (ordinaryAfter law exterior))

namespace OrdinaryHandleSlide

/-- Every constructor in the closed ordinary-slide whitelist preserves evaluation. -/
theorem sound
    {source target : Boundary C}
    {before after : Diagram C source target}
    (slide : OrdinaryHandleSlide before after) :
    Diagram.eval C before = Diagram.eval C after := by
  cases slide with
  | oneOverOne metadata kind_sound lineage law exterior context =>
      exact Context.eval_plug_congr C context
        (ordinary_exterior_transport_sound law exterior)
  | twoOverOne metadata kind_sound lineage law exterior context =>
      exact Context.eval_plug_congr C context
        (ordinary_exterior_transport_sound law exterior)

end OrdinaryHandleSlide

end OrdinarySliding

section GeneralizedSliding

variable {R : Type uR} [CommSemiring R]
variable {D : Type u} [Category.{v} D] [Preadditive D]
variable [CategoryTheory.Linear R D]
variable [MonoidalCategory D] [BraidedCategory D]
variable [MonoidalPreadditive D] [MonoidalLinear R D]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]
variable {data :
  SlidingCategoryData (R := R) (D := D) (S := S) (I := I)}

/--
Closed whitelist for a two-handle sliding over a two-handle.  The only
constructor requires the actual Lemma 3.3 `SlidingFamily`.
-/
inductive TwoHandleOverTwoSlide :
    {source target : Boundary D} →
    Diagram D source target → Diagram D source target →
      Type (max (max u v) (max uR (max uS uI)))
  | twoOverTwo
      (metadata : SlideMetadata)
      (kind_sound : metadata.kind = .twoOverTwo)
      (lineage : ComponentLineage metadata)
      (family : SlidingFamily data)
      {source target wholeSource wholeTarget : Boundary D}
      (exterior : Diagram D source target)
      (context :
        Context D
          (.atom (data.fixed ⊗ source.denote))
          (.atom (data.fixed ⊗ target.denote))
          wholeSource wholeTarget) :
      TwoHandleOverTwoSlide
        (Context.plug D context
          (beforeExterior family.sourcedFunctorSlidingLaw exterior))
        (Context.plug D context
          (afterExterior family.sourcedFunctorSlidingLaw exterior))

namespace TwoHandleOverTwoSlide

/-- The two-over-two slide is exactly the R5 Lemma 3.4 movie soundness theorem. -/
theorem sound
    {source target : Boundary D}
    {before after : Diagram D source target}
    (slide : TwoHandleOverTwoSlide (data := data) before after) :
    Diagram.eval D before = Diagram.eval D after := by
  cases slide with
  | twoOverTwo metadata kind_sound lineage family exterior context =>
      exact SlidingFamily.lemma34Movie_sound family exterior context

end TwoHandleOverTwoSlide

end GeneralizedSliding

end TwistedYetter.Kirby.KirbyHandleMoves
