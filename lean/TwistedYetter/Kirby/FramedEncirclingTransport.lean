import TwistedYetter.Kirby.FramingNaturality
import TwistedYetter.Kirby.KirbyColorEncirclingTransport

/-!
# Kirby-colour encircling transport in arbitrary framed contexts

The pointwise encircling identity extends from one exposed strand to an
arbitrary tensor product of strands and an arbitrarily framed, linked
encircling knot.  The proof is locality plus naturality: external crossings,
extrema, coupons, and twists form a typed diagram, and tensoring that diagram
on the left by the fixed object commutes with the encircling operator.

This file keeps the external diagram visible.  It is not replaced by an
untyped "arbitrary knot" token.
-/

namespace TwistedYetter.Kirby.FramedEncirclingTransport

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.CategoricalMovie
open TwistedYetter.Kirby.KirbyColorEncirclingTransport
open TwistedYetter.Kirby.HandleSlide

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/--
Change from the atomic presentation of `fixed ⊗ boundary.denote` to the
explicit two-part boundary.  Both denote the same categorical object, so the
adapter evaluates to an identity morphism.
-/
def exposeTensorBoundary (fixed : C) (boundary : Boundary C) :
    Diagram C
      (.atom (fixed ⊗ boundary.denote))
      (.tensor (.atom fixed) boundary) :=
  Diagram.coupon "expose-fixed-tensor-boundary" (𝟙 _)

/-- The inverse boundary adapter, again evaluating to an identity. -/
def packTensorBoundary (fixed : C) (boundary : Boundary C) :
    Diagram C
      (.tensor (.atom fixed) boundary)
      (.atom (fixed ⊗ boundary.denote)) :=
  Diagram.coupon "pack-fixed-tensor-boundary" (𝟙 _)

/--
Tensor a visible external tangle on the left by the fixed object, retaining
the external crossings, extrema, and coupons in the syntax tree.
-/
def liftExterior
    (fixed : C)
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Diagram C
      (.atom (fixed ⊗ source.denote))
      (.atom (fixed ⊗ target.denote)) :=
  exposeTensorBoundary fixed source ≫ᵈ
    (Diagram.identity (.atom fixed) ⊗ᵈ exterior) ≫ᵈ
      packTensorBoundary fixed target

/-- The visible lift evaluates to the map of the functor `fixed ⊗ -`. -/
theorem liftExterior_eval
    (fixed : C)
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Diagram.eval C (liftExterior fixed exterior) =
      (tensorLeft fixed).map (Diagram.eval C exterior) := by
  simp [liftExterior, exposeTensorBoundary, packTensorBoundary, Diagram.eval,
    Boundary.denote, MonoidalCategory.id_tensorHom]

/--
The framed exterior immediately after the source encircling endpoint.
-/
def beforeExterior
    {fixed : C}
    (law : SourcedTensorLeftEncirclingLaw fixed)
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Diagram C
      (.atom (fixed ⊗ source.denote))
      (.atom (fixed ⊗ target.denote)) :=
  law.sourceDiagram source.denote ≫ᵈ liftExterior fixed exterior

/--
The same framed exterior immediately before the target encircling endpoint.
-/
def afterExterior
    {fixed : C}
    (law : SourcedTensorLeftEncirclingLaw fixed)
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Diagram C
      (.atom (fixed ⊗ source.denote))
      (.atom (fixed ⊗ target.denote)) :=
  liftExterior fixed exterior ≫ᵈ law.targetDiagram target.denote

/--
Before closure, every typed external tangle passes through the encircling
window.  The proof uses the derived pointwise equality and target-endpoint
naturality.
-/
theorem exterior_transport_sound
    {fixed : C}
    (law : SourcedTensorLeftEncirclingLaw fixed)
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Diagram.eval C (beforeExterior law exterior) =
      Diagram.eval C (afterExterior law exterior) := by
  change Diagram.eval C (law.sourceDiagram source.denote) ≫
      Diagram.eval C (liftExterior fixed exterior) =
    Diagram.eval C (liftExterior fixed exterior) ≫
      Diagram.eval C (law.targetDiagram target.denote)
  calc
    _ = law.sourceOperator.app source.denote ≫
        (tensorLeft fixed).map (Diagram.eval C exterior) := by
      rw [law.source_eval]
      exact congrArg
        (fun morphism => law.sourceOperator.app source.denote ≫ morphism)
        (liftExterior_eval fixed exterior)
    _ = law.targetOperator.app source.denote ≫
        (tensorLeft fixed).map (Diagram.eval C exterior) := by
      rw [law.source_eq_target]
    _ = (tensorLeft fixed).map (Diagram.eval C exterior) ≫
        law.targetOperator.app target.denote :=
      (law.targetOperator.naturality (Diagram.eval C exterior)).symm
    _ = _ := by
      rw [liftExterior_eval]
      exact congrArg
        (fun morphism =>
          (tensorLeft fixed).map (Diagram.eval C exterior) ≫ morphism)
        (law.target_eval target.denote).symm

/-- Framed encircling transport packaged as one certified local movie. -/
def exteriorTransportMove
    {fixed : C}
    (law : SourcedTensorLeftEncirclingLaw fixed)
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    CertifiedMove
      (beforeExterior law exterior)
      (afterExterior law exterior) where
  label := "kirby-encircling-arbitrary-framed-exterior"
  sound := exterior_transport_sound law exterior

/-- Framed encircling transport as a one-frame movie. -/
def exteriorTransportMovie
    {fixed : C}
    (law : SourcedTensorLeftEncirclingLaw fixed)
    {source target : Boundary C}
    (exterior : Diagram C source target) :
    Movie
      (beforeExterior law exterior)
      (afterExterior law exterior) :=
  Movie.one (exteriorTransportMove law exterior)

/--
The arbitrary framed exterior may itself sit inside any well-typed outer
context.  Nested contexts are already represented by `Context.compose`.
-/
def exteriorTransportInContext
    {fixed : C}
    (law : SourcedTensorLeftEncirclingLaw fixed)
    {source target wholeSource wholeTarget : Boundary C}
    (exterior : Diagram C source target)
    (context :
      Context C
        (.atom (fixed ⊗ source.denote))
        (.atom (fixed ⊗ target.denote))
        wholeSource wholeTarget) :
    Movie
      (Context.plug C context (beforeExterior law exterior))
      (Context.plug C context (afterExterior law exterior)) :=
  Movie.inContext context (exteriorTransportMovie law exterior)

/-- Soundness of the complete outer-context movie. -/
theorem exterior_transport_in_context_sound
    {fixed : C}
    (law : SourcedTensorLeftEncirclingLaw fixed)
    {source target wholeSource wholeTarget : Boundary C}
    (exterior : Diagram C source target)
    (context :
      Context C
        (.atom (fixed ⊗ source.denote))
        (.atom (fixed ⊗ target.denote))
        wholeSource wholeTarget) :
    Diagram.eval C
        (Context.plug C context (beforeExterior law exterior)) =
      Diagram.eval C
        (Context.plug C context (afterExterior law exterior)) :=
  Movie.sound (exteriorTransportInContext law exterior context)

/--
A closed framed context has no boundary.  This is the exact specialization
needed when the entire framed link is evaluated as an endomorphism of the
monoidal unit.
-/
structure ClosedFramedContext
    (fixed : C)
    (source target : Boundary C) where
  context :
    Context C
      (.atom (fixed ⊗ source.denote))
      (.atom (fixed ⊗ target.denote))
      .unit .unit

namespace ClosedFramedContext

/-- The closed source encircling diagram. -/
def before
    {fixed : C}
    {source target : Boundary C}
    (closed : ClosedFramedContext fixed source target)
    (law : SourcedTensorLeftEncirclingLaw fixed)
    (exterior : Diagram C source target) :
    Diagram C .unit .unit :=
  Context.plug C closed.context (beforeExterior law exterior)

/-- The closed target encircling diagram. -/
def after
    {fixed : C}
    {source target : Boundary C}
    (closed : ClosedFramedContext fixed source target)
    (law : SourcedTensorLeftEncirclingLaw fixed)
    (exterior : Diagram C source target) :
    Diagram C .unit .unit :=
  Context.plug C closed.context (afterExterior law exterior)

/--
Closed-link encircling transport.  Multiple strands are represented by the
parenthesized `source` and `target` boundaries; arbitrary linking, framing,
coupons, and extrema remain in `exterior` and `context`.
-/
theorem closed_transport_sound
    {fixed : C}
    {source target : Boundary C}
    (closed : ClosedFramedContext fixed source target)
    (law : SourcedTensorLeftEncirclingLaw fixed)
    (exterior : Diagram C source target) :
    Diagram.eval C (closed.before law exterior) =
      Diagram.eval C (closed.after law exterior) :=
  exterior_transport_in_context_sound law exterior closed.context

end ClosedFramedContext

namespace EncirclingTransportFamily

open scoped BigOperators

universe uR uS uI

variable {R : Type uR} [CommSemiring R]
variable [Preadditive C] [CategoryTheory.Linear R C]
variable [MonoidalPreadditive C] [MonoidalLinear R C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]
variable {data :
  EncirclingTransportData (R := R) (D := C) (S := S) (I := I)}

/--
The public framed constructor starts from the pointwise encircling family;
there is no independent arbitrary-knot equality input.
-/
noncomputable def framedTransportMovie
    (family : EncirclingTransportFamily data)
    {source target wholeSource wholeTarget : Boundary C}
    (exterior : Diagram C source target)
    (context :
      Context C
        (.atom (data.fixed ⊗ source.denote))
        (.atom (data.fixed ⊗ target.denote))
        wholeSource wholeTarget) :
    Movie
      (Context.plug C context
        (beforeExterior family.sourcedEncirclingLaw exterior))
      (Context.plug C context
        (afterExterior family.sourcedEncirclingLaw exterior)) :=
  exteriorTransportInContext family.sourcedEncirclingLaw exterior context

/-- Kernel-checked soundness of the public framed constructor. -/
theorem framedEncirclingTransport_sound
    (family : EncirclingTransportFamily data)
    {source target wholeSource wholeTarget : Boundary C}
    (exterior : Diagram C source target)
    (context :
      Context C
        (.atom (data.fixed ⊗ source.denote))
        (.atom (data.fixed ⊗ target.denote))
        wholeSource wholeTarget) :
    Diagram.eval C
        (Context.plug C context
          (beforeExterior family.sourcedEncirclingLaw exterior)) =
      Diagram.eval C
        (Context.plug C context
          (afterExterior family.sourcedEncirclingLaw exterior)) :=
  Movie.sound (framedTransportMovie family exterior context)

end EncirclingTransportFamily

end TwistedYetter.Kirby.FramedEncirclingTransport
