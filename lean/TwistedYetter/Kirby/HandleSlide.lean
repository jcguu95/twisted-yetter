import TwistedYetter.Kirby.CategoricalMovie

/-!
# Coupon-aware handle-slide interface

The fusion-category sliding lemma is isolated as equality between two natural
endomorphisms of the identity functor. This module does not assert that such a
law exists. Given a proved law, transport of arbitrary coupons through the
handle-slide window follows from naturality and is not an additional axiom.
-/

namespace TwistedYetter.Kirby.HandleSlide

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.CategoricalMovie

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/--
A diagram-backed sliding law for an arbitrary endofunctor.

Lemma 3.3 acts on `F(X) ⊗ A`, so its natural transformations belong to the
functor `F(X) ⊗ -`, not generally to the identity functor.  The older
`SourcedSlidingLaw` below is the identity-functor specialization used by the
initial bootstrap.
-/
structure SourcedFunctorSlidingLaw
    (G : C ⥤ C) where
  before_diagram : (X : C) →
    Diagram C (.atom (G.obj X)) (.atom (G.obj X))
  after_diagram : (X : C) →
    Diagram C (.atom (G.obj X)) (.atom (G.obj X))
  before : G ⟶ G
  after : G ⟶ G
  before_eval : (X : C) →
    Diagram.eval C (before_diagram X) = before.app X
  after_eval : (X : C) →
    Diagram.eval C (after_diagram X) = after.app X
  core_sound : before = after
  diagram_schema : String
  diagram_content_hash : String
  source_ref : String
  source_locator : String

namespace SourcedFunctorSlidingLaw

variable {G : C ⥤ C}

/-- The functorial slide window immediately before an arbitrary coupon. -/
def beforeCoupon (law : SourcedFunctorSlidingLaw G) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram C (.atom (G.obj X)) (.atom (G.obj Y)) :=
  law.before_diagram X ≫ᵈ
    atomicCoupon name (G.map f)

/-- The functorial slide window after an arbitrary coupon. -/
def afterCoupon (law : SourcedFunctorSlidingLaw G) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram C (.atom (G.obj X)) (.atom (G.obj Y)) :=
  atomicCoupon name (G.map f) ≫ᵈ
    law.after_diagram Y

/--
An arbitrary coupon crosses a functor-valued slide window.  This uses the
proved core equality and naturality of the resulting natural transformation.
-/
theorem coupon_transport_sound
    (law : SourcedFunctorSlidingLaw G) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram.eval C (law.beforeCoupon name f) =
      Diagram.eval C (law.afterCoupon name f) := by
  change Diagram.eval C (law.before_diagram X) ≫ G.map f =
    G.map f ≫ Diagram.eval C (law.after_diagram Y)
  rw [law.before_eval, law.after_eval]
  rw [law.core_sound]
  exact (law.after.naturality f).symm

/-- The functorial coupon transport as one certified movie step. -/
def couponTransportMove
    (law : SourcedFunctorSlidingLaw G) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    CertifiedMove (law.beforeCoupon name f) (law.afterCoupon name f) where
  label := "coupon-through-functor-handle-slide-window:" ++ name
  sound := law.coupon_transport_sound name f

/-- The functorial coupon transport as a one-frame movie. -/
def couponTransportMovie
    (law : SourcedFunctorSlidingLaw G) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Movie (law.beforeCoupon name f) (law.afterCoupon name f) :=
  Movie.one (law.couponTransportMove name f)

end SourcedFunctorSlidingLaw

/--
Evaluator-side interface to a proved handle-slide lemma.

For the generalized dichromatic invariant, a future category module should
construct this datum from the generalized sliding property rather than postulate
it globally. The source fields make the provenance visible in generated audit
artifacts but carry no mathematical force.
-/
structure SourcedSlidingLaw (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] where
  before_diagram : (X : C) → Diagram C (.atom X) (.atom X)
  after_diagram : (X : C) → Diagram C (.atom X) (.atom X)
  before : 𝟭 C ⟶ 𝟭 C
  after : 𝟭 C ⟶ 𝟭 C
  before_eval : (X : C) → Diagram.eval C (before_diagram X) = before.app X
  after_eval : (X : C) → Diagram.eval C (after_diagram X) = after.app X
  core_sound : before = after
  diagram_schema : String
  diagram_content_hash : String
  source_ref : String
  source_locator : String

namespace SourcedSlidingLaw

/-- The local frame with a slide window immediately before an arbitrary coupon. -/
def beforeCoupon (law : SourcedSlidingLaw C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram C (.atom X) (.atom Y) :=
  law.before_diagram X ≫ᵈ
    atomicCoupon name f

/-- The local frame after the coupon has crossed the handle-slide window. -/
def afterCoupon (law : SourcedSlidingLaw C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram C (.atom X) (.atom Y) :=
  atomicCoupon name f ≫ᵈ
    law.after_diagram Y

/--
An arbitrary coupon crosses the handle-slide window. Only the supplied core
sliding equality and naturality of its natural transformation are used.
-/
theorem coupon_transport_sound (law : SourcedSlidingLaw C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Diagram.eval C (law.beforeCoupon name f) =
      Diagram.eval C (law.afterCoupon name f) := by
  change Diagram.eval C (law.before_diagram X) ≫ f =
    f ≫ Diagram.eval C (law.after_diagram Y)
  rw [law.before_eval, law.after_eval]
  rw [law.core_sound]
  simpa using (law.after.naturality f).symm

/-- The coupon transport theorem packaged as one certified movie step. -/
def couponTransportMove (law : SourcedSlidingLaw C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    CertifiedMove (law.beforeCoupon name f) (law.afterCoupon name f) where
  label := "coupon-through-handle-slide-window:" ++ name
  sound := law.coupon_transport_sound name f

/-- A one-frame proof object for coupon-assisted handle-slide transport. -/
def couponTransportMovie (law : SourcedSlidingLaw C) {X Y : C}
    (name : String) (f : X ⟶ Y) :
    Movie (law.beforeCoupon name f) (law.afterCoupon name f) :=
  Movie.one (law.couponTransportMove name f)

/--
Coupon-assisted handle-slide transport remains valid inside an arbitrary
well-typed surrounding Kirby/tangle context.
-/
def couponTransportInContext
    (law : SourcedSlidingLaw C)
    {X Y : C}
    (name : String)
    (f : X ⟶ Y)
    {wholeSource wholeTarget : Boundary C}
    (context :
      Context C (.atom X) (.atom Y) wholeSource wholeTarget) :
    Movie
      (Context.plug C context (law.beforeCoupon name f))
      (Context.plug C context (law.afterCoupon name f)) :=
  Movie.inContext context (law.couponTransportMovie name f)

/-- Soundness of the complete context-embedded coupon-assisted slide movie. -/
theorem coupon_transport_in_context_sound
    (law : SourcedSlidingLaw C)
    {X Y : C}
    (name : String)
    (f : X ⟶ Y)
    {wholeSource wholeTarget : Boundary C}
    (context :
      Context C (.atom X) (.atom Y) wholeSource wholeTarget) :
    Diagram.eval C
        (Context.plug C context (law.beforeCoupon name f)) =
      Diagram.eval C
        (Context.plug C context (law.afterCoupon name f)) :=
  Movie.sound (law.couponTransportInContext name f context)

end SourcedSlidingLaw

end TwistedYetter.Kirby.HandleSlide
