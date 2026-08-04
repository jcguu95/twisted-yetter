import TwistedYetter.Kirby.Final.Semantics.Independent.Evaluator

/-!
# Category evidence for the stable no-go calculation

This module isolates the category-literature inputs used by the explicit
standard-manifold calculations.  In particular, the axiom below is only the
standard Hopf-link specialization of framed-ribbon coherence.  It says
nothing about Kirby calculus, four-manifolds, homology markings, character
weights, or evaluator normalization.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- Positive crossing of two oriented simple strands. -/
def positiveCrossingWordMorphism
    (𝒞 : BundledPremodularCategory K)
    (first second : OrientedSimple 𝒞) :
    ribbonWordObject 𝒞 [first, second] ⟶
      ribbonWordObject 𝒞 [second, first] :=
  (α_ _ _ _).inv ≫
    ((β_ _ _).hom ⊗ₘ 𝟙 _) ≫
    (α_ _ _ _).hom

/--
The standard cup--cross--cross--cap ribbon presentation of the positive Hopf
link whose two components are labelled by `first` and `second`.
-/
def standardPositiveHopfClosure
    (𝒞 : BundledPremodularCategory K)
    (first second : 𝒞.simples.Simple) : 𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C :=
  let firstPositive : OrientedSimple 𝒞 :=
    { label := first, direction := .forward }
  let firstNegative : OrientedSimple 𝒞 :=
    { label := first, direction := .dual }
  let secondPositive : OrientedSimple 𝒞 :=
    { label := second, direction := .forward }
  let secondNegative : OrientedSimple 𝒞 :=
    { label := second, direction := .dual }
  canonicalPositiveNegativeBirth 𝒞 first ≫
    contextualizeRibbonMorphism 𝒞
      [firstPositive] [] [secondPositive, secondNegative] [firstNegative]
      (canonicalPositiveNegativeBirth 𝒞 second) ≫
    contextualizeRibbonMorphism 𝒞
      [] [firstPositive, secondPositive] [secondPositive, firstPositive]
      [secondNegative, firstNegative]
      (positiveCrossingWordMorphism 𝒞 firstPositive secondPositive) ≫
    contextualizeRibbonMorphism 𝒞
      [secondPositive] [firstPositive, secondNegative]
      [secondNegative, firstPositive] [firstNegative]
      (positiveCrossingWordMorphism 𝒞 firstPositive secondNegative) ≫
    contextualizeRibbonMorphism 𝒞
      [] [secondPositive, secondNegative] [] [firstPositive, firstNegative]
      (canonicalPositiveNegativeDeath 𝒞 second) ≫
    canonicalPositiveNegativeDeath 𝒞 first

/--
The standard positive Hopf ribbon diagram evaluates as the canonical pivotal
trace of positive monodromy:

`Hopf(A,B) = tr_{A tensor B}(c_{B,A} after c_{A,B})`.

This is the elementary Hopf-link instance of framed-ribbon graphical
coherence.  It is retained as an explicit category-literature axiom because
the current frozen graphical interface treats isotopy witnesses abstractly
and therefore cannot construct this particular witness internally.
-/
axiom standardPositiveHopfClosure_eq_monodromyTrace
    (𝒞 : BundledPremodularCategory K)
    (first second : 𝒞.simples.Simple) :
    standardPositiveHopfClosure 𝒞 first second =
      𝒞.canonicalRibbonTrace
        (monodromyHom (𝒞.simpleObject first) (𝒞.simpleObject second))

end

end TwistedYetter.StableNoGo
