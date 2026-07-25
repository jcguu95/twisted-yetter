import Mathlib.Algebra.Category.Grp.Basic
import TwistedYetter.Kirby.Final.ModularClosedFourManifoldInvariant
import TwistedYetter.Kirby.ModularAlgebraicSurface

/-!
# Intrinsic public interface for the homologically twisted Yetter invariant

The public mathematical arguments are exactly the dependent pairs

* `⟨𝒞, η⟩`, where `𝒞` is modular and `η` is a tensor automorphism of its
  identity functor; and
* `⟨X, α⟩`, where `X` is a closed oriented smooth four-manifold and
  `α ∈ H₂(X; ℤ)`.

Special Kirby presentations occur only in the construction and computation
interfaces.  They are not part of the intrinsic invariant's input.

The smooth-manifold universe and the literature-backed realization of the
current canonical special-Kirby calculus are explicit axioms in
`SpecialKirbyFoundation`.  The existing local categorical calculations and
the descent from Kirby movies are proved in Lean.
-/

namespace TwistedYetter.Kirby.Final

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.BoundaryStandardization
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalModularKirbyInvariance
open TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry
open TwistedYetter.Kirby.LiteratureBackedHomologicalFourManifoldTopology
open TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget

universe uK uC vC uX

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-!
## Ambient smooth four-manifold foundation

These declarations are the deliberate stopping point before formalizing
smooth atlases, compactness, orientation, singular homology, and the
functoriality of homology from foundations.
-/

/-- The externally supplied type of closed oriented smooth four-manifolds. -/
axiom ClosedOrientedSmoothFourManifold : Type uX

/-- Integral second homology as a bundled abelian group. -/
axiom H₂ :
  ClosedOrientedSmoothFourManifold → AddCommGrpCat.{uX}

/-- Orientation-preserving diffeomorphisms form a groupoid. -/
axiom orientedDiffeomorphism :
  OrientedDiffeomorphismGroupoid.{uX, uX}
    ClosedOrientedSmoothFourManifold

/-- The map on integral second homology induced by a diffeomorphism. -/
axiom inducedH₂
    {X Y : ClosedOrientedSmoothFourManifold} :
    orientedDiffeomorphism.Hom X Y →
      H₂ X ≃+ H₂ Y

/-- The identity diffeomorphism induces the identity on `H₂`. -/
axiom inducedH₂_identity
    (X : ClosedOrientedSmoothFourManifold) :
    inducedH₂ (orientedDiffeomorphism.identity X) =
      AddEquiv.refl (H₂ X)

/-- Induced maps on `H₂` respect composition of diffeomorphisms. -/
axiom inducedH₂_compose
    {X Y Z : ClosedOrientedSmoothFourManifold}
    (first : orientedDiffeomorphism.Hom X Y)
    (second : orientedDiffeomorphism.Hom Y Z) :
    inducedH₂ (orientedDiffeomorphism.compose first second) =
      (inducedH₂ (X := X) (Y := Y) first).trans
        (inducedH₂ (X := Y) (Y := Z) second)

/-- The geometry object used internally by the already-proved descent layer. -/
abbrev fourManifoldGeometry :
    HomologicalFourManifoldTheory.{uX, uX, uX} where
  FourManifold := ClosedOrientedSmoothFourManifold
  SecondHomology := fun X => H₂ X
  secondHomologyAddCommGroup := fun _ => inferInstance
  orientedDiffeomorphism := orientedDiffeomorphism
  homologyMap := inducedH₂
  homologyMap_identity := inducedH₂_identity
  homologyMap_compose := inducedH₂_compose

/-- The intrinsic dependent pair `⟨X, α⟩`. -/
abbrev HomologicalFourManifold :=
  Σ X : ClosedOrientedSmoothFourManifold, H₂ X

namespace SpecialKirbyFoundation

/-!
The current canonical evaluator is indexed by a content-addressed
presentation scope and an auxiliary additive group.  Those are implementation
coordinates of the established special-Kirby calculus, not arguments of the
intrinsic invariant.
-/

/-- Fixed implementation scope of the admitted special-Kirby calculus. -/
axiom presentationScope :
  ClosedConnectedSmoothOrientedFourManifoldInput

/-- Integral auxiliary coordinates used by the canonical presentation type. -/
abbrev AuxiliaryH₂ := ℤ

/-- The canonical handle-presentation theory used by the formal evaluator. -/
noncomputable def handles : HandlePresentationTheory :=
  handlePresentationTheory presentationScope AuxiliaryH₂

/--
External realization of canonical handle-chain markings as actual manifold
homology classes.
-/
axiom realization :
  HandlePresentationRealization handles fourManifoldGeometry

/-- Every elementary canonical move realizes the transported marked pair. -/
axiom elementaryMoveSoundness :
  ElementaryMoveHomologicalSoundness realization

/-- Every intrinsic pair `⟨X, α⟩` has a canonical special-Kirby presentation. -/
axiom presentationExistence :
  MarkedPresentationExistence realization

/-- Marked-diffeomorphic presentations are connected by the admitted movies. -/
axiom kirbyCerfCompleteness :
  MarkedKirbyCerfCompleteness realization

/-- The separately reviewable topology boundary assembled from the axioms above. -/
noncomputable def topologyBoundary :
    HomologicalFourManifoldTopologyBoundary
      handles fourManifoldGeometry where
  realization := realization
  elementaryMoveSoundness := elementaryMoveSoundness
  markedPresentationExistence := presentationExistence
  markedKirbyCerfCompleteness := kirbyCerfCompleteness

end SpecialKirbyFoundation

/-- Interpret the intrinsic dependent pair in the internal descent language. -/
def homologicalPair
    (Xα : HomologicalFourManifold) :
    fourManifoldGeometry.MarkedManifold where
  manifold := Xα.1
  alpha := Xα.2

/--
A special Kirby presentation of the intrinsic pair `⟨X, α⟩`.

The underlying canonical presentation has one zero-handle and one
four-handle by the admitted special-presentation calculus.  The indexed type
also records the external realization and the equality of its transported
handle-chain class with `α`.
-/
abbrev SpecialKirbyPresentation
    (Xα : HomologicalFourManifold) :=
  MarkedPresentationOf
    SpecialKirbyFoundation.realization
    (homologicalPair Xα)

/-- Every intrinsic homological four-manifold pair has a special presentation. -/
theorem specialKirbyPresentationExists
    (Xα : HomologicalFourManifold) :
    Nonempty (SpecialKirbyPresentation Xα) :=
  SpecialKirbyFoundation.presentationExistence.presentation
    (homologicalPair Xα)

/-- The intrinsic dependent pair `⟨𝒞, η⟩`. -/
abbrev TwistedModularCategory :=
  Σ 𝒞 : ModularCategory (K := K) (C := C) (S := S),
    𝒞.TensorIdentityAutomorphism

/-- The formal scalar attached to one accepted special Kirby presentation. -/
noncomputable def specialKirbyEvaluation
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S))
    {Xα : HomologicalFourManifold}
    (presentation : SpecialKirbyPresentation Xα) : K :=
  (presentationEvaluation
      𝒞η.1 𝒞η.2
      SpecialKirbyFoundation.presentationScope
      SpecialKirbyFoundation.AuxiliaryH₂).markedValue
    presentation.markedPresentation

/--
The intrinsic homologically twisted Yetter invariant.

Its only mathematical arguments are `⟨𝒞, η⟩` and `⟨X, α⟩`.
Noncomputability comes solely from selecting a presentation of an abstract
manifold pair.
-/
noncomputable def TwistedYetter
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S))
    (Xα : HomologicalFourManifold) : K :=
  (SpecialKirbyFoundation.topologyBoundary.constructInvariant
      (presentationEvaluation
        𝒞η.1 𝒞η.2
        SpecialKirbyFoundation.presentationScope
        SpecialKirbyFoundation.AuxiliaryH₂)
      (evalC_local_move_invariant 𝒞η.1 𝒞η.2)).EvalC
    Xα.1 Xα.2

/--
The intrinsic invariant agrees with the formal evaluation of every accepted
special Kirby presentation.
-/
theorem TwistedYetter_on_specialKirbyPresentation
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S))
    {Xα : HomologicalFourManifold}
    (presentation : SpecialKirbyPresentation Xα) :
    TwistedYetter 𝒞η Xα =
      specialKirbyEvaluation 𝒞η presentation := by
  simpa [TwistedYetter, specialKirbyEvaluation] using
    SpecialKirbyFoundation.topologyBoundary.admissibleKirbyCerfTheorem
      |>.constructInvariant_EvalC_eq_presentation
        (SpecialKirbyFoundation.topologyBoundary.admissibleFormula
          (presentationEvaluation
            𝒞η.1 𝒞η.2
            SpecialKirbyFoundation.presentationScope
            SpecialKirbyFoundation.AuxiliaryH₂))
        (SpecialKirbyFoundation.topologyBoundary.admissibleFormula_movieInvariant
          (presentationEvaluation
            𝒞η.1 𝒞η.2
            SpecialKirbyFoundation.presentationScope
            SpecialKirbyFoundation.AuxiliaryH₂)
          (evalC_local_move_invariant 𝒞η.1 𝒞η.2))
        Xα.1 Xα.2 presentation

/-- Diffeomorphism invariance with the displayed class transported on `H₂`. -/
theorem TwistedYetter_diffeomorphism_invariant
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S))
    {X Y : ClosedOrientedSmoothFourManifold}
    (f : orientedDiffeomorphism.Hom X Y)
    (α : H₂ X) :
    TwistedYetter 𝒞η ⟨X, α⟩ =
      TwistedYetter 𝒞η ⟨Y, inducedH₂ f α⟩ := by
  simpa [TwistedYetter] using
    (SpecialKirbyFoundation.topologyBoundary.constructInvariant
        (presentationEvaluation
          𝒞η.1 𝒞η.2
          SpecialKirbyFoundation.presentationScope
          SpecialKirbyFoundation.AuxiliaryH₂)
        (evalC_local_move_invariant 𝒞η.1 𝒞η.2))
      |>.diffeomorphismInvariant f α

namespace TwistedYetter

/--
An executable implementation of the presentation-level computation.

The class is deliberately separate from the abstract EGNO category.  A
Lean-native implementation or a verified foreign-function bridge supplies an
instance.  Merely assuming the class does not manufacture executable code.
-/
class Computable
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S)) where
  compute :
    {Xα : HomologicalFourManifold} →
      SpecialKirbyPresentation Xα → K

/-- Execute the installed presentation-level implementation. -/
def compute
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S))
    [implementation : Computable 𝒞η]
    {Xα : HomologicalFourManifold}
    (presentation : SpecialKirbyPresentation Xα) : K :=
  implementation.compute presentation

/--
External correctness boundary between the executable implementation and the
intrinsic invariant.

This is intentionally an axiom at the current project stage.
-/
axiom compute_correct
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S))
    [Computable 𝒞η]
    {Xα : HomologicalFourManifold}
    (presentation : SpecialKirbyPresentation Xα) :
    TwistedYetter 𝒞η Xα =
      compute 𝒞η presentation

end TwistedYetter

end

end TwistedYetter.Kirby.Final
