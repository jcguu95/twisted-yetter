import Mathlib.Algebra.Category.Grp.Basic
import TwistedYetter.Kirby.PremodularRoleAwareFourManifoldInvariant

/-!
# Intrinsic public interface for the homologically twisted Yetter invariant

The public mathematical arguments are exactly the dependent pairs

* `⟨𝒞, η⟩`, where `𝒞` is premodular and `η` is a tensor automorphism of its
  identity functor; and
* `⟨X, α⟩`, where `X` is a closed oriented smooth four-manifold and
  `α ∈ H₂(X; ℤ)`.

Special Kirby presentations occur only in the construction and computation
interfaces.  They are not part of the intrinsic invariant's input.

The smooth-manifold universe and the four category-neutral topology
boundaries are explicit axioms in `SpecialKirbyHandleTheory.Axioms`.  Representative
independence, all eight local evaluator equalities, finite-movie descent, and
the modular specialization are proved in Lean.
-/

namespace TwistedYetter.Kirby.Final

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.BoundaryStandardization
open TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget
open TwistedYetter.Kirby.LiteratureBackedHomologicalFourManifoldTopology
open TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget
open TwistedYetter.Kirby.PremodularRoleAwareFourManifoldInvariant
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation
open TwistedYetter.Kirby.RoleAwareTableTwoMove
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

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

namespace SpecialKirbyHandleTheory

/--
The presentation coordinate group must be the actual integral second
homology of the manifold being presented.

This deliberately makes the former global-`ℤ` route fail: every downstream
construction must now state which manifold its presentation belongs to.
-/
abbrev AuxiliaryH₂
    (X : ClosedOrientedSmoothFourManifold) :=
  H₂ X

namespace Axioms

/--
T4: a certified standard Kirby move is local in the exact role-aware sense.

The recipe already pins the source and target windows, move kind, participating
component identifiers, roles, orientation, and any components added or
removed.  This topology input supplies only the common-exterior realization
of that certified replacement.  Its indexed result has eight public
constructors, so it cannot substitute an unrelated move, reverse an
orientation, change a component role, or assert an evaluator equality.
-/
axiom certifiedMoveCommonExterior
    {source target : Presentation AuxiliaryH₂}
    (move :
      TopologicalTableTwoMove
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology) :
    Nonempty (StandardMoveLocalFactorization move)

/--
The exact local factorization consumed by the graphical proof.  This theorem
is intentionally a transparent alias of the single category-neutral topology
boundary above.
-/
theorem standardMoveLocalFactorization
    {source target : Presentation AuxiliaryH₂}
    (move :
      TopologicalTableTwoMove
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology) :
    Nonempty (StandardMoveLocalFactorization move) :=
  certifiedMoveCommonExterior move

end Axioms

/--
Compile the imported local factorization by an exhaustive eight-event
constructor dispatch.
-/
noncomputable def localGeometry :
    LocalGeometryRealization AuxiliaryH₂ where
  realize := fun move =>
    (Classical.choice
      (Axioms.standardMoveLocalFactorization move)).compile
  forget_realize := fun move =>
    StandardMoveLocalFactorization.forget_compile
      (Classical.choice
        (Axioms.standardMoveLocalFactorization move))

/-- The role-aware handle-presentation theory used by the formal evaluator. -/
noncomputable def handles : HandlePresentationTheory.{1, 0, 1} :=
  handlePresentationTheory AuxiliaryH₂ localGeometry

namespace Axioms

/--
The handle-theory realization of canonical special Kirby presentations.

This is an explicit external handle-theory input, not a wrapper advertised as
an internally certified theory.
-/
axiom realization :
  HandlePresentationRealization.{1, 0, 1, uX, uX, uX}
    handles
    fourManifoldGeometry

end Axioms

/-- T2: every elementary move realizes the transported marked pair. -/
axiom elementaryMoveSoundness :
  ElementaryMoveHomologicalSoundness Axioms.realization

/-- T1: every intrinsic pair has a role-aware special Kirby presentation. -/
axiom presentationExistence :
  MarkedPresentationExistence Axioms.realization

/-- T3: marked-diffeomorphic presentations are connected by admitted movies. -/
axiom kirbyCerfCompleteness :
  MarkedKirbyCerfCompleteness Axioms.realization

/-- The separately reviewable topology boundary assembled from the axioms above. -/
noncomputable def topologyBoundary :
    HomologicalFourManifoldTopologyBoundary
      handles fourManifoldGeometry where
  realization := Axioms.realization
  elementaryMoveSoundness := elementaryMoveSoundness
  markedPresentationExistence := presentationExistence
  markedKirbyCerfCompleteness := kirbyCerfCompleteness

end SpecialKirbyHandleTheory

/-- Interpret the intrinsic dependent pair in the internal descent language. -/
def homologicalPair
    (Xα : HomologicalFourManifold.{uX}) :
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
    (Xα : HomologicalFourManifold.{uX}) :=
  MarkedPresentationOf
    SpecialKirbyHandleTheory.Axioms.realization
    (homologicalPair Xα)

/-- Every intrinsic homological four-manifold pair has a special presentation. -/
theorem specialKirbyPresentationExists
    (Xα : HomologicalFourManifold.{uX}) :
    Nonempty (SpecialKirbyPresentation Xα) :=
  SpecialKirbyHandleTheory.presentationExistence.presentation
    (homologicalPair Xα)

/-- The intrinsic premodular dependent pair `⟨𝒞, η⟩`. -/
abbrev TwistedPremodularCategory :=
  Σ 𝒞 : PremodularFusionCategory (K := K) (C := C) (S := S),
    TensorIdentityAutomorphism C

/-- The modular subcase, retained only as an input to specialization. -/
abbrev TwistedModularCategory :=
  Σ 𝒞 : ModularFusionCategory (K := K) (C := C) (S := S),
    TensorIdentityAutomorphism C

namespace TwistedModularCategory

/-- Forget only S-matrix nondegeneracy; all ribbon-fusion data are retained. -/
def toPremodular
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S)) :
    TwistedPremodularCategory (K := K) (C := C) (S := S) :=
  ⟨𝒞η.1.premodular, 𝒞η.2⟩

end TwistedModularCategory

/-- The formal scalar attached to one accepted special Kirby presentation. -/
noncomputable def specialKirbyEvaluation
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    {Xα : HomologicalFourManifold.{uX}}
    (presentation : SpecialKirbyPresentation Xα) : K :=
  (presentationEvaluation
      𝒞η.1 𝒞η.2
      SpecialKirbyHandleTheory.AuxiliaryH₂
      SpecialKirbyHandleTheory.localGeometry).markedValue
    presentation.markedPresentation

/--
The homologically twisted Yetter candidate.  Its only two currently
unproved local graphical inputs are the explicit attach/detach evaluation
axioms in `TwoOverTwoAttachDetach`.
-/
noncomputable def TwistedYetter
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    (Xα : HomologicalFourManifold.{uX}) : K :=
  (SpecialKirbyHandleTheory.topologyBoundary.constructInvariant
      (presentationEvaluation
        𝒞η.1 𝒞η.2
        SpecialKirbyHandleTheory.AuxiliaryH₂
        SpecialKirbyHandleTheory.localGeometry)
      (presentationEvaluation_localInvariant
        𝒞η.1 𝒞η.2
        SpecialKirbyHandleTheory.AuxiliaryH₂
        SpecialKirbyHandleTheory.localGeometry)).EvalC
    Xα.1 Xα.2

/-- The candidate agrees with every accepted special Kirby presentation. -/
theorem TwistedYetter_on_specialKirbyPresentation
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    {Xα : HomologicalFourManifold.{uX}}
    (presentation : SpecialKirbyPresentation Xα) :
    TwistedYetter 𝒞η Xα =
      specialKirbyEvaluation 𝒞η presentation := by
  simpa [TwistedYetter, specialKirbyEvaluation] using
    SpecialKirbyHandleTheory.topologyBoundary.admissibleKirbyCerfTheorem
      |>.constructInvariant_EvalC_eq_presentation
        (SpecialKirbyHandleTheory.topologyBoundary.admissibleFormula
          (presentationEvaluation
            𝒞η.1 𝒞η.2
            SpecialKirbyHandleTheory.AuxiliaryH₂
            SpecialKirbyHandleTheory.localGeometry))
        (SpecialKirbyHandleTheory.topologyBoundary.admissibleFormula_movieInvariant
          (presentationEvaluation
            𝒞η.1 𝒞η.2
            SpecialKirbyHandleTheory.AuxiliaryH₂
            SpecialKirbyHandleTheory.localGeometry)
          (presentationEvaluation_localInvariant
            𝒞η.1 𝒞η.2
            SpecialKirbyHandleTheory.AuxiliaryH₂
            SpecialKirbyHandleTheory.localGeometry))
        Xα.1 Xα.2 presentation

/-- Diffeomorphism invariance, with the class transported on `H₂`. -/
theorem TwistedYetter_diffeomorphism_invariant
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    {X Y : ClosedOrientedSmoothFourManifold.{uX}}
    (f : orientedDiffeomorphism.Hom X Y)
    (α : H₂ X) :
    TwistedYetter 𝒞η ⟨X, α⟩ =
      TwistedYetter 𝒞η ⟨Y, inducedH₂ f α⟩ := by
  simpa [TwistedYetter] using
    (SpecialKirbyHandleTheory.topologyBoundary.constructInvariant
        (presentationEvaluation
          𝒞η.1 𝒞η.2
          SpecialKirbyHandleTheory.AuxiliaryH₂
          SpecialKirbyHandleTheory.localGeometry)
        (presentationEvaluation_localInvariant
          𝒞η.1 𝒞η.2
          SpecialKirbyHandleTheory.AuxiliaryH₂
          SpecialKirbyHandleTheory.localGeometry))
      |>.diffeomorphismInvariant f α

/-- The modular candidate is the premodular candidate after
forgetting S-matrix nondegeneracy. -/
noncomputable def TwistedYetterModular
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S))
    (Xα : HomologicalFourManifold.{uX}) : K :=
  TwistedYetter 𝒞η.toPremodular Xα

/-- Modular invariance is a specialization, not a second proof. -/
theorem TwistedYetterModular_diffeomorphism_invariant
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S))
    {X Y : ClosedOrientedSmoothFourManifold.{uX}}
    (f : orientedDiffeomorphism.Hom X Y)
    (α : H₂ X) :
    TwistedYetterModular 𝒞η ⟨X, α⟩ =
      TwistedYetterModular 𝒞η ⟨Y, inducedH₂ f α⟩ :=
  TwistedYetter_diffeomorphism_invariant
    𝒞η.toPremodular f α

namespace TwistedYetter

/--
An executable implementation of the presentation-level computation.

The class is deliberately separate from the abstract EGNO category.  A
Lean-native implementation or a verified foreign-function bridge supplies an
instance.  Merely assuming the class does not manufacture executable code.
-/
class Computable
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S)) where
  compute :
    {Xα : HomologicalFourManifold.{uX}} →
      SpecialKirbyPresentation Xα → K
  correct :
    {Xα : HomologicalFourManifold.{uX}} →
      (presentation : SpecialKirbyPresentation Xα) →
        TwistedYetter 𝒞η Xα = compute presentation

/-- Execute the installed presentation-level implementation. -/
def compute
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    [implementation : Computable 𝒞η]
    {Xα : HomologicalFourManifold.{uX}}
    (presentation : SpecialKirbyPresentation Xα) : K :=
  implementation.compute presentation

/--
The correctness proof required from the installed executable implementation.

This theorem introduces no global axiom: constructing a `Computable` instance
requires supplying the proof together with the executable function.
-/
theorem compute_correct
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    [implementation : Computable 𝒞η]
    {Xα : HomologicalFourManifold.{uX}}
    (presentation : SpecialKirbyPresentation Xα) :
    TwistedYetter 𝒞η Xα =
      compute 𝒞η presentation := by
  exact implementation.correct presentation

end TwistedYetter

end

end TwistedYetter.Kirby.Final
