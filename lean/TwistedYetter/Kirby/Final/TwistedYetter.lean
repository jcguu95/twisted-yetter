import Mathlib.Algebra.Category.Grp.Basic
import TwistedYetter.Kirby.DependentRoleAwareFourManifoldInvariant

/-!
# Public homologically twisted Yetter invariant

The public inputs are exactly `⟨𝒞, η⟩` and `⟨X, α⟩`, with
`α : H₂(X; ℤ)`.  Every internal presentation is indexed by the actual group
`H₂(X)` of its manifold; there is no global auxiliary homology group.
-/

namespace TwistedYetter.Kirby.Final

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.BoundaryStandardization
open TwistedYetter.Kirby.DependentRoleAwareFourManifoldInvariant
open TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget
open TwistedYetter.Kirby.RoleAwarePresentationEvaluation
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation

universe uK uC vC uX

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-! ## Classical smooth-manifold and homology boundary -/

/-- The externally supplied type of closed oriented smooth four-manifolds. -/
axiom ClosedOrientedSmoothFourManifold : Type uX

/-- Integral second homology, separately for every manifold. -/
axiom H₂ :
  ClosedOrientedSmoothFourManifold → AddCommGrpCat.{uX}

/-- Orientation-preserving diffeomorphisms form a groupoid. -/
axiom orientedDiffeomorphism :
  OrientedDiffeomorphismGroupoid.{uX, uX}
    ClosedOrientedSmoothFourManifold

/-- The induced additive equivalence on integral second homology. -/
axiom inducedH₂
    {X Y : ClosedOrientedSmoothFourManifold} :
    orientedDiffeomorphism.Hom X Y →
      H₂ X ≃+ H₂ Y

/-- The identity diffeomorphism induces the identity map on `H₂`. -/
axiom inducedH₂_identity
    (X : ClosedOrientedSmoothFourManifold) :
    inducedH₂ (orientedDiffeomorphism.identity X) =
      AddEquiv.refl (H₂ X)

/-- Induced maps on `H₂` respect composition. -/
axiom inducedH₂_compose
    {X Y Z : ClosedOrientedSmoothFourManifold}
    (first : orientedDiffeomorphism.Hom X Y)
    (second : orientedDiffeomorphism.Hom Y Z) :
    inducedH₂ (orientedDiffeomorphism.compose first second) =
      (inducedH₂ (X := X) (Y := Y) first).trans
        (inducedH₂ (X := Y) (Y := Z) second)

/-- The manifold/homology data used by the dependent descent theorem. -/
abbrev fourManifoldGeometry :
    HomologicalFourManifoldTheory.{uX, uX, uX} where
  FourManifold := ClosedOrientedSmoothFourManifold
  SecondHomology := fun X => H₂ X
  secondHomologyAddCommGroup := fun _ => inferInstance
  orientedDiffeomorphism := orientedDiffeomorphism
  homologyMap := inducedH₂
  homologyMap_identity := inducedH₂_identity
  homologyMap_compose := inducedH₂_compose

/-- The intrinsic pair `⟨X, α⟩`. -/
abbrev HomologicalFourManifold :=
  Σ X : ClosedOrientedSmoothFourManifold, H₂ X

/-! ## Dependent special-Kirby topology boundary -/

namespace SpecialKirbyHandleTheory

namespace Axioms

/--
The category-neutral assertion that a certified role-aware diagram realizes
the named manifold.  It contains no evaluator or scalar equality.
-/
axiom Realizes
    (X : ClosedOrientedSmoothFourManifold)
    (presentation : Presentation (H₂ X)) :
    Prop

/-- Every closed oriented smooth four-manifold has such a presentation. -/
axiom presentationExists
    (X : ClosedOrientedSmoothFourManifold) :
    Nonempty
      {presentation : Presentation (H₂ X) //
        Realizes X presentation}

/--
Marked Kirby--Cerf completeness after reindexing by the induced map on `H₂`.

The result is an explicit finite movie of the eight certified local moves.
-/
axiom kirbyCerfMovie
    {X Y : ClosedOrientedSmoothFourManifold}
    (f : orientedDiffeomorphism.Hom X Y)
    (source : {presentation : Presentation (H₂ X) //
      Realizes X presentation})
    (target : {presentation : Presentation (H₂ Y) //
      Realizes Y presentation}) :
    Movie
      (RoleAwarePresentationReindexing.reindex (inducedH₂ f) source.1)
      target.1

/--
The explicit movie transports the source marking to the target marking.

This is a topology/homology statement only.  It cannot assert equality of
category evaluations.
-/
axiom kirbyCerfMovie_transports_marking
    {X Y : ClosedOrientedSmoothFourManifold}
    (f : orientedDiffeomorphism.Hom X Y)
    (source : {presentation : Presentation (H₂ X) //
      Realizes X presentation})
    (target : {presentation : Presentation (H₂ Y) //
      Realizes Y presentation})
    (alpha : H₂ X) :
    (kirbyCerfMovie f source target).transport
        (source.1.canonicalPresentation.topology.h2ModelEquiv.symm alpha) =
      target.1.canonicalPresentation.topology.h2ModelEquiv.symm
        (inducedH₂ f alpha)

end Axioms

/-- Assemble the four visible topology inputs into the dependent boundary. -/
noncomputable def topologyBoundary :
    TopologyBoundary fourManifoldGeometry where
  Realizes := Axioms.Realizes
  presentationExists := Axioms.presentationExists
  movie := Axioms.kirbyCerfMovie
  movie_transports_marking :=
    Axioms.kirbyCerfMovie_transports_marking

end SpecialKirbyHandleTheory

/-! ## Public algebraic and manifold inputs -/

/-- The intrinsic pair `⟨𝒞, η⟩` for a premodular fusion category. -/
abbrev TwistedPremodularCategory :=
  Σ 𝒞 : PremodularFusionCategory (K := K) (C := C) (S := S),
    TensorIdentityAutomorphism C

/-- The modular subcase, retained only for specialization. -/
abbrev TwistedModularCategory :=
  Σ 𝒞 : ModularFusionCategory (K := K) (C := C) (S := S),
    TensorIdentityAutomorphism C

namespace TwistedModularCategory

/-- Forget S-matrix nondegeneracy and retain all ribbon-fusion data. -/
def toPremodular
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S)) :
    TwistedPremodularCategory (K := K) (C := C) (S := S) :=
  ⟨𝒞η.1.premodular, 𝒞η.2⟩

end TwistedModularCategory

/-- One certified special Kirby presentation of the manifold in `Xα`. -/
abbrev SpecialKirbyPresentation
    (Xα : HomologicalFourManifold.{uX}) :=
  SpecialKirbyHandleTheory.topologyBoundary.AdmissiblePresentation Xα.1

/-- Every intrinsic pair has at least one certified special presentation. -/
theorem specialKirbyPresentationExists
    (Xα : HomologicalFourManifold.{uX}) :
    Nonempty (SpecialKirbyPresentation Xα) :=
  SpecialKirbyHandleTheory.Axioms.presentationExists Xα.1

/-- Evaluate one accepted presentation with the displayed class `α`. -/
noncomputable def specialKirbyEvaluation
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    {Xα : HomologicalFourManifold.{uX}}
    (presentation : SpecialKirbyPresentation Xα) : K :=
  roleAwareEvalH2 𝒞η.1 𝒞η.2 presentation.1
    (presentation.1.canonicalPresentation.topology.h2ModelEquiv.symm Xα.2)

/-- The homologically twisted Yetter invariant. -/
noncomputable def TwistedYetter
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    (Xα : HomologicalFourManifold.{uX}) : K :=
  SpecialKirbyHandleTheory.topologyBoundary.evaluate
    𝒞η.1 𝒞η.2 Xα.1 Xα.2

/-- The invariant agrees with every accepted special presentation. -/
theorem TwistedYetter_on_specialKirbyPresentation
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    {Xα : HomologicalFourManifold.{uX}}
    (presentation : SpecialKirbyPresentation Xα) :
    TwistedYetter 𝒞η Xα =
      specialKirbyEvaluation 𝒞η presentation := by
  exact
    SpecialKirbyHandleTheory.topologyBoundary
      |>.evaluate_eq_admissiblePresentation
        𝒞η.1 𝒞η.2 Xα.1 Xα.2 presentation

/-- Diffeomorphism invariance with the class transported on actual `H₂`. -/
theorem TwistedYetter_diffeomorphism_invariant
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    {X Y : ClosedOrientedSmoothFourManifold.{uX}}
    (f : orientedDiffeomorphism.Hom X Y)
    (alpha : H₂ X) :
    TwistedYetter 𝒞η ⟨X, alpha⟩ =
      TwistedYetter 𝒞η ⟨Y, inducedH₂ f alpha⟩ :=
  SpecialKirbyHandleTheory.topologyBoundary
    |>.evaluate_diffeomorphism_invariant 𝒞η.1 𝒞η.2 f alpha

/-- Modular evaluation is the premodular invariant after specialization. -/
noncomputable def TwistedYetterModular
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S))
    (Xα : HomologicalFourManifold.{uX}) : K :=
  TwistedYetter 𝒞η.toPremodular Xα

/-- Modular invariance uses no proof beyond premodular specialization. -/
theorem TwistedYetterModular_diffeomorphism_invariant
    (𝒞η : TwistedModularCategory (K := K) (C := C) (S := S))
    {X Y : ClosedOrientedSmoothFourManifold.{uX}}
    (f : orientedDiffeomorphism.Hom X Y)
    (alpha : H₂ X) :
    TwistedYetterModular 𝒞η ⟨X, alpha⟩ =
      TwistedYetterModular 𝒞η ⟨Y, inducedH₂ f alpha⟩ :=
  TwistedYetter_diffeomorphism_invariant 𝒞η.toPremodular f alpha

namespace TwistedYetter

/-- An optional executable presentation-level implementation. -/
class Computable
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S)) where
  compute :
    {Xα : HomologicalFourManifold.{uX}} →
      SpecialKirbyPresentation Xα → K
  correct :
    {Xα : HomologicalFourManifold.{uX}} →
      (presentation : SpecialKirbyPresentation Xα) →
        TwistedYetter 𝒞η Xα = compute presentation

/-- Execute the installed implementation on one certified presentation. -/
def compute
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    [implementation : Computable 𝒞η]
    {Xα : HomologicalFourManifold.{uX}}
    (presentation : SpecialKirbyPresentation Xα) : K :=
  implementation.compute presentation

/-- The correctness theorem supplied by the executable implementation. -/
theorem compute_correct
    (𝒞η : TwistedPremodularCategory (K := K) (C := C) (S := S))
    [implementation : Computable 𝒞η]
    {Xα : HomologicalFourManifold.{uX}}
    (presentation : SpecialKirbyPresentation Xα) :
    TwistedYetter 𝒞η Xα =
      compute 𝒞η presentation :=
  implementation.correct presentation

end TwistedYetter

end

end TwistedYetter.Kirby.Final
