import TwistedYetter.Kirby.CanonicalModularKirbyInvariance
import TwistedYetter.Kirby.LiteratureBackedHomologicalFourManifoldTopology

/-!
# Public modular closed four-manifold invariant

This is the single public entry point for the current modular route.

The four layers remain deliberately distinct:

1. `PresentationEvalC` is the explicit Kirby-presentation formula.
2. `HomologicalFourManifoldTopologyBoundary` identifies handle-chain `H₂`
   with the actual `H₂` of an underlying closed oriented smooth
   four-manifold.
3. `EvalC` is the resulting noncomputable function of exactly
   `(X, alpha : H₂(X; ℤ))`.
4. `EvalC_on_presentation` proves that the abstract descent agrees with the
   explicit presentation formula, so computation never needs to choose a
   manifold presentation noncomputably.

The external smooth-topology and graphical inputs are listed by
`ModularClosedFourManifoldInvariantAxiomAudit`.
-/

namespace TwistedYetter.Kirby.Final.ModularClosedFourManifoldInvariant

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalModularKirbyInvariance
open TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry
open TwistedYetter.Kirby.LiteratureBackedHomologicalFourManifoldTopology

universe uK uC vC uAuxH2 uX uH uD

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- The public type of closed oriented smooth four-manifolds and their `H₂`. -/
abbrev FourManifoldGeometry :=
  HomologicalFourManifoldTheory

/-- The explicit formula on one marked Kirby presentation. -/
noncomputable abbrev PresentationEvalC
    {auxiliaryH2 : Type uAuxH2} [AddCommGroup auxiliaryH2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C) :=
  presentationEvaluation 𝒞 automorphism auxiliaryH2

/--
Construct the genuine homological four-manifold invariant from the explicit
presentation formula and the category-neutral topology boundary.

`calculus` and `auxiliaryH2` index the concrete implementation of
the handle-presentation calculus.  They are discharged by this construction;
the resulting invariant accepts only `X` and `alpha : H₂(X; ℤ)`.
-/
noncomputable def constructEvalC
    {auxiliaryH2 : Type uAuxH2} [AddCommGroup auxiliaryH2]
    {geometry : FourManifoldGeometry.{uX, uH, uD}}
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (fourManifoldTopology :
      HomologicalFourManifoldTopologyBoundary
        (handlePresentationTheory auxiliaryH2)
        geometry) :
    HomologicalFourManifoldInvariant geometry K :=
  fourManifoldTopology.constructInvariant
    (presentationEvaluation
      𝒞 automorphism auxiliaryH2)
    (evalC_local_move_invariant 𝒞 automorphism)

/--
The public scalar.  After the category and topology boundary are fixed, its
only mathematical inputs are a manifold `X` and a class `alpha : H₂(X; ℤ)`.
-/
noncomputable def EvalC
    {auxiliaryH2 : Type uAuxH2} [AddCommGroup auxiliaryH2]
    {geometry : FourManifoldGeometry.{uX, uH, uD}}
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (fourManifoldTopology :
      HomologicalFourManifoldTopologyBoundary
        (handlePresentationTheory auxiliaryH2)
        geometry)
    (X : geometry.FourManifold)
    (alpha : geometry.SecondHomology X) : K :=
  (constructEvalC 𝒞 automorphism fourManifoldTopology).EvalC X alpha

/--
`EvalC` is invariant under oriented diffeomorphism, with the homology class
transported by the induced map on actual manifold `H₂`.
-/
theorem EvalC_diffeomorphism_invariant
    {auxiliaryH2 : Type uAuxH2} [AddCommGroup auxiliaryH2]
    {geometry : FourManifoldGeometry.{uX, uH, uD}}
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (fourManifoldTopology :
      HomologicalFourManifoldTopologyBoundary
        (handlePresentationTheory auxiliaryH2)
        geometry)
    {X Y : geometry.FourManifold}
    (f :
      geometry.orientedDiffeomorphism.Hom X Y)
    (alpha : geometry.SecondHomology X) :
    EvalC 𝒞 automorphism fourManifoldTopology X alpha =
      EvalC 𝒞 automorphism fourManifoldTopology Y
        (geometry.homologyMap f alpha) :=
  (constructEvalC 𝒞 automorphism fourManifoldTopology)
    |>.diffeomorphismInvariant f alpha

/--
On a supplied marked Kirby presentation, the manifold-level invariant is the
explicit presentation formula.
-/
theorem EvalC_on_presentation
    {auxiliaryH2 : Type uAuxH2} [AddCommGroup auxiliaryH2]
    {geometry : FourManifoldGeometry.{uX, uH, uD}}
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (fourManifoldTopology :
      HomologicalFourManifoldTopologyBoundary
        (handlePresentationTheory auxiliaryH2)
        geometry)
    (presentation :
      StandardDottedCanonicalPresentation auxiliaryH2)
    (alpha :
      presentation.canonicalPresentation.topology.handleChain.SecondHomology) :
    EvalC 𝒞 automorphism fourManifoldTopology
        (fourManifoldTopology.realization.underlyingManifold presentation)
        (fourManifoldTopology.realization.secondHomologyEquiv
          presentation alpha) =
      presentation.canonicalPresentation.EvalC 𝒞 automorphism alpha :=
  fourManifoldTopology.constructInvariant_on_presentation
    (presentationEvaluation
      𝒞 automorphism auxiliaryH2)
    (evalC_local_move_invariant 𝒞 automorphism)
    ⟨presentation, alpha⟩

end TwistedYetter.Kirby.Final.ModularClosedFourManifoldInvariant
