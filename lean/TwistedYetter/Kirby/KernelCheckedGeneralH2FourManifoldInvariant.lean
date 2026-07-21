import TwistedYetter.Kirby.GeneralH2MarkedKirbyInvariance
import TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler
import TwistedYetter.Kirby.LiteratureBackedFourManifoldTopology

/-!
# Arbitrary-H2 four-manifold descent from checked local moves

This is the fail-closed replacement for the former `Completion` route.
An elementary move contains an actual kernel-checked eight-case graphical
certificate and topology-only representative compatibility.  The final
theorem therefore does not accept a function claiming that every raw window
can be compiled.

The only remaining external boundary in this file is the standard marked
smooth-topology package: realization, geometric soundness, presentation
existence, and marked Kirby--Cerf completeness.  Those fields contain no
category evaluator and no equality in the scalar field.
-/

namespace TwistedYetter.Kirby.KernelCheckedGeneralH2FourManifoldInvariant

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CancellationSafeH2Representative
open TwistedYetter.Kirby.GeneralH2MarkedKirbyInvariance
open TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LiteratureBackedFourManifoldTopology
open TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget

universe uK uC vC uH uX uXHom

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
One admitted elementary move.

The first field is checked graphical syntax.  The second field says that the
actual source and target cycles are related by that same move and that a
death does not delete a hidden marked coefficient.  Neither field can store
the desired scalar equality.
-/
structure CertifiedMarkedMove
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {alpha : H2}
    (source target : AdmissiblePresentation manifold H2 alpha) where
  certificate :
    CertifiedMove 𝒞 automorphism
      source.state.presentation target.state.presentation
  compatibility :
    CancellationSafeStep certificate.compile
      source.state.representative target.state.representative

/-- The exact proof-carrying presentation calculus used by the final route. -/
noncomputable def presentationTheory
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (alpha : H2) :
    HandlePresentationTheory where
  Presentation := AdmissiblePresentation manifold H2 alpha
  Marking := fun _ => PUnit
  ElementaryMove := fun source target =>
    CertifiedMarkedMove 𝒞 automorphism source target
  transport := fun _ _ => PUnit.unit

/-- The explicit link evaluation attached to one certified presentation. -/
noncomputable def presentationEvaluation
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (alpha : H2) :
    PresentationEvaluation
      (presentationTheory 𝒞 automorphism manifold H2 alpha) K where
  value := fun presentation _ => presentation.value 𝒞 automorphism

/-- Every accepted elementary move preserves the explicit evaluation. -/
theorem presentationEvaluation_localInvariant
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (alpha : H2) :
    IsInvariantUnderElementaryMoves
      (presentationEvaluation 𝒞 automorphism manifold H2 alpha) := by
  intro source target move _
  exact eval_sound move.certificate.compile
    source.state.representative target.state.representative
    move.compatibility

/--
The smooth-topology boundary for this exact proof-carrying presentation
theory.  It is category-free in mathematical content even though the type of
an elementary certificate records which graphical laws were checked.
-/
abbrev TopologyInput
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (alpha : H2) :=
  Assumptions.{_, _, _, uX, uXHom}
    (presentationTheory 𝒞 automorphism manifold H2 alpha)

/-- The resulting scalar on marked closed oriented smooth four-manifolds. -/
noncomputable def EvalC
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (alpha : H2)
    (topology :
      TopologyInput.{uK, uC, vC, uH, uX, uXHom}
        𝒞 automorphism manifold H2 alpha) :
    topology.realization.MarkedClosedOrientedSmoothFourManifold → K :=
  topology.fourManifoldInvariant
    (presentationEvaluation 𝒞 automorphism manifold H2 alpha)
    (presentationEvaluation_localInvariant
      𝒞 automorphism manifold H2 alpha)

/-- The checked evaluator is invariant under oriented diffeomorphism. -/
theorem EvalC_diffeomorphism_invariant
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (alpha : H2)
    (topology :
      TopologyInput.{uK, uC, vC, uH, uX, uXHom}
        𝒞 automorphism manifold H2 alpha)
    {left right :
      topology.realization.MarkedClosedOrientedSmoothFourManifold}
    (diffeomorphism :
      topology.realization.orientedDiffeomorphism.Hom left right) :
    EvalC 𝒞 automorphism manifold H2 alpha topology left =
      EvalC 𝒞 automorphism manifold H2 alpha topology right :=
  topology.fourManifoldInvariant_diffeomorphism_invariant
    (presentationEvaluation 𝒞 automorphism manifold H2 alpha)
    (presentationEvaluation_localInvariant
      𝒞 automorphism manifold H2 alpha)
    diffeomorphism

/-- Pullback to an admitted presentation is the explicit link formula. -/
theorem EvalC_on_presentation
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (alpha : H2)
    (topology :
      TopologyInput.{uK, uC, vC, uH, uX, uXHom}
        𝒞 automorphism manifold H2 alpha)
    (presentation : AdmissiblePresentation manifold H2 alpha) :
    EvalC 𝒞 automorphism manifold H2 alpha topology
        (topology.realization.realize
          { presentation := presentation, marking := PUnit.unit }) =
      presentation.value 𝒞 automorphism :=
  topology.fourManifoldInvariant_on_presentation
    (presentationEvaluation 𝒞 automorphism manifold H2 alpha)
    (presentationEvaluation_localInvariant
      𝒞 automorphism manifold H2 alpha)
    { presentation := presentation, marking := PUnit.unit }

end TwistedYetter.Kirby.KernelCheckedGeneralH2FourManifoldInvariant
