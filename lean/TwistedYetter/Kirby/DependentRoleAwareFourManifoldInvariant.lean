import TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget
import TwistedYetter.Kirby.PremodularRoleAwareLocalInvariance
import TwistedYetter.Kirby.RoleAwarePresentationReindexing

/-!
# Dependent second-homology descent for the role-aware evaluator

Every manifold `X` uses presentations indexed by its own group `H₂(X)`.
No global auxiliary homology group occurs in this module.
-/

namespace TwistedYetter.Kirby.DependentRoleAwareFourManifoldInvariant

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.HomologicalFourManifoldInvariantFinalTarget
open TwistedYetter.Kirby.PremodularRoleAwareLocalInvariance
open TwistedYetter.Kirby.RoleAwarePresentationEvaluation
open TwistedYetter.Kirby.RoleAwarePresentationReindexing
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation
open TwistedYetter.Kirby.RoleAwareTableTwoMove

universe uK uC vC uH uX uD

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- A finite sequence of the eight role-aware elementary moves. -/
inductive Movie
    {H2 : Type uH} [AddCommGroup H2] :
    Presentation H2 → Presentation H2 → Type (uH + 1)
  | refl (presentation : Presentation H2) :
      Movie presentation presentation
  | step
      {source target : Presentation H2}
      (move : ElementaryMove source target) :
      Movie source target
  | trans
      {source middle target : Presentation H2}
      (first : Movie source middle)
      (second : Movie middle target) :
      Movie source target

namespace Movie

/-- The chain-derived transport carried by a finite movie. -/
noncomputable def transport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    (movie : Movie source target) :
    source.canonicalPresentation.topology.handleChain.SecondHomology ≃+
      target.canonicalPresentation.topology.handleChain.SecondHomology :=
  match movie with
  | .refl _ => AddEquiv.refl _
  | .step move => ElementaryMove.transport move
  | .trans first second => first.transport.trans second.transport

/-- The role-aware evaluation is unchanged along every finite movie. -/
theorem preserves_evaluation
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {source target : Presentation H2}
    (movie : Movie source target)
    (alpha :
      source.canonicalPresentation.topology.handleChain.SecondHomology) :
    roleAwareEvalH2 𝒞 η source alpha =
      roleAwareEvalH2 𝒞 η target (movie.transport alpha) := by
  induction movie with
  | refl =>
      rfl
  | step move =>
      exact elementaryMove_invariant 𝒞 η move alpha
  | trans first second firstIH secondIH =>
      exact (firstIH alpha).trans (secondIH (first.transport alpha))

end Movie

/--
The category-neutral topology boundary for dependent presentations.

The final field says that the movie's explicit chain transport agrees with
the map on actual second homology induced by the displayed diffeomorphism.
No field mentions a category, character, evaluator, or scalar equality.
-/
structure TopologyBoundary
    (geometry : HomologicalFourManifoldTheory.{uX, uH, uD}) where
  Realizes :
    (X : geometry.FourManifold) →
      Presentation (geometry.SecondHomology X) → Prop
  presentationExists :
    (X : geometry.FourManifold) →
      Nonempty
        {presentation : Presentation (geometry.SecondHomology X) //
          Realizes X presentation}
  movie :
    {X Y : geometry.FourManifold} →
    (f : geometry.orientedDiffeomorphism.Hom X Y) →
    (source :
      {presentation : Presentation (geometry.SecondHomology X) //
        Realizes X presentation}) →
    (target :
      {presentation : Presentation (geometry.SecondHomology Y) //
        Realizes Y presentation}) →
      Movie
        (reindex (geometry.homologyMap f) source.1)
        target.1
  movie_transports_marking :
    {X Y : geometry.FourManifold} →
    (f : geometry.orientedDiffeomorphism.Hom X Y) →
    (source :
      {presentation : Presentation (geometry.SecondHomology X) //
        Realizes X presentation}) →
    (target :
      {presentation : Presentation (geometry.SecondHomology Y) //
        Realizes Y presentation}) →
    (alpha : geometry.SecondHomology X) →
      (movie f source target).transport
          (source.1.canonicalPresentation.topology.h2ModelEquiv.symm alpha) =
        target.1.canonicalPresentation.topology.h2ModelEquiv.symm
          (geometry.homologyMap f alpha)

namespace TopologyBoundary

/-- A certified dependent presentation of `X`. -/
abbrev AdmissiblePresentation
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (topology : TopologyBoundary geometry)
    (X : geometry.FourManifold) :=
  {presentation : Presentation (geometry.SecondHomology X) //
    topology.Realizes X presentation}

/-- Noncomputably select one certified presentation of `X`. -/
noncomputable def chosenPresentation
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (topology : TopologyBoundary geometry)
    (X : geometry.FourManifold) :
    topology.AdmissiblePresentation X :=
  Classical.choice (topology.presentationExists X)

/-- Evaluate one intrinsic pair `(X, α)` using a chosen dependent presentation. -/
noncomputable def evaluate
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (topology : TopologyBoundary geometry)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (X : geometry.FourManifold)
    (alpha : geometry.SecondHomology X) : K :=
  let presentation := topology.chosenPresentation X
  roleAwareEvalH2 𝒞 η presentation.1
    (presentation.1.canonicalPresentation.topology.h2ModelEquiv.symm alpha)

/-- The chosen value agrees with every certified presentation of `(X, α)`. -/
theorem evaluate_eq_admissiblePresentation
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (topology : TopologyBoundary geometry)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (X : geometry.FourManifold)
    (alpha : geometry.SecondHomology X)
    (target : topology.AdmissiblePresentation X) :
    topology.evaluate 𝒞 η X alpha =
      roleAwareEvalH2 𝒞 η target.1
        (target.1.canonicalPresentation.topology.h2ModelEquiv.symm alpha) := by
  let source := topology.chosenPresentation X
  let identity := geometry.orientedDiffeomorphism.identity X
  let sourceClass :=
    source.1.canonicalPresentation.topology.h2ModelEquiv.symm alpha
  calc
    topology.evaluate 𝒞 η X alpha =
        roleAwareEvalH2 𝒞 η source.1 sourceClass := rfl
    _ =
        roleAwareEvalH2 𝒞 η
          (reindex (geometry.homologyMap identity) source.1) sourceClass :=
      roleAwareEvalH2_reindex 𝒞 η
        (geometry.homologyMap identity) source.1 sourceClass
    _ =
        roleAwareEvalH2 𝒞 η target.1
          ((topology.movie identity source target).transport sourceClass) :=
      (topology.movie identity source target).preserves_evaluation
        𝒞 η sourceClass
    _ =
        roleAwareEvalH2 𝒞 η target.1
          (target.1.canonicalPresentation.topology.h2ModelEquiv.symm
            (geometry.homologyMap identity alpha)) := by
      rw [topology.movie_transports_marking identity source target alpha]
    _ =
        roleAwareEvalH2 𝒞 η target.1
          (target.1.canonicalPresentation.topology.h2ModelEquiv.symm alpha) := by
      have hMap :=
        DFunLike.congr_fun (geometry.homologyMap_identity X) alpha
      exact congrArg
        (fun beta =>
          roleAwareEvalH2 𝒞 η target.1
            (target.1.canonicalPresentation.topology.h2ModelEquiv.symm beta))
        hMap

/-- The dependent evaluation is invariant under oriented diffeomorphism. -/
theorem evaluate_diffeomorphism_invariant
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (topology : TopologyBoundary geometry)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {X Y : geometry.FourManifold}
    (f : geometry.orientedDiffeomorphism.Hom X Y)
    (alpha : geometry.SecondHomology X) :
    topology.evaluate 𝒞 η X alpha =
      topology.evaluate 𝒞 η Y (geometry.homologyMap f alpha) := by
  let source := topology.chosenPresentation X
  let target := topology.chosenPresentation Y
  let sourceClass :=
    source.1.canonicalPresentation.topology.h2ModelEquiv.symm alpha
  calc
    topology.evaluate 𝒞 η X alpha =
        roleAwareEvalH2 𝒞 η source.1 sourceClass := rfl
    _ =
        roleAwareEvalH2 𝒞 η
          (reindex (geometry.homologyMap f) source.1) sourceClass :=
      roleAwareEvalH2_reindex 𝒞 η (geometry.homologyMap f) source.1 sourceClass
    _ =
        roleAwareEvalH2 𝒞 η target.1
          ((topology.movie f source target).transport sourceClass) :=
      (topology.movie f source target).preserves_evaluation 𝒞 η sourceClass
    _ =
        roleAwareEvalH2 𝒞 η target.1
          (target.1.canonicalPresentation.topology.h2ModelEquiv.symm
            (geometry.homologyMap f alpha)) := by
      rw [topology.movie_transports_marking f source target alpha]
    _ = topology.evaluate 𝒞 η Y (geometry.homologyMap f alpha) := rfl

/-- Package the dependent evaluation as the paper-facing invariant structure. -/
noncomputable def constructInvariant
    {geometry : HomologicalFourManifoldTheory.{uX, uH, uD}}
    (topology : TopologyBoundary geometry)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C) :
    HomologicalFourManifoldInvariant geometry K where
  EvalC := topology.evaluate 𝒞 η
  diffeomorphismInvariant :=
    topology.evaluate_diffeomorphism_invariant 𝒞 η

end TopologyBoundary

end TwistedYetter.Kirby.DependentRoleAwareFourManifoldInvariant
