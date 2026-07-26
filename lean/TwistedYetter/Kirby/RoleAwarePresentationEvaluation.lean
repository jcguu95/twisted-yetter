import TwistedYetter.Kirby.RoleAwareRepresentativeIndependence

/-!
# The role-aware evaluator on handle-chain homology classes

This module performs the only representative choice used by the premodular
main line.  The preceding representative-independence theorem proves that the
result is independent of that choice.
-/

namespace TwistedYetter.Kirby.RoleAwarePresentationEvaluation

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwareRepresentativeIndependence
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- The role-aware premodular value of one handle-chain homology class. -/
noncomputable def roleAwareEvalH2
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : Presentation H2)
    (alpha :
      presentation.canonicalPresentation.topology.handleChain.SecondHomology) :
    K :=
  RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
    𝒞 η presentation.canonicalPresentation presentation.simultaneousGeometry
    (presentation.canonicalPresentation.chosenCycle alpha)

/--
Any explicit cycle representing `alpha` computes the same value as the
chosen-section definition above.
-/
theorem roleAwareCycleEval_eq_roleAwareEvalH2
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation : Presentation H2)
    (alpha :
      presentation.canonicalPresentation.topology.handleChain.SecondHomology)
    (cycle : presentation.canonicalPresentation.DegreeTwoCycle)
    (cycleClass :
      presentation.canonicalPresentation.topology.handleChain.complex.homologyπ
          2 cycle =
        alpha) :
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
        𝒞 η presentation.canonicalPresentation
        presentation.simultaneousGeometry cycle =
      roleAwareEvalH2 𝒞 η presentation alpha := by
  unfold roleAwareEvalH2
  apply
    Presentation.roleAwareCycleEval_respects_homology_class
      𝒞 η presentation
  exact cycleClass.trans
    (presentation.canonicalPresentation.chosenCycle_class alpha).symm

end TwistedYetter.Kirby.RoleAwarePresentationEvaluation
