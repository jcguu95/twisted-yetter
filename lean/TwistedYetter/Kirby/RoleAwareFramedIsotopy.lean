import TwistedYetter.Kirby.RoleAwareSameComponentTransport

/-!
# Framed isotopy for the role-aware evaluator

The topology certificate below contains only component/exponent transport and
a generated isotopy of the free role-aware diagrams.  Evaluation equality is
derived for every premodular category.
-/

namespace TwistedYetter.Kirby.RoleAwareFramedIsotopy

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.RoleAwareComponentDiagram
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwareSameComponentTransport
open TwistedYetter.Kirby.SimultaneousDottedCutGeometry
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Category-neutral source-bound geometry of one framed isotopy. -/
structure Geometry
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2) where
  sourceGeometry : SimultaneousDottedCutGeometry.Geometry source
  targetGeometry : SimultaneousDottedCutGeometry.Geometry target
  componentChange :
    SameComponentIndexChange
      source.topology.formal target.topology.formal
  cut_isotopy :
    RoleAwareDiagram.GeneratedIsotopy
      sourceGeometry.cutDiagram targetGeometry.cutDiagram

namespace Geometry

/-- A source-bound framed isotopy preserves the complete normalized value. -/
theorem roleAwareCycleEval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (transport :
      KirbyCompleteness.MarkedH2Transport
        source.topology target.topology)
    (geometry : Geometry source target)
    (exponentTransport :
      (sourceCycle : source.DegreeTwoCycle) →
        SameComponentCycleExponentTransport source target
          geometry.componentChange sourceCycle
          ((CycleTransport.ofMarkedH2Transport source target transport)
            |>.targetCycle sourceCycle))
    (countsSound : source.topology.counts = target.topology.counts)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) :
    CanonicalPresentation.roleAwareCycleEval
        𝒞 η source geometry.sourceGeometry sourceCycle =
      CanonicalPresentation.roleAwareCycleEval
        𝒞 η target geometry.targetGeometry
        ((CycleTransport.ofMarkedH2Transport source target transport)
          |>.targetCycle sourceCycle) := by
  apply RoleAwareSameComponentTransport.roleAwareCycleEval_transport
    𝒞 η geometry.sourceGeometry geometry.targetGeometry countsSound
    geometry.componentChange
    (exponentTransport sourceCycle)
  intro sourceLabeling
  let targetLabeling :=
    OrdinaryTransport.ordinaryLabelingEquiv
      geometry.componentChange sourceLabeling
  have labelsEq :
      CanonicalPresentation.roleAwareLabelOf
          𝒞 target targetLabeling =
        CanonicalPresentation.roleAwareLabelOf
          𝒞 source sourceLabeling := by
    funext componentId
    exact roleAwareLabelOf_transport
      𝒞 source target geometry.componentChange sourceLabeling componentId
  unfold CanonicalPresentation.roleAwareTermDiagram
  rw [labelsEq]
  exact geometry.cut_isotopy.eval_eq
    𝒞 η (CanonicalPresentation.roleAwareLabelOf 𝒞 source sourceLabeling)

end Geometry

end TwistedYetter.Kirby.RoleAwareFramedIsotopy
