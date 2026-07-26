import TwistedYetter.Kirby.RoleAwarePremodularEvaluator
import TwistedYetter.Kirby.ModularDottedEncircling

/-!
# Modular calibration of the role-aware evaluator

This file proves the local and contextual part of compatibility with the old
modular evaluator.  At a special dotted node, the legacy modular
Kirby-coloured encircling is exactly the normalized tensor-unit projector.
The equality is then propagated recursively through every role-aware
composition and tensor context.
-/

namespace TwistedYetter.Kirby.RoleAwareModularCalibration

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.ModularDottedEncircling
open TwistedYetter.Kirby.ModularVacuumProjector
open TwistedYetter.Kirby.RoleAwareComponentDiagram
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator.CanonicalPresentation
open TwistedYetter.Kirby.SimultaneousDottedCutGeometry
open TwistedYetter.Kirby.LinearDiagram

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

namespace RoleAwareDiagram

/--
Interpret a special node by the old modular Kirby-coloured open encircling.

The ordinary nodes are unchanged.  This is the old local semantics after the
finite sum over each dotted label has been collected into its open operator.
-/
noncomputable def interpretLegacyModular
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S) :
    {source target : ComponentBoundary} →
      RoleAwareDiagram source target →
        Diagram C
          (source.interpret 𝒞.premodular labelOf)
          (target.interpret 𝒞.premodular labelOf)
  | _, _, .ordinary diagram =>
      diagram.interpret 𝒞.premodular labelOf
  | _, _, .specialDottedCut dottedId punctureBoundary =>
      Diagram.coupon
        ("legacy-modular-kirby-encircling:" ++ dottedId)
        (openKirbyEncirclingOperator 𝒞.premodular
          (punctureBoundary.interpret
            𝒞.premodular labelOf).denote)
  | _, _, .characterPower boundary exponent =>
      Diagram.coupon "tensor-automorphism-power"
        (automorphismObjectPower η
          (boundary.interpret 𝒞.premodular labelOf).denote exponent)
  | _, _, .comp first second =>
      interpretLegacyModular 𝒞 η labelOf first ≫ᵈ
        interpretLegacyModular 𝒞 η labelOf second
  | _, _, .tensor left right =>
      interpretLegacyModular 𝒞 η labelOf left ⊗ᵈ
        interpretLegacyModular 𝒞 η labelOf right

/-- One special node is calibrated by the open modular killing theorem. -/
theorem specialDottedCut_eval_eq_legacy
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (dottedId : String)
    (punctureBoundary : ComponentBoundary) :
    Diagram.eval C
        ((RoleAwareDiagram.specialDottedCut
          dottedId punctureBoundary).interpret
            𝒞.premodular η labelOf) =
      Diagram.eval C
        (interpretLegacyModular 𝒞 η labelOf
          (RoleAwareDiagram.specialDottedCut
            dottedId punctureBoundary)) := by
  change
    PremodularDottedCutting.specialDottedCutOperator
        𝒞.premodular
        (punctureBoundary.interpret
          𝒞.premodular labelOf).denote =
      openKirbyEncirclingOperator 𝒞.premodular
        (punctureBoundary.interpret
          𝒞.premodular labelOf).denote
  exact
    (baerenzBarrett_tham_openKirbyKilling 𝒞
      (punctureBoundary.interpret
        𝒞.premodular labelOf).denote).symm

/--
Nodewise modular calibration is stable under every composition and tensor
context in the role-aware syntax.
-/
theorem interpret_eval_eq_legacy
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    {source target : ComponentBoundary}
    (diagram : RoleAwareDiagram source target) :
    Diagram.eval C (diagram.interpret 𝒞.premodular η labelOf) =
      Diagram.eval C (interpretLegacyModular 𝒞 η labelOf diagram) := by
  induction diagram with
  | ordinary diagram =>
      rfl
  | specialDottedCut dottedId punctureBoundary =>
      exact specialDottedCut_eval_eq_legacy
        𝒞 η labelOf dottedId punctureBoundary
  | characterPower boundary exponent =>
      rfl
  | comp first second firstIH secondIH =>
      simp only [RoleAwareDiagram.interpret,
        interpretLegacyModular, Diagram.eval]
      rw [firstIH, secondIH]
  | tensor left right leftIH rightIH =>
      simp only [RoleAwareDiagram.interpret,
        interpretLegacyModular, Diagram.eval]
      rw [leftIH, rightIH]

end RoleAwareDiagram

namespace CanonicalPresentation

/-- One old modular term after all dotted-label sums have been collected. -/
noncomputable def legacyCollapsedTermDiagram
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation :
      CanonicalModularKirbyEvaluator.CanonicalPresentation H2)
    (geometry : Geometry presentation)
    (labeling : OrdinaryLabeling (S := S) presentation) :
    Diagram C .unit .unit :=
  RoleAwareDiagram.interpretLegacyModular 𝒞 η
    (roleAwareLabelOf 𝒞.premodular presentation labeling)
    geometry.cutDiagram

/-- The ordinary-label sum of the collected legacy modular terms. -/
noncomputable def legacyCollapsedLinearDiagram
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation :
      CanonicalModularKirbyEvaluator.CanonicalPresentation H2)
    (geometry : Geometry presentation)
    (cycle : presentation.DegreeTwoCycle) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum
    (roleAwareGlobalWeight 𝒞.premodular η presentation cycle)
    (legacyCollapsedTermDiagram 𝒞 η presentation geometry)

/--
The complete ordinary-label role-aware sum equals the collected legacy
modular sum.

No finite dotted-label Fubini theorem is hidden here: the right side is
explicitly named `legacyCollapsedLinearDiagram`.
-/
theorem roleAwareLinearDiagram_eval_eq_legacyCollapsed
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (presentation :
      CanonicalModularKirbyEvaluator.CanonicalPresentation H2)
    (geometry : Geometry presentation)
    (cycle : presentation.DegreeTwoCycle) :
    LinearDiagram.eval
        (roleAwareLinearDiagram
          𝒞.premodular η presentation geometry cycle) =
      LinearDiagram.eval
        (legacyCollapsedLinearDiagram
          𝒞 η presentation geometry cycle) := by
  classical
  simp only [roleAwareLinearDiagram,
    legacyCollapsedLinearDiagram, eval_weightedSum]
  apply Finset.sum_congr rfl
  intro labeling _
  apply congrArg
  exact RoleAwareDiagram.interpret_eval_eq_legacy
    𝒞 η (roleAwareLabelOf 𝒞.premodular presentation labeling)
      geometry.cutDiagram

end CanonicalPresentation

end TwistedYetter.Kirby.RoleAwareModularCalibration
