import TwistedYetter.Kirby.TensorAutomorphismCouponCalculus

/-!
# Duality laws for tensor-identity automorphisms

A negatively oriented puncture carries the selected right dual.  Its tensor
automorphism is not extra character data: monoidality, naturality of the
evaluation morphism, and rigidity force it to be the right mate of the
inverse component on the primal object.
-/

namespace TwistedYetter.Kirby.TensorAutomorphismDuality

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [RigidCategory C]

/-- The component on a selected right dual is the mate of the inverse. -/
theorem hom_app_rightDual
    (automorphism : TensorIdentityAutomorphism C)
    (X : C) :
    automorphism.iso.hom.app Xᘁ =
      (automorphism.iso.inv.app X)ᘁ := by
  letI : NatTrans.IsMonoidal automorphism.iso.hom :=
    automorphism.monoidal
  have unitLaw :
      automorphism.iso.hom.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
    simpa using
      (NatTrans.IsMonoidal.unit
        (τ := automorphism.iso.hom))
  have tensorLaw :
      automorphism.iso.hom.app (Xᘁ ⊗ X) =
        automorphism.iso.hom.app Xᘁ ⊗ₘ
          automorphism.iso.hom.app X := by
    simpa using
      (NatTrans.IsMonoidal.tensor
        (τ := automorphism.iso.hom) Xᘁ X)
  have evaluationNaturality :
      automorphism.iso.hom.app (Xᘁ ⊗ X) ≫ ε_ X Xᘁ =
        ε_ X Xᘁ := by
    simpa [unitLaw] using
      (automorphism.iso.hom.naturality (ε_ X Xᘁ)).symm
  have expandedNaturality :
      (automorphism.iso.hom.app Xᘁ ▷ X) ≫
          (Xᘁ ◁ automorphism.iso.hom.app X) ≫
          ε_ X Xᘁ =
        ε_ X Xᘁ := by
    have tensorEvaluation :
        (automorphism.iso.hom.app Xᘁ ⊗ₘ
            automorphism.iso.hom.app X) ≫ ε_ X Xᘁ =
          ε_ X Xᘁ := by
      rw [← tensorLaw]
      exact evaluationNaturality
    simpa [tensorHom_def, Category.assoc] using tensorEvaluation
  have dualEvaluation :
      (automorphism.iso.hom.app Xᘁ ▷ X) ≫ ε_ X Xᘁ =
        (Xᘁ ◁ automorphism.iso.inv.app X) ≫ ε_ X Xᘁ := by
    symm
    calc
      (Xᘁ ◁ automorphism.iso.inv.app X) ≫ ε_ X Xᘁ =
          (Xᘁ ◁ automorphism.iso.inv.app X) ≫
            ((automorphism.iso.hom.app Xᘁ ▷ X) ≫
              (Xᘁ ◁ automorphism.iso.hom.app X) ≫
                ε_ X Xᘁ) := by
        simpa [Category.assoc] using
          congrArg
            (fun f =>
              (Xᘁ ◁ automorphism.iso.inv.app X) ≫ f)
            expandedNaturality.symm
      _ = (Xᘁ ◁ automorphism.iso.inv.app X) ≫
            (automorphism.iso.hom.app Xᘁ ▷ X) ≫
            (Xᘁ ◁ automorphism.iso.hom.app X) ≫
            ε_ X Xᘁ := by
        simp only [Category.assoc]
      _ = (automorphism.iso.hom.app Xᘁ ▷ X) ≫
            (Xᘁ ◁ automorphism.iso.inv.app X) ≫
            (Xᘁ ◁ automorphism.iso.hom.app X) ≫
            ε_ X Xᘁ := by
        simpa [Category.assoc] using
          congrArg
            (fun f => f ≫
              (Xᘁ ◁ automorphism.iso.hom.app X) ≫
                ε_ X Xᘁ)
            (whisker_exchange
              (automorphism.iso.hom.app Xᘁ)
              (automorphism.iso.inv.app X))
      _ = (automorphism.iso.hom.app Xᘁ ▷ X) ≫
            (Xᘁ ◁
              (automorphism.iso.inv.app X ≫
                automorphism.iso.hom.app X)) ≫
            ε_ X Xᘁ := by
        simpa [Category.assoc] using
          congrArg
            (fun f =>
              (automorphism.iso.hom.app Xᘁ ▷ X) ≫
                f ≫ ε_ X Xᘁ)
            (MonoidalCategory.whiskerLeft_comp Xᘁ
              (automorphism.iso.inv.app X)
              (automorphism.iso.hom.app X)).symm
      _ = (automorphism.iso.hom.app Xᘁ ▷ X) ≫
            ε_ X Xᘁ := by
        have cancelWhisker :
            Xᘁ ◁
                (automorphism.iso.inv.app X ≫
                  automorphism.iso.hom.app X) =
              𝟙 (Xᘁ ⊗ X) := by
          rw [automorphism.iso.inv_hom_id_app]
          simp
        simpa [Category.assoc] using
          congrArg
            (fun f =>
              (automorphism.iso.hom.app Xᘁ ▷ X) ≫
                f ≫ ε_ X Xᘁ)
            cancelWhisker
  have mateEvaluation :
      ((automorphism.iso.inv.app X)ᘁ ▷ X) ≫ ε_ X Xᘁ =
        (Xᘁ ◁ automorphism.iso.inv.app X) ≫ ε_ X Xᘁ :=
    rightAdjointMate_comp_evaluation (automorphism.iso.inv.app X)
  have comparison :
      (automorphism.iso.hom.app Xᘁ ▷ X) ≫ ε_ X Xᘁ =
        ((automorphism.iso.inv.app X)ᘁ ▷ X) ≫ ε_ X Xᘁ :=
    dualEvaluation.trans mateEvaluation.symm
  let e := tensorRightHomEquiv Xᘁ X Xᘁ (𝟙_ C)
  have composed :
      automorphism.iso.hom.app Xᘁ ≫ (λ_ Xᘁ).inv =
        (automorphism.iso.inv.app X)ᘁ ≫ (λ_ Xᘁ).inv := by
    have leftRule :
        e ((automorphism.iso.hom.app Xᘁ ▷ X) ≫
            ε_ X Xᘁ) =
          automorphism.iso.hom.app Xᘁ ≫ (λ_ Xᘁ).inv :=
      tensorRightHomEquiv_whiskerRight_comp_evaluation
        (automorphism.iso.hom.app Xᘁ)
    have rightRule :
        e (((automorphism.iso.inv.app X)ᘁ ▷ X) ≫
            ε_ X Xᘁ) =
          (automorphism.iso.inv.app X)ᘁ ≫ (λ_ Xᘁ).inv :=
      tensorRightHomEquiv_whiskerRight_comp_evaluation
        ((automorphism.iso.inv.app X)ᘁ)
    exact leftRule.symm.trans ((congrArg e comparison).trans rightRule)
  exact (cancel_mono (λ_ Xᘁ).inv).mp composed

/-- Machine-visible status of the orientation/duality sign law. -/
def currentStatus : String :=
  "PASS_NEGATIVE_PUNCTURE_FORCED_TO_INVERSE_DUAL_COUPON"

end TwistedYetter.Kirby.TensorAutomorphismDuality
