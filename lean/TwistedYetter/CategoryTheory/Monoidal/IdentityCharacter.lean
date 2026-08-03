import TwistedYetter.CategoryTheory.Fusion.Dual

/-!
# Monoidal automorphisms of the tensor identity

This is the category-theoretic character used by Twisted Yetter.  It is
independent of Kirby diagrams and of any chosen finite semisimple coordinates.
-/

namespace CategoryTheory

open MonoidalCategory

universe v uK uC

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{v} C] [MonoidalCategory C]

/-- A monoidal natural automorphism of the identity functor. -/
structure TensorIdentityCharacter where
  iso : 𝟭 C ≅ 𝟭 C
  monoidal : NatTrans.IsMonoidal iso.hom

namespace TensorIdentityCharacter

theorem tensor_hom (character : TensorIdentityCharacter (C := C)) (X Y : C) :
    character.iso.hom.app (X ⊗ Y) =
      character.iso.hom.app X ⊗ₘ character.iso.hom.app Y := by
  letI : NatTrans.IsMonoidal character.iso.hom := character.monoidal
  simpa using NatTrans.IsMonoidal.tensor (τ := character.iso.hom) X Y

theorem unit_hom (character : TensorIdentityCharacter (C := C)) :
    character.iso.hom.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
  letI : NatTrans.IsMonoidal character.iso.hom := character.monoidal
  simpa using NatTrans.IsMonoidal.unit (τ := character.iso.hom)

theorem hom_app_rightDual
    [RigidCategory C] [RightRigidCategory C]
    (character : TensorIdentityCharacter (C := C)) (X : C) :
    character.iso.hom.app Xᘁ = (character.iso.inv.app X)ᘁ := by
  letI : NatTrans.IsMonoidal character.iso.hom := character.monoidal
  have unitLaw :
      character.iso.hom.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
    simpa using NatTrans.IsMonoidal.unit (τ := character.iso.hom)
  have tensorLaw :
      character.iso.hom.app (Xᘁ ⊗ X) =
        character.iso.hom.app Xᘁ ⊗ₘ character.iso.hom.app X := by
    simpa using NatTrans.IsMonoidal.tensor (τ := character.iso.hom) Xᘁ X
  have evaluationNaturality :
      character.iso.hom.app (Xᘁ ⊗ X) ≫ ε_ X Xᘁ = ε_ X Xᘁ := by
    simpa [unitLaw] using (character.iso.hom.naturality (ε_ X Xᘁ)).symm
  have expandedNaturality :
      (character.iso.hom.app Xᘁ ▷ X) ≫
          (Xᘁ ◁ character.iso.hom.app X) ≫ ε_ X Xᘁ = ε_ X Xᘁ := by
    have tensorEvaluation :
        (character.iso.hom.app Xᘁ ⊗ₘ character.iso.hom.app X) ≫ ε_ X Xᘁ =
          ε_ X Xᘁ := by
      rw [← tensorLaw]
      exact evaluationNaturality
    rw [MonoidalCategory.tensorHom_def] at tensorEvaluation
    simpa only [Category.assoc] using tensorEvaluation
  have dualEvaluation :
      (character.iso.hom.app Xᘁ ▷ X) ≫ ε_ X Xᘁ =
        (Xᘁ ◁ character.iso.inv.app X) ≫ ε_ X Xᘁ := by
    symm
    calc
      (Xᘁ ◁ character.iso.inv.app X) ≫ ε_ X Xᘁ =
          (Xᘁ ◁ character.iso.inv.app X) ≫
            ((character.iso.hom.app Xᘁ ▷ X) ≫
              (Xᘁ ◁ character.iso.hom.app X) ≫ ε_ X Xᘁ) := by
        simpa [Category.assoc] using congrArg
          (fun f => (Xᘁ ◁ character.iso.inv.app X) ≫ f)
          expandedNaturality.symm
      _ = (Xᘁ ◁ character.iso.inv.app X) ≫
            (character.iso.hom.app Xᘁ ▷ X) ≫
            (Xᘁ ◁ character.iso.hom.app X) ≫ ε_ X Xᘁ := by
        rfl
      _ = (character.iso.hom.app Xᘁ ▷ X) ≫
            (Xᘁ ◁ character.iso.inv.app X) ≫
            (Xᘁ ◁ character.iso.hom.app X) ≫ ε_ X Xᘁ := by
        simpa [Category.assoc] using congrArg
          (fun f => f ≫ (Xᘁ ◁ character.iso.hom.app X) ≫ ε_ X Xᘁ)
          (whisker_exchange
            (character.iso.hom.app Xᘁ) (character.iso.inv.app X))
      _ = (character.iso.hom.app Xᘁ ▷ X) ≫
            (Xᘁ ◁ (character.iso.inv.app X ≫ character.iso.hom.app X)) ≫
            ε_ X Xᘁ := by
        simp [Category.assoc]
      _ = (character.iso.hom.app Xᘁ ▷ X) ≫ ε_ X Xᘁ := by
        have cancelWhisker :
            Xᘁ ◁ (character.iso.inv.app X ≫ character.iso.hom.app X) =
              𝟙 (Xᘁ ⊗ X) := by
          rw [character.iso.inv_hom_id_app]
          simp
        simpa [Category.assoc] using congrArg
          (fun f => (character.iso.hom.app Xᘁ ▷ X) ≫ f ≫ ε_ X Xᘁ)
          cancelWhisker
  let inverseMate : Xᘁ ⟶ Xᘁ := rightAdjointMate (character.iso.inv.app X)
  have mateEvaluation :
      (inverseMate ▷ X) ≫ ε_ X Xᘁ =
        (Xᘁ ◁ character.iso.inv.app X) ≫ ε_ X Xᘁ :=
    rightAdjointMate_comp_evaluation (character.iso.inv.app X)
  have comparison :
      (character.iso.hom.app Xᘁ ▷ X) ≫ ε_ X Xᘁ =
        (inverseMate ▷ X) ≫ ε_ X Xᘁ :=
    dualEvaluation.trans mateEvaluation.symm
  let e := tensorRightHomEquiv Xᘁ X Xᘁ (𝟙_ C)
  have composed :
      character.iso.hom.app Xᘁ ≫ (λ_ Xᘁ).inv =
        inverseMate ≫ (λ_ Xᘁ).inv := by
    have leftRule :
        e ((character.iso.hom.app Xᘁ ▷ X) ≫ ε_ X Xᘁ) =
          character.iso.hom.app Xᘁ ≫ (λ_ Xᘁ).inv :=
      tensorRightHomEquiv_whiskerRight_comp_evaluation
        (character.iso.hom.app Xᘁ)
    have rightRule :
        e ((inverseMate ▷ X) ≫ ε_ X Xᘁ) =
          inverseMate ≫ (λ_ Xᘁ).inv :=
      tensorRightHomEquiv_whiskerRight_comp_evaluation inverseMate
    exact leftRule.symm.trans ((congrArg e comparison).trans rightRule)
  exact (cancel_mono (λ_ Xᘁ).inv).mp composed

end TensorIdentityCharacter

section LinearSimple

universe uI

variable [IsAlgClosed K]
variable [Abelian C] [Linear K C]
variable [FiniteSemisimpleCategory.{v, uK, uC, uI} K C]

namespace TensorIdentityCharacter

/-- The Schur scalar of a monoidal identity character on a simple object. -/
noncomputable def simpleScalar
    (character : TensorIdentityCharacter (C := C))
    (X : C) [CategoryTheory.Simple X] : K :=
  (simpleEndLinearEquiv K X).symm (character.iso.hom.app X)

theorem component_on_simple_eq_scalar_smul_identity
    (character : TensorIdentityCharacter (C := C))
    (X : C) [CategoryTheory.Simple X] :
    character.iso.hom.app X = character.simpleScalar (K := K) X • 𝟙 X :=
  (simpleEndLinearEquiv K X).apply_symm_apply
    (character.iso.hom.app X) |>.symm

theorem simpleScalar_ne_zero
    (character : TensorIdentityCharacter (C := C))
    (X : C) [CategoryTheory.Simple X] :
    character.simpleScalar (K := K) X ≠ 0 := by
  intro scalar_zero
  have component_zero : character.iso.hom.app X = 0 := by
    rw [character.component_on_simple_eq_scalar_smul_identity (K := K) X,
      scalar_zero, zero_smul]
    rfl
  have identity_zero : 𝟙 X = 0 := by
    calc
      𝟙 X = character.iso.inv.app X ≫ character.iso.hom.app X :=
        (character.iso.inv_hom_id_app X).symm
      _ = character.iso.inv.app X ≫ 0 := by rw [component_zero]
      _ = 0 := Limits.comp_zero
  exact id_nonzero X identity_zero

/-- The nonzero Schur scalar, packaged as a unit of `K`. -/
noncomputable def simpleValue
    (character : TensorIdentityCharacter (C := C))
    (X : C) [CategoryTheory.Simple X] : Kˣ :=
  Units.mk0 (character.simpleScalar (K := K) X)
    (character.simpleScalar_ne_zero (K := K) X)

@[simp]
theorem simpleValue_val
    (character : TensorIdentityCharacter (C := C))
    (X : C) [CategoryTheory.Simple X] :
    (character.simpleValue (K := K) X : K) =
      character.simpleScalar (K := K) X :=
  rfl

end TensorIdentityCharacter

end LinearSimple

end CategoryTheory
