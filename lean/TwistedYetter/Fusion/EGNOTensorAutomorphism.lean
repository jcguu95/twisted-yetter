import TwistedYetter.Fusion.EGNOTracePairing

/-!
# Tensor automorphisms of a fusion category

A homological Kirby colour uses the scalar action of a monoidal natural
automorphism of the identity functor on every simple object.  The scalar table
is not independent data: Schur's lemma derives it from the categorical
automorphism.

This module records the genuine categorical input and derives:

* the tensor and unit laws from `NatTrans.IsMonoidal`;
* the unique scalar action on every listed simple;
* nonvanishing of that scalar from invertibility of the natural isomorphism;
* the corresponding element of `Kˣ`.

No concrete fusion category or nontrivial automorphism is selected here.
-/

namespace TwistedYetter.Fusion.EGNO

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
A monoidal natural automorphism of the identity functor.

The monoidality proof is categorical data.  There is deliberately no field
for a scalar character on the simple-object index.
-/
structure TensorIdentityAutomorphism (C : Type uC)
    [Category.{vC} C] [MonoidalCategory C] where
  iso : 𝟭 C ≅ 𝟭 C
  monoidal : NatTrans.IsMonoidal iso.hom

namespace TensorIdentityAutomorphism

variable (automorphism : TensorIdentityAutomorphism C)

/-- The tensor law, derived from Mathlib's monoidal-natural-transformation law. -/
theorem tensor_hom (X Y : C) :
    automorphism.iso.hom.app (X ⊗ Y) =
      automorphism.iso.hom.app X ⊗ₘ
        automorphism.iso.hom.app Y := by
  letI : NatTrans.IsMonoidal automorphism.iso.hom :=
    automorphism.monoidal
  simpa using
    (NatTrans.IsMonoidal.tensor
      (τ := automorphism.iso.hom) X Y)

/-- The unit law, derived from the same monoidality proof. -/
theorem unit_hom :
    automorphism.iso.hom.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
  letI : NatTrans.IsMonoidal automorphism.iso.hom :=
    automorphism.monoidal
  simpa using
    (NatTrans.IsMonoidal.unit
      (τ := automorphism.iso.hom))

/-- The identity monoidal natural automorphism. -/
def identity (C : Type uC) [Category.{vC} C] [MonoidalCategory C] :
    TensorIdentityAutomorphism C where
  iso := Iso.refl (𝟭 C)
  monoidal := by
    change NatTrans.IsMonoidal (𝟙 (𝟭 C))
    infer_instance

end TensorIdentityAutomorphism

namespace FusionCategoryData

variable (data : FusionCategoryData (K := K) (C := C) (S := S))

/--
The scalar by which a tensor identity automorphism acts on a listed simple.

This is computed by the Schur equivalence already derived from the finite
semisimple fusion data.
-/
noncomputable def automorphismSimpleScalar
    (automorphism : TensorIdentityAutomorphism C)
    (s : S) : K := by
  letI : Simple (data.simple s) := data.simple_isSimple s
  exact data.simpleScalar (data.simple s)
    (automorphism.iso.hom.app (data.simple s))

omit [MonoidalPreadditive C] [MonoidalLinear K C] in
/-- The categorical action is exactly scalar multiplication by the derived scalar. -/
theorem automorphism_app_eq_smul_identity
    (automorphism : TensorIdentityAutomorphism C)
    (s : S) :
    automorphism.iso.hom.app (data.simple s) =
      data.automorphismSimpleScalar automorphism s •
        𝟙 (data.simple s) := by
  letI : Simple (data.simple s) := data.simple_isSimple s
  symm
  change
    (data.simpleEndLinearEquiv (data.simple s))
        ((data.simpleEndLinearEquiv (data.simple s)).symm
          (automorphism.iso.hom.app (data.simple s))) =
      automorphism.iso.hom.app (data.simple s)
  exact
    (data.simpleEndLinearEquiv (data.simple s)).apply_symm_apply
      (automorphism.iso.hom.app (data.simple s))

omit [MonoidalPreadditive C] [MonoidalLinear K C] in
/-- Invertibility of the natural isomorphism forces every simple scalar to be nonzero. -/
theorem automorphismSimpleScalar_ne_zero
    (automorphism : TensorIdentityAutomorphism C)
    (s : S) :
    data.automorphismSimpleScalar automorphism s ≠ 0 := by
  letI : Simple (data.simple s) := data.simple_isSimple s
  intro scalar_zero
  have app_zero :
      automorphism.iso.hom.app (data.simple s) = 0 :=
    (data.simpleScalar_eq_zero_iff
      (data.simple s)
      (automorphism.iso.hom.app (data.simple s))).mp scalar_zero
  have inverse_composite :
      automorphism.iso.inv.app (data.simple s) ≫
          automorphism.iso.hom.app (data.simple s) =
        𝟙 (data.simple s) := by
    simpa using automorphism.iso.inv_hom_id_app (data.simple s)
  have identity_zero : 𝟙 (data.simple s) = 0 := by
    calc
      𝟙 (data.simple s) =
          automorphism.iso.inv.app (data.simple s) ≫
            automorphism.iso.hom.app (data.simple s) :=
        inverse_composite.symm
      _ =
          automorphism.iso.inv.app (data.simple s) ≫ 0 := by
        rw [app_zero]
      _ = 0 := CategoryTheory.Limits.comp_zero
  exact CategoryTheory.id_nonzero (data.simple s) identity_zero

/-- The derived simple scalar, packaged as an element of the unit group. -/
noncomputable def automorphismSimpleUnit
    (automorphism : TensorIdentityAutomorphism C)
    (s : S) : Kˣ :=
  Units.mk0
    (data.automorphismSimpleScalar automorphism s)
    (data.automorphismSimpleScalar_ne_zero automorphism s)

@[simp]
theorem automorphismSimpleUnit_val
    (automorphism : TensorIdentityAutomorphism C)
    (s : S) :
    (data.automorphismSimpleUnit automorphism s : K) =
      data.automorphismSimpleScalar automorphism s :=
  rfl

/-- Integral powers of the derived simple unit. -/
noncomputable def automorphismScalarPower
    (automorphism : TensorIdentityAutomorphism C)
    (s : S)
    (exponent : ℤ) : K :=
  ↑((data.automorphismSimpleUnit automorphism s) ^ exponent : Kˣ)

@[simp]
theorem automorphismScalarPower_zero
    (automorphism : TensorIdentityAutomorphism C)
    (s : S) :
    data.automorphismScalarPower automorphism s 0 = 1 := by
  simp [automorphismScalarPower]

theorem automorphismScalarPower_add
    (automorphism : TensorIdentityAutomorphism C)
    (s : S)
    (left right : ℤ) :
    data.automorphismScalarPower automorphism s (left + right) =
      data.automorphismScalarPower automorphism s left *
        data.automorphismScalarPower automorphism s right := by
  simpa only [automorphismScalarPower, Units.val_mul] using
    congrArg
      (fun unit : Kˣ => (unit : K))
      (zpow_add
        (data.automorphismSimpleUnit automorphism s) left right)

@[simp]
theorem identity_automorphism_simple_scalar
    (s : S) :
    data.automorphismSimpleScalar
        (TensorIdentityAutomorphism.identity C) s =
      1 := by
  letI : Simple (data.simple s) := data.simple_isSimple s
  exact data.simpleScalar_identity (data.simple s)

@[simp]
theorem identity_automorphism_scalar_power
    (s : S)
    (exponent : ℤ) :
    data.automorphismScalarPower
        (TensorIdentityAutomorphism.identity C) s exponent =
      1 := by
  simp [automorphismScalarPower, automorphismSimpleUnit,
    identity_automorphism_simple_scalar]

end FusionCategoryData

end TwistedYetter.Fusion.EGNO
