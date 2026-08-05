import TwistedYetter.StableNoGo.Main

/-!
# Numerical expressions for the stable Twisted Yetter formula

These are the fixed numerical definitions shared by the standard-block
calculations and the public final theorem.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- The normalization for which connected sum is exactly multiplicative. -/
noncomputable def NormalizedTwistedYetter
    (𝒞η : TwistedPremodularCategory K)
    (Xα : Σ X : ClosedOrientedSmoothFourManifold, ManifoldH₂ X) : K :=
  𝒞η.category.globalDimension⁻¹ * TwistedYetter 𝒞η Xα

/-
Framing convention used throughout the standard-block calculation:

* zero explicit framing twists give the canonical ribbon/spherical trace of
  the identity;
* one positive explicit framing twist inserts `theta`;
* one negative explicit framing twist inserts `theta⁻¹`.

Thus the scalar below occurs only for an explicitly recorded framing twist.
-/
/-- The scalar by which the ribbon twist acts on a chosen simple object. -/
noncomputable def simpleTwistScalar
    (𝒞η : TwistedPremodularCategory K)
    (simple : 𝒞η.category.Simple) : K :=
  (simpleEndLinearEquiv K (𝒞η.category.simpleObject simple)).symm
    (𝒞η.category.twist.hom.app (𝒞η.category.simpleObject simple))

theorem twist_hom_on_simple_eq_smul_identity
    (𝒞η : TwistedPremodularCategory K)
    (simple : 𝒞η.category.Simple) :
    𝒞η.category.twist.hom.app (𝒞η.category.simpleObject simple) =
      simpleTwistScalar 𝒞η simple •
        𝟙 (𝒞η.category.simpleObject simple) := by
  exact
    (simpleEndLinearEquiv K (𝒞η.category.simpleObject simple)).apply_symm_apply
      (𝒞η.category.twist.hom.app (𝒞η.category.simpleObject simple)) |>.symm

theorem simpleTwistScalar_ne_zero
    (𝒞η : TwistedPremodularCategory K)
    (simple : 𝒞η.category.Simple) :
    simpleTwistScalar 𝒞η simple ≠ 0 := by
  intro scalarZero
  let X := 𝒞η.category.simpleObject simple
  have twistZero : 𝒞η.category.twist.hom.app X = 0 := by
    simpa [X, scalarZero] using
      twist_hom_on_simple_eq_smul_identity 𝒞η simple
  have identityZero : 𝟙 X = 0 := by
    have inverseIdentity := 𝒞η.category.twist.hom_inv_id_app X
    change
      𝒞η.category.twist.hom.app X ≫
          𝒞η.category.twist.inv.app X = 𝟙 X at inverseIdentity
    rw [twistZero] at inverseIdentity
    simpa only [Limits.zero_comp] using inverseIdentity.symm
  exact (id_nonzero X) identityZero

theorem twist_inv_on_simple_eq_smul_identity
    (𝒞η : TwistedPremodularCategory K)
    (simple : 𝒞η.category.Simple) :
    𝒞η.category.twist.inv.app (𝒞η.category.simpleObject simple) =
      (simpleTwistScalar 𝒞η simple)⁻¹ •
        𝟙 (𝒞η.category.simpleObject simple) := by
  apply (cancel_epi
    (𝒞η.category.twist.hom.app
      (𝒞η.category.simpleObject simple))).1
  rw [show
    𝒞η.category.twist.hom.app (𝒞η.category.simpleObject simple) ≫
        𝒞η.category.twist.inv.app (𝒞η.category.simpleObject simple) =
      𝟙 (𝒞η.category.simpleObject simple) by
    simpa using 𝒞η.category.twist.hom_inv_id_app
      (𝒞η.category.simpleObject simple)]
  rw [twist_hom_on_simple_eq_smul_identity]
  simp [simpleTwistScalar_ne_zero]

theorem closedScalar_ribbonTrace_twist
    (𝒞η : TwistedPremodularCategory K)
    (simple : 𝒞η.category.Simple) :
    𝒞η.category.closedScalar
        (𝒞η.category.canonicalRibbonTrace
          (𝒞η.category.twist.hom.app
            (𝒞η.category.simpleObject simple))) =
      𝒞η.category.quantumDimension simple *
        simpleTwistScalar 𝒞η simple := by
  letI : Simple (𝟙_ 𝒞η.category.C) :=
    FusionCategory.tensorUnit_simple (K := K)
  rw [twist_hom_on_simple_eq_smul_identity]
  have traceEquality :
    𝒞η.category.canonicalRibbonTrace
        (simpleTwistScalar 𝒞η simple •
          𝟙 (𝒞η.category.simpleObject simple)) =
      simpleTwistScalar 𝒞η simple •
        𝒞η.category.canonicalRibbonTrace
          (𝟙 (𝒞η.category.simpleObject simple)) := by
    exact pivotalTrace_smul K
      𝒞η.category.canonicalSpherical.toPivotalStructure _ _
  calc
    _ = 𝒞η.category.closedScalar
          (simpleTwistScalar 𝒞η simple •
            𝒞η.category.canonicalRibbonTrace
              (𝟙 (𝒞η.category.simpleObject simple))) :=
        congrArg 𝒞η.category.closedScalar traceEquality
    _ = simpleTwistScalar 𝒞η simple *
          𝒞η.category.quantumDimension simple := by
        change
          (simpleEndLinearEquiv K (𝟙_ 𝒞η.category.C)).symm
              (simpleTwistScalar 𝒞η simple •
                𝒞η.category.canonicalRibbonTrace
                  (𝟙 (𝒞η.category.simpleObject simple))) = _
        rw [map_smul]
        rfl
    _ = _ := mul_comm _ _

theorem closedScalar_ribbonTrace_twist_inv
    (𝒞η : TwistedPremodularCategory K)
    (simple : 𝒞η.category.Simple) :
    𝒞η.category.closedScalar
        (𝒞η.category.canonicalRibbonTrace
          (𝒞η.category.twist.inv.app
            (𝒞η.category.simpleObject simple))) =
      𝒞η.category.quantumDimension simple *
        (simpleTwistScalar 𝒞η simple)⁻¹ := by
  letI : Simple (𝟙_ 𝒞η.category.C) :=
    FusionCategory.tensorUnit_simple (K := K)
  rw [twist_inv_on_simple_eq_smul_identity]
  have traceEquality :
    𝒞η.category.canonicalRibbonTrace
        ((simpleTwistScalar 𝒞η simple)⁻¹ •
          𝟙 (𝒞η.category.simpleObject simple)) =
      (simpleTwistScalar 𝒞η simple)⁻¹ •
        𝒞η.category.canonicalRibbonTrace
          (𝟙 (𝒞η.category.simpleObject simple)) := by
    exact pivotalTrace_smul K
      𝒞η.category.canonicalSpherical.toPivotalStructure _ _
  calc
    _ = 𝒞η.category.closedScalar
          ((simpleTwistScalar 𝒞η simple)⁻¹ •
            𝒞η.category.canonicalRibbonTrace
              (𝟙 (𝒞η.category.simpleObject simple))) :=
        congrArg 𝒞η.category.closedScalar traceEquality
    _ = (simpleTwistScalar 𝒞η simple)⁻¹ *
          𝒞η.category.quantumDimension simple := by
        change
          (simpleEndLinearEquiv K (𝟙_ 𝒞η.category.C)).symm
              ((simpleTwistScalar 𝒞η simple)⁻¹ •
                𝒞η.category.canonicalRibbonTrace
                  (𝟙 (𝒞η.category.simpleObject simple))) = _
        rw [map_smul]
        rfl
    _ = _ := mul_comm _ _

/-- `Σᵢ dᵢ² θᵢ ηᵢⁿ`. -/
noncomputable def positiveShiftedGaussSum
    (𝒞η : TwistedPremodularCategory K) (n : ℤ) : K :=
  ∑ simple : 𝒞η.category.Simple,
    𝒞η.category.quantumDimension simple ^ 2 *
      simpleTwistScalar 𝒞η simple *
      ((((𝒞η.character.value simple) ^ n : Kˣ) : K))

/-- `Σᵢ dᵢ² θᵢ⁻¹ ηᵢⁿ`. -/
noncomputable def negativeShiftedGaussSum
    (𝒞η : TwistedPremodularCategory K) (n : ℤ) : K :=
  ∑ simple : 𝒞η.category.Simple,
    𝒞η.category.quantumDimension simple ^ 2 *
      (simpleTwistScalar 𝒞η simple)⁻¹ *
      ((((𝒞η.character.value simple) ^ n : Kˣ) : K))

end

end TwistedYetter.StableNoGo
