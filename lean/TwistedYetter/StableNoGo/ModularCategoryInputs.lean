import TwistedYetter.StableNoGo.ModularCategory

/-!
# Literature inputs for the modular numerical reduction

The external category facts are stated at the same semantic level as their
sources: the character-object correspondence, the two `S`-matrix Gauss-sum
identities, and the standard description of the powers of the character
object.  The shifted Gauss-sum formulas used downstream are theorems below,
not literature axioms.

References:

* EGNO, Lemma 8.22.9: characters of the universal grading group are
  represented by invertible objects in a non-degenerate braided fusion
  category.
* EGNO, Lemma 8.15.3 and Corollary 8.15.5: the positive and negative
  `S`-matrix Gauss-sum identities.
* EGNO, Proposition 8.15.4: `tau_plus * tau_minus = globalDimension`.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- An object has tensor inverse when tensoring it with its right dual gives the unit. -/
def IsTensorInvertible
    {C : Type*} [Category C] [MonoidalCategory C] [RightRigidCategory C]
    (X : C) : Prop :=
  Nonempty (X ⊗ Xᘁ ≅ 𝟙_ C)

/--
The invertible simple object `g_eta` corresponding to the monoidal identity
character.  The displayed equality is the unclosed tensor form of EGNO
equation (8.95): closing the `g_eta` strand gives the natural automorphism
`alpha(g_eta) = eta` of Lemma 8.22.9.  Our monodromy starts on `g_eta tensor X`,
so the character component occurs on the second tensor factor.
-/
structure ModularCharacterObject (𝒞η : TwistedModularCategory K) where
  simple : 𝒞η.category.Simple
  tensorInvertible :
    IsTensorInvertible (𝒞η.category.simpleObject simple)
  monodromy_eq_tensor_character :
    forall X : 𝒞η.category.C,
      monodromyHom (𝒞η.category.simpleObject simple) X =
        𝟙 (𝒞η.category.simpleObject simple) ⊗ₘ
          𝒞η.character.iso.hom.app X

/-- EGNO, Lemma 8.22.9, with the monodromy convention fixed above. -/
axiom egno_characterObject_exists (𝒞η : TwistedModularCategory K) :
    Nonempty (ModularCharacterObject 𝒞η)

/-- The ribbon twist of the character object, packaged as a unit of `K`. -/
noncomputable def ModularCharacterObject.twistUnit
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) : Kˣ :=
  Units.mk0
    (simpleTwistScalar 𝒞η.toPremodular g.simple)
    (simpleTwistScalar_ne_zero 𝒞η.toPremodular g.simple)

/-- The unshifted positive Gauss sum `tau_plus`. -/
noncomputable def positiveGaussSum
    (𝒞η : TwistedPremodularCategory K) : K :=
  positiveShiftedGaussSum 𝒞η 0

/-- The unshifted negative Gauss sum `tau_minus`. -/
noncomputable def negativeGaussSum
    (𝒞η : TwistedPremodularCategory K) : K :=
  negativeShiftedGaussSum 𝒞η 0

/--
The unnormalized `S`-matrix entry `s_XY`, defined exactly as the canonical
ribbon trace of positive monodromy.
-/
noncomputable def sMatrixEntry
    (𝒞η : TwistedPremodularCategory K)
    (first second : 𝒞η.category.Simple) : K :=
  𝒞η.category.closedScalar
    (𝒞η.category.canonicalRibbonTrace
      (monodromyHom
        (𝒞η.category.simpleObject first)
        (𝒞η.category.simpleObject second)))

/--
EGNO, Lemma 8.15.3, equation (8.58), printed page 229:
`sum_X theta_X dim(X) s_XY = dim(Y) theta_Y⁻¹ tau⁺(C)`.
-/
axiom egno_positiveGaussSum_sMatrixIdentity
    (𝒞η : TwistedModularCategory K)
    (second : 𝒞η.category.Simple) :
    (∑ first : 𝒞η.category.Simple,
      simpleTwistScalar 𝒞η.toPremodular first *
        𝒞η.category.quantumDimension first *
        sMatrixEntry 𝒞η.toPremodular first second) =
      𝒞η.category.quantumDimension second *
        (simpleTwistScalar 𝒞η.toPremodular second)⁻¹ *
        positiveGaussSum 𝒞η.toPremodular

/--
EGNO, Corollary 8.15.5, equation (8.61), printed page 230:
`sum_X theta_X⁻¹ dim(X) s_XY = dim(Y) theta_Y tau⁻(C)`.
-/
axiom egno_negativeGaussSum_sMatrixIdentity
    (𝒞η : TwistedModularCategory K)
    (second : 𝒞η.category.Simple) :
    (∑ first : 𝒞η.category.Simple,
      (simpleTwistScalar 𝒞η.toPremodular first)⁻¹ *
        𝒞η.category.quantumDimension first *
        sMatrixEntry 𝒞η.toPremodular first second) =
      𝒞η.category.quantumDimension second *
        simpleTwistScalar 𝒞η.toPremodular second *
        negativeGaussSum 𝒞η.toPremodular

/--
The simple object `g^n` obtained from the invertible character object.  The
first equation is EGNO's character pairing (8.95)--(8.96), traced on a simple
object; the second is quadraticity of the ribbon twist on the pointed
subcategory.  Keeping these equations separate prevents either convention
from being hidden inside a shifted Gauss-sum axiom.
-/
structure ModularCharacterPower
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) (n : ℤ) where
  simple : 𝒞η.category.Simple
  quantumDimension_ne_zero :
    𝒞η.category.quantumDimension simple ≠ 0
  sMatrixEntry_eq :
    ∀ first : 𝒞η.category.Simple,
      sMatrixEntry 𝒞η.toPremodular first simple =
        𝒞η.category.quantumDimension first *
          𝒞η.category.quantumDimension simple *
          ((((𝒞η.character.value first) ^ n : Kˣ) : K))
  twist_eq :
    simpleTwistScalar 𝒞η.toPremodular simple =
      (((g.twistUnit ^ (n * n) : Kˣ) : K))

/--
EGNO, equations (8.95)--(8.96) and Lemma 8.22.9, together with the balancing
equation restricted to the pointed subcategory.  This is the precise
character-power input; it contains no Gauss-sum conclusion.
-/
axiom egno_characterPower_exists
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) (n : ℤ) :
    Nonempty (ModularCharacterPower g n)

/-- The positive shifted formula derived from EGNO (8.58). -/
theorem egno_positiveShiftedGaussSum
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) (n : ℤ) :
    positiveShiftedGaussSum 𝒞η.toPremodular n =
      (((g.twistUnit ^ (-(n * n)) : Kˣ) : K)) *
        positiveGaussSum 𝒞η.toPremodular := by
  let power := Classical.choice (egno_characterPower_exists g n)
  have identity := egno_positiveGaussSum_sMatrixIdentity 𝒞η power.simple
  have expanded :
      𝒞η.category.quantumDimension power.simple *
          positiveShiftedGaussSum 𝒞η.toPremodular n =
        𝒞η.category.quantumDimension power.simple *
          (simpleTwistScalar 𝒞η.toPremodular power.simple)⁻¹ *
          positiveGaussSum 𝒞η.toPremodular := by
    rw [← identity]
    unfold positiveShiftedGaussSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [power.sMatrixEntry_eq]
    dsimp [TwistedModularCategory.toPremodular]
    ring
  have inverseTwist :
      ((((g.twistUnit ^ (n * n) : Kˣ) : K)))⁻¹ =
        (((g.twistUnit ^ (-(n * n)) : Kˣ) : K)) := by
    rw [zpow_neg, Units.val_inv_eq_inv_val]
  exact mul_left_cancel₀ power.quantumDimension_ne_zero (by
    rw [expanded, power.twist_eq, inverseTwist]
    ring)

/-- The negative shifted formula derived from EGNO (8.61). -/
theorem egno_negativeShiftedGaussSum
    {𝒞η : TwistedModularCategory K}
    (g : ModularCharacterObject 𝒞η) (n : ℤ) :
    negativeShiftedGaussSum 𝒞η.toPremodular n =
      (((g.twistUnit ^ (n * n) : Kˣ) : K)) *
        negativeGaussSum 𝒞η.toPremodular := by
  let power := Classical.choice (egno_characterPower_exists g n)
  have identity := egno_negativeGaussSum_sMatrixIdentity 𝒞η power.simple
  have expanded :
      𝒞η.category.quantumDimension power.simple *
          negativeShiftedGaussSum 𝒞η.toPremodular n =
        𝒞η.category.quantumDimension power.simple *
          simpleTwistScalar 𝒞η.toPremodular power.simple *
          negativeGaussSum 𝒞η.toPremodular := by
    rw [← identity]
    unfold negativeShiftedGaussSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [power.sMatrixEntry_eq]
    dsimp [TwistedModularCategory.toPremodular]
    ring
  exact mul_left_cancel₀ power.quantumDimension_ne_zero (by
    rw [expanded, power.twist_eq]
    ring)

/-- EGNO, Proposition 8.15.4. -/
axiom egno_gaussSums_product (𝒞η : TwistedModularCategory K) :
    positiveGaussSum 𝒞η.toPremodular *
        negativeGaussSum 𝒞η.toPremodular =
      𝒞η.category.globalDimension

theorem positiveGaussSum_ne_zero (𝒞η : TwistedModularCategory K) :
    positiveGaussSum 𝒞η.toPremodular ≠ 0 := by
  intro positiveZero
  have productZero :
      positiveGaussSum 𝒞η.toPremodular *
          negativeGaussSum 𝒞η.toPremodular = 0 := by
    rw [positiveZero, zero_mul]
  exact egno_globalDimension_ne_zero 𝒞η.category
    ((egno_gaussSums_product 𝒞η).symm.trans productZero)

theorem negativeGaussSum_ne_zero (𝒞η : TwistedModularCategory K) :
    negativeGaussSum 𝒞η.toPremodular ≠ 0 := by
  intro negativeZero
  have productZero :
      positiveGaussSum 𝒞η.toPremodular *
          negativeGaussSum 𝒞η.toPremodular = 0 := by
    rw [negativeZero, mul_zero]
  exact egno_globalDimension_ne_zero 𝒞η.category
    ((egno_gaussSums_product 𝒞η).symm.trans productZero)

end

end TwistedYetter.StableNoGo
