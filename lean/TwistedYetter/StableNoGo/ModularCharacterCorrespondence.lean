import TwistedYetter.StableNoGo.ModularCategory
import TwistedYetter.CategoryTheory.Rigid.TensorExactPairing

/-!
# The EGNO character-object correspondence

This module states only the character-object correspondence supplied by EGNO
(8.95)--(8.96) and Lemma 8.22.9.  It deliberately contains no `S`-matrix,
Gauss-sum, or twist-value conclusion.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-- A simple object together with the invertibility needed to close and reopen
its strand.  The `IsIso` field is object-domain data, not a numerical
conclusion about the invariant. -/
structure InvertibleSimpleObject
    (category : BundledPremodularCategory K) where
  simple : category.simples.Simple
  coevaluationIsIso :
    IsIso (η_ (category.simples.simpleObject simple)
      ((category.simples.simpleObject simple)ᘁ))

namespace InvertibleSimpleObject

variable {category : BundledPremodularCategory K}

noncomputable instance (g : InvertibleSimpleObject category) :
    IsIso (η_ (category.simples.simpleObject g.simple)
      ((category.simples.simpleObject g.simple)ᘁ)) :=
  g.coevaluationIsIso

/-- EGNO (8.95): close the positive monodromy around an invertible object. -/
noncomputable def alphaComponent
    (g : InvertibleSimpleObject category) (X : category.C) : X ⟶ X :=
  let G := category.simples.simpleObject g.simple
  (ρ_ X).inv ≫
    X ◁ η_ G (Gᘁ) ≫
    (α_ X G (Gᘁ)).inv ≫
    (monodromyHom X G ▷ (Gᘁ)) ≫
    (α_ X G (Gᘁ)).hom ≫
    X ◁ inv (η_ G (Gᘁ)) ≫
    (ρ_ X).hom

end InvertibleSimpleObject

/-- The exact semantic statement that the invertible object `g` corresponds
to the prescribed monoidal identity character under EGNO (8.95). -/
def RepresentsIdentityCharacter
    (categoryCharacter : TwistedModularCategory K)
    (g : InvertibleSimpleObject categoryCharacter.category) : Prop :=
  ∀ X : categoryCharacter.category.C,
    g.alphaComponent X = categoryCharacter.character.iso.hom.app X

/-- EGNO, Lemma 8.22.9(iii): in a non-degenerate braided fusion category,
every monoidal automorphism of the identity is represented by an invertible
simple object. -/
axiom egno_characterObject_correspondence
    (categoryCharacter : TwistedModularCategory K) :
    ∃ g : InvertibleSimpleObject categoryCharacter.category,
      RepresentsIdentityCharacter categoryCharacter g

/-- The canonical noncomputable character object selected from EGNO's
existence theorem. -/
noncomputable def egnoCharacterObject
    (categoryCharacter : TwistedModularCategory K) :
    InvertibleSimpleObject categoryCharacter.category :=
  Classical.choose (egno_characterObject_correspondence categoryCharacter)

/-- The selected object really represents the requested character. -/
theorem egnoCharacterObject_represents
    (categoryCharacter : TwistedModularCategory K) :
    RepresentsIdentityCharacter categoryCharacter
      (egnoCharacterObject categoryCharacter) :=
  Classical.choose_spec (egno_characterObject_correspondence categoryCharacter)

/-- A parenthesized natural tensor power of an object. -/
def naturalTensorPowerObject
    {C : Type*} [Category C] [MonoidalCategory C]
    (X : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => naturalTensorPowerObject X n ⊗ X

/-- Integral tensor powers use the selected right dual in negative degree. -/
def integralTensorPowerObject
    {C : Type*} [Category C] [MonoidalCategory C] [RightRigidCategory C]
    (X : C) : ℤ → C
  | .ofNat n => naturalTensorPowerObject X n
  | .negSucc n => naturalTensorPowerObject (Xᘁ) (n + 1)

/-- A simple-skeleton representative genuinely bound to the integral tensor
power of `g`; unlike the former interface, this contains no `S`-matrix or twist
formula. -/
structure CharacterPowerRepresentative
    {categoryCharacter : TwistedModularCategory K}
    (g : InvertibleSimpleObject categoryCharacter.category) (n : ℤ) where
  object : InvertibleSimpleObject categoryCharacter.category
  powerIso :
    categoryCharacter.category.simples.simpleObject object.simple ≅
      integralTensorPowerObject
        (categoryCharacter.category.simples.simpleObject g.simple) n

/-- EGNO, Lemma 8.22.9(ii), together with finite-simple-skeleton
representability: the group power of an invertible object has a chosen simple
representative.  No scalar evaluation is asserted here. -/
axiom egno_characterPowerRepresentative_exists
    {categoryCharacter : TwistedModularCategory K}
    (g : InvertibleSimpleObject categoryCharacter.category) (n : ℤ) :
    Nonempty (CharacterPowerRepresentative g n)

/-- Integral powers of an automorphism component, written without introducing
any scalar coordinates. -/
def automorphismNatPowerHom
    {C : Type*} [Category C] {X : C} (iso : X ≅ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => automorphismNatPowerHom iso n ≫ iso.hom

def automorphismIntPowerHom
    {C : Type*} [Category C] {X : C} (iso : X ≅ X) : ℤ → (X ⟶ X)
  | .ofNat n => automorphismNatPowerHom iso n
  | .negSucc n => automorphismNatPowerHom iso.symm (n + 1)

/-- EGNO, Lemma 8.22.9(ii): `alpha` is a group homomorphism.  This is stated
at the component level for the explicitly bound tensor-power representative;
it contains no trace, dimension, `S`-matrix, or twist conclusion. -/
axiom egno_alpha_characterPower
    {categoryCharacter : TwistedModularCategory K}
    (g : InvertibleSimpleObject categoryCharacter.category)
    (represents : RepresentsIdentityCharacter categoryCharacter g)
    (n : ℤ) (power : CharacterPowerRepresentative g n) :
    ∀ X : categoryCharacter.category.C,
      power.object.alphaComponent X =
        automorphismIntPowerHom
          (categoryCharacter.character.iso.app X) n

omit [IsAlgClosed K] [CharZero K] in
private theorem automorphismNatPowerHom_eq_unit_smul_identity
    {C : Type*} [Category C] [Preadditive C] [Linear K C]
    {X : C} (iso : X ≅ X) (unit : Kˣ)
    (homEq : iso.hom = (unit : K) • 𝟙 X) (n : ℕ) :
    automorphismNatPowerHom iso n =
      ((unit ^ n : Kˣ) : K) • 𝟙 X := by
  induction n with
  | zero => simp [automorphismNatPowerHom]
  | succ n inductionHypothesis =>
      simp only [automorphismNatPowerHom]
      rw [inductionHypothesis, homEq]
      simp [← mul_smul, pow_succ]
      rw [mul_comm]

private theorem automorphismIntPowerHom_eq_unit_zpow_smul_identity
    {C : Type*} [Category C] [Preadditive C] [Linear K C]
    {X : C} (iso : X ≅ X) (unit : Kˣ)
    (homEq : iso.hom = (unit : K) • 𝟙 X)
    (invEq : iso.inv = ((unit⁻¹ : Kˣ) : K) • 𝟙 X) (n : ℤ) :
    automorphismIntPowerHom iso n =
      ((unit ^ n : Kˣ) : K) • 𝟙 X := by
  cases n with
  | ofNat n =>
      exact automorphismNatPowerHom_eq_unit_smul_identity
        iso unit homEq n
  | negSucc n =>
      simpa [zpow_negSucc] using
        automorphismNatPowerHom_eq_unit_smul_identity
          iso.symm unit⁻¹ invEq (n + 1)

private theorem characterInverse_on_simple
    {categoryCharacter : TwistedModularCategory K}
    (first : categoryCharacter.category.simples.Simple) :
    categoryCharacter.character.iso.inv.app
        (categoryCharacter.category.simples.simpleObject first) =
      ((((categoryCharacter.character.value first)⁻¹ : Kˣ) : K)) •
        𝟙 (categoryCharacter.category.simples.simpleObject first) := by
  apply (cancel_epi
    (categoryCharacter.character.iso.hom.app
      (categoryCharacter.category.simples.simpleObject first))).1
  rw [categoryCharacter.character.iso.hom_inv_id_app]
  change
    𝟙 (categoryCharacter.category.simples.simpleObject first) =
      categoryCharacter.character.iso.hom.app
          (categoryCharacter.category.simples.simpleObject first) ≫
        (((((categoryCharacter.character.value first)⁻¹ : Kˣ) : K)) •
          𝟙 (categoryCharacter.category.simples.simpleObject first))
  rw [categoryCharacter.character.component_on_simple_eq_value_smul_identity]
  let X := categoryCharacter.category.simples.simpleObject first
  let unit := categoryCharacter.character.value first
  change 𝟙 X = ((unit : K) • 𝟙 X) ≫ (((unit⁻¹ : Kˣ) : K) • 𝟙 X)
  rw [CategoryTheory.Linear.comp_smul X X X
    ((unit : K) • 𝟙 X) (((unit⁻¹ : Kˣ) : K)) (𝟙 X)]
  rw [CategoryTheory.Linear.smul_comp X X X
    (unit : K) (𝟙 X) (𝟙 X)]
  simp only [Category.id_comp, smul_smul]
  rw [show (((unit⁻¹ : Kˣ) : K)) * (unit : K) = 1 by
    exact Units.inv_mul unit]
  simp

/-- On a simple object, the EGNO character-power component is the expected
integer power of its Schur scalar. -/
theorem egno_alpha_characterPower_on_simple
    {categoryCharacter : TwistedModularCategory K}
    (g : InvertibleSimpleObject categoryCharacter.category)
    (represents : RepresentsIdentityCharacter categoryCharacter g)
    (n : ℤ) (power : CharacterPowerRepresentative g n)
    (first : categoryCharacter.category.simples.Simple) :
    power.object.alphaComponent
        (categoryCharacter.category.simples.simpleObject first) =
      ((((categoryCharacter.character.value first) ^ n : Kˣ) : K)) •
        𝟙 (categoryCharacter.category.simples.simpleObject first) := by
  rw [egno_alpha_characterPower g represents n power]
  exact automorphismIntPowerHom_eq_unit_zpow_smul_identity
      (categoryCharacter.character.iso.app
      (categoryCharacter.category.simples.simpleObject first))
    (categoryCharacter.character.value first)
    (categoryCharacter.character.component_on_simple_eq_value_smul_identity first)
    (characterInverse_on_simple first)
    n

/-- The scalar of the closed-monodromy automorphism `alpha(g)` on a simple
object.  This is a definition through Schur's lemma, not an input law. -/
noncomputable def alphaScalar
    {categoryCharacter : TwistedModularCategory K}
    (g : InvertibleSimpleObject categoryCharacter.category)
    (first : categoryCharacter.category.simples.Simple) : K :=
  (simpleEndLinearEquiv K
    (categoryCharacter.category.simples.simpleObject first)).symm
      (g.alphaComponent
        (categoryCharacter.category.simples.simpleObject first))

/-- The unnormalized `S`-matrix entry: the canonical ribbon trace of positive
monodromy. -/
noncomputable def sMatrixEntry
    (categoryCharacter : TwistedPremodularCategory K)
    (first second : categoryCharacter.category.simples.Simple) : K :=
  categoryCharacter.category.closedScalar
    (categoryCharacter.category.canonicalRibbonTrace
      (monodromyHom
        (categoryCharacter.category.simples.simpleObject first)
        (categoryCharacter.category.simples.simpleObject second)))

/--
EGNO equation (8.96), printed page 249: under the character--invertible-object
pairing defined by (8.95), the normalized `S`-matrix entry is the Schur scalar
of `alpha(g)`.  This is the literature input; it does not mention powers of a
chosen character or any shifted Gauss sum.
-/
axiom egno_sMatrix_characterPairing
    {categoryCharacter : TwistedModularCategory K}
    (g : InvertibleSimpleObject categoryCharacter.category)
    (first : categoryCharacter.category.simples.Simple) :
    sMatrixEntry categoryCharacter.toPremodular first g.simple =
      categoryCharacter.category.quantumDimension first *
        categoryCharacter.category.quantumDimension g.simple *
          alphaScalar g first

/-- Schur-coordinate extraction sends a scalar multiple of the identity back
to that scalar. -/
private theorem alphaScalar_eq_of_alphaComponent_eq_smul_identity
    {categoryCharacter : TwistedModularCategory K}
    (g : InvertibleSimpleObject categoryCharacter.category)
    (first : categoryCharacter.category.simples.Simple)
    (scalar : K)
    (componentEq :
      g.alphaComponent
          (categoryCharacter.category.simples.simpleObject first) =
        scalar •
          𝟙 (categoryCharacter.category.simples.simpleObject first)) :
    alphaScalar g first = scalar := by
  unfold alphaScalar
  rw [componentEq]
  exact (simpleEndLinearEquiv K
    (categoryCharacter.category.simples.simpleObject first)).symm_apply_apply
      scalar

/-- EGNO (8.96), after substituting the theorem
`alpha(g^n) = eta^n`: the former `sMatrixEntry_eq` proof field is a derived
theorem. -/
theorem sMatrixEntry_characterPower_eq
    {categoryCharacter : TwistedModularCategory K}
    (g : InvertibleSimpleObject categoryCharacter.category)
    (represents : RepresentsIdentityCharacter categoryCharacter g)
    (n : ℤ) (power : CharacterPowerRepresentative g n)
    (first : categoryCharacter.category.simples.Simple) :
    sMatrixEntry categoryCharacter.toPremodular first power.object.simple =
      categoryCharacter.category.quantumDimension first *
        categoryCharacter.category.quantumDimension power.object.simple *
    ((((categoryCharacter.character.value first) ^ n : Kˣ) : K)) := by
  rw [egno_sMatrix_characterPairing power.object first]
  rw [alphaScalar_eq_of_alphaComponent_eq_smul_identity power.object first
    ((((categoryCharacter.character.value first) ^ n : Kˣ) : K))
    (egno_alpha_characterPower_on_simple g represents n power first)]

/-- The nonzero Schur scalar of the ribbon twist on an invertible simple
object, packaged as a unit. -/
noncomputable def InvertibleSimpleObject.twistUnit
    {categoryCharacter : TwistedModularCategory K}
    (g : InvertibleSimpleObject categoryCharacter.category) : Kˣ :=
  Units.mk0
    (simpleTwistScalar categoryCharacter.toPremodular g.simple)
    (simpleTwistScalar_ne_zero categoryCharacter.toPremodular g.simple)

/--
The ribbon twist restricted to the Picard group is a quadratic form.  In the
notation of EGNO Definition 8.4.1, this is `q(n g) = q(g)^(n^2)`; the ribbon
interpretation follows from the balancing and duality conditions in EGNO
Definition 8.10.1.  The statement is deliberately at the morphism level.
-/
axiom egno_picardTwist_quadratic
    {categoryCharacter : TwistedModularCategory K}
    (g : InvertibleSimpleObject categoryCharacter.category)
    (n : ℤ) (power : CharacterPowerRepresentative g n) :
    categoryCharacter.category.twist.hom.app
        (categoryCharacter.category.simples.simpleObject power.object.simple) =
      ((((g.twistUnit ^ (n * n) : Kˣ) : K))) •
        𝟙 (categoryCharacter.category.simples.simpleObject power.object.simple)

/-- The former scalar-valued `twist_eq` proof field, derived from Picard
quadraticity by Schur-coordinate extraction. -/
theorem simpleTwistScalar_characterPower_eq
    {categoryCharacter : TwistedModularCategory K}
    (g : InvertibleSimpleObject categoryCharacter.category)
    (n : ℤ) (power : CharacterPowerRepresentative g n) :
    simpleTwistScalar categoryCharacter.toPremodular power.object.simple =
      (((g.twistUnit ^ (n * n) : Kˣ) : K)) := by
  unfold simpleTwistScalar
  change
    (simpleEndLinearEquiv K
      (categoryCharacter.category.simples.simpleObject
        power.object.simple)).symm
        (categoryCharacter.category.twist.hom.app
          (categoryCharacter.category.simples.simpleObject
            power.object.simple)) = _
  rw [egno_picardTwist_quadratic g n power]
  exact (simpleEndLinearEquiv K
    (categoryCharacter.category.simples.simpleObject
      power.object.simple)).symm_apply_apply _

end

end TwistedYetter.StableNoGo
