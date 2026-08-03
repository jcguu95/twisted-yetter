import TwistedYetter.CategoryTheory.Premodular.Bundled

/-!
# Independent semantics: typed ribbon graphical calculus

Every expression is indexed by its categorical source and target.  General
coupons contain actual morphisms; names and parser identifiers are not part of
their mathematical meaning.  Closed evaluation is derived by interpreting the
expression as an endomorphism of the tensor unit and then applying Schur
scalarization.

The sole external graphical theorem used later is Shum's coherence theorem
for ribbon categories.  Its exact statement is deliberately located in
`EntranceAxioms`; this file only defines typed syntax, interpretation, and
canonical closed evaluation.

M.-C. Shum, *Tortile tensor categories*, Journal of Pure and Applied Algebra
93 (1994), Theorem 2.6.
-/

namespace TwistedYetter.Semantics.Independent

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe uK uC uS v

noncomputable section

inductive RibbonDirection
  | forward
  | dual
  deriving DecidableEq, Repr

inductive RibbonCrossingSign
  | positive
  | negative
  deriving DecidableEq, Repr

structure OrientedSimple
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) where
  label : 𝒞.simples.Simple
  direction : RibbonDirection

def RibbonWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) :=
  List (OrientedSimple 𝒞)

def orientedSimpleObject
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (strand : OrientedSimple 𝒞) : 𝒞.C :=
  match strand.direction with
  | .forward => 𝒞.simples.simpleObject strand.label
  | .dual => (𝒞.simples.simpleObject strand.label)ᘁ

def ribbonWordObject
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) :
    RibbonWord 𝒞 → 𝒞.C
  | [] => 𝟙_ 𝒞.C
  | strand :: rest =>
      orientedSimpleObject 𝒞 strand ⊗ ribbonWordObject 𝒞 rest

/--
Typed formal linear combinations of categorical ribbon morphisms.

Invalid composition is unrepresentable: `compose` requires the intermediate
object to agree definitionally.
-/
inductive RibbonExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory.{v, uK, uC, uS} K) :
    𝒞.C → 𝒞.C → Type (max uK uC uS v)
  | morphism {X Y : 𝒞.C} (map : X ⟶ Y) :
      RibbonExpression 𝒞 X Y
  | compose {X Y Z : 𝒞.C}
      (first : RibbonExpression 𝒞 X Y)
      (second : RibbonExpression 𝒞 Y Z) :
      RibbonExpression 𝒞 X Z
  | tensor {X₁ Y₁ X₂ Y₂ : 𝒞.C}
      (left : RibbonExpression 𝒞 X₁ Y₁)
      (right : RibbonExpression 𝒞 X₂ Y₂) :
      RibbonExpression 𝒞 (X₁ ⊗ X₂) (Y₁ ⊗ Y₂)
  | zero {X Y : 𝒞.C} :
      RibbonExpression 𝒞 X Y
  | add {X Y : 𝒞.C}
      (left right : RibbonExpression 𝒞 X Y) :
      RibbonExpression 𝒞 X Y
  | smul {X Y : 𝒞.C}
      (scalar : K)
      (term : RibbonExpression 𝒞 X Y) :
      RibbonExpression 𝒞 X Y

def RibbonExpression.interpret
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    {X Y : 𝒞.C} :
    RibbonExpression 𝒞 X Y → (X ⟶ Y)
  | .morphism map => map
  | .compose first second =>
      first.interpret ≫ second.interpret
  | .tensor left right =>
      left.interpret ⊗ₘ right.interpret
  | .zero => 0
  | .add left right =>
      left.interpret + right.interpret
  | .smul scalar term =>
      scalar • term.interpret

def identityExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 X X :=
  .morphism (𝟙 X)

def positiveCrossing
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (X Y : 𝒞.C) :
    RibbonExpression 𝒞 (X ⊗ Y) (Y ⊗ X) :=
  .morphism (β_ X Y).hom

def negativeCrossing
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (X Y : 𝒞.C) :
    RibbonExpression 𝒞 (X ⊗ Y) (Y ⊗ X) :=
  .morphism (β_ Y X).inv

def coevaluationExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 (𝟙_ 𝒞.C) (X ⊗ Xᘁ) :=
  .morphism (η_ X (Xᘁ))

def evaluationExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 (Xᘁ ⊗ X) (𝟙_ 𝒞.C) :=
  .morphism (ε_ X (Xᘁ))

def positiveTwist
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 X X :=
  .morphism (𝒞.twist.hom.app X)

def negativeTwist
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 X X :=
  .morphism (𝒞.twist.inv.app X)

/-- A general coupon is an actual categorical morphism. -/
def morphismCoupon
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    {X Y : 𝒞.C}
    (map : X ⟶ Y) :
    RibbonExpression 𝒞 X Y :=
  .morphism map

def isoNatPowerHom
    {C : Type uC} [Category.{v} C]
    {X : C}
    (iso : X ≅ X) :
    ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => isoNatPowerHom iso n ≫ iso.hom

def isoIntPowerHom
    {C : Type uC} [Category.{v} C]
    {X : C}
    (iso : X ≅ X) :
    ℤ → (X ⟶ X)
  | .ofNat n => isoNatPowerHom iso n
  | .negSucc n => isoNatPowerHom iso.symm (n + 1)

private theorem isoNatPowerHom_eq_unit_smul_identity
    {K : Type uK} [Field K]
    {C : Type uC} [Category.{v} C] [Preadditive C] [Linear K C]
    {X : C}
    (iso : X ≅ X)
    (unit : Kˣ)
    (hom_eq : iso.hom = (unit : K) • 𝟙 X)
    (power : ℕ) :
    isoNatPowerHom iso power =
      ((unit ^ power : Kˣ) : K) • 𝟙 X := by
  induction power with
  | zero => simp [isoNatPowerHom]
  | succ power inductionHypothesis =>
      simp only [isoNatPowerHom]
      rw [inductionHypothesis, hom_eq]
      simp [← mul_smul, pow_succ]
      rw [mul_comm]

private theorem isoIntPowerHom_eq_unit_zpow_smul_identity
    {K : Type uK} [Field K]
    {C : Type uC} [Category.{v} C] [Preadditive C] [Linear K C]
    {X : C}
    (iso : X ≅ X)
    (unit : Kˣ)
    (hom_eq : iso.hom = (unit : K) • 𝟙 X)
    (inv_eq : iso.inv = ((unit⁻¹ : Kˣ) : K) • 𝟙 X)
    (exponent : ℤ) :
    isoIntPowerHom iso exponent =
      ((unit ^ exponent : Kˣ) : K) • 𝟙 X := by
  cases exponent with
  | ofNat power =>
      exact isoNatPowerHom_eq_unit_smul_identity
        iso unit hom_eq power
  | negSucc power =>
      simpa [zpow_negSucc] using
        isoNatPowerHom_eq_unit_smul_identity
          iso.symm unit⁻¹ inv_eq (power + 1)

/-- The actual character morphism on an arbitrary object. -/
def characterCoupon
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (X : 𝒞.C)
    (exponent : ℤ) :
    RibbonExpression 𝒞 X X :=
  .morphism (isoIntPowerHom (character.iso.app X) exponent)

private theorem characterCoupon_natPower_naturality
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    {X Y : 𝒞.C}
    (f : X ⟶ Y)
    (power : ℕ) :
    isoNatPowerHom (character.iso.app X) power ≫ f =
      f ≫ isoNatPowerHom (character.iso.app Y) power := by
  have naturality :
      (character.iso.app X).hom ≫ f =
        f ≫ (character.iso.app Y).hom := by
    simpa using (character.iso.hom.naturality f).symm
  induction power with
  | zero =>
      simp [isoNatPowerHom]
  | succ power inductionHypothesis =>
      simp only [isoNatPowerHom, Category.assoc]
      rw [naturality]
      calc
        isoNatPowerHom (character.iso.app X) power ≫
              (f ≫ (character.iso.app Y).hom) =
            (isoNatPowerHom (character.iso.app X) power ≫ f) ≫
              (character.iso.app Y).hom := (Category.assoc _ _ _).symm
        _ =
            (f ≫ isoNatPowerHom (character.iso.app Y) power) ≫
              (character.iso.app Y).hom :=
          congrArg
            (fun map => map ≫ (character.iso.app Y).hom)
            inductionHypothesis
        _ =
            f ≫ (isoNatPowerHom (character.iso.app Y) power ≫
              (character.iso.app Y).hom) := Category.assoc _ _ _

private theorem characterCoupon_invNatPower_naturality
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    {X Y : 𝒞.C}
    (f : X ⟶ Y)
    (power : ℕ) :
    isoNatPowerHom (character.iso.app X).symm power ≫ f =
      f ≫ isoNatPowerHom (character.iso.app Y).symm power := by
  have naturality :
      (character.iso.app X).symm.hom ≫ f =
        f ≫ (character.iso.app Y).symm.hom := by
    simpa using (character.iso.inv.naturality f).symm
  induction power with
  | zero =>
      simp [isoNatPowerHom]
  | succ power inductionHypothesis =>
      simp only [isoNatPowerHom, Category.assoc]
      rw [naturality]
      calc
        isoNatPowerHom (character.iso.app X).symm power ≫
              (f ≫ (character.iso.app Y).symm.hom) =
            (isoNatPowerHom (character.iso.app X).symm power ≫ f) ≫
              (character.iso.app Y).symm.hom := (Category.assoc _ _ _).symm
        _ =
            (f ≫ isoNatPowerHom (character.iso.app Y).symm power) ≫
              (character.iso.app Y).symm.hom :=
          congrArg
            (fun map => map ≫ (character.iso.app Y).symm.hom)
            inductionHypothesis
        _ =
            f ≫ (isoNatPowerHom (character.iso.app Y).symm power ≫
              (character.iso.app Y).symm.hom) := Category.assoc _ _ _

/--
Naturality of every integral power of the character automorphism.

This is the single categorical calculation behind transporting a character
coupon across a crossing, cup, cap, twist, or general morphism coupon: after
interpretation, every such local event is simply a morphism `f : X ⟶ Y`.
-/
theorem characterCoupon_naturality
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    {X Y : 𝒞.C}
    (f : X ⟶ Y)
    (exponent : ℤ) :
    isoIntPowerHom (character.iso.app X) exponent ≫ f =
      f ≫ isoIntPowerHom (character.iso.app Y) exponent := by
  cases exponent with
  | ofNat power =>
      exact characterCoupon_natPower_naturality character f power
  | negSucc power =>
      exact
        characterCoupon_invNatPower_naturality
          character f (power + 1)

theorem character_inv_on_simple_eq_value_inv_smul_identity
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (simple : 𝒞.simples.Simple) :
    character.iso.inv.app (𝒞.simples.simpleObject simple) =
      (((character.value simple)⁻¹ : Kˣ) : K) •
        𝟙 (𝒞.simples.simpleObject simple) := by
  apply (cancel_epi
    (character.iso.hom.app
      (𝒞.simples.simpleObject simple))).1
  rw [character.iso.hom_inv_id_app]
  rw [character.component_on_simple_eq_value_smul_identity]
  change
    𝟙 (𝒞.simples.simpleObject simple) =
      ((character.value simple : K) •
          𝟙 (𝒞.simples.simpleObject simple)) ≫
        ((((character.value simple)⁻¹ : Kˣ) : K) •
          𝟙 (𝒞.simples.simpleObject simple))
  rw [Linear.smul_comp]
  simp only [Category.id_comp]
  rw [← mul_smul]
  have scalar_cancel :
      (character.value simple : K) *
          (((character.value simple)⁻¹ : Kˣ) : K) =
        1 := by
    exact Units.mul_inv (character.value simple)
  rw [scalar_cancel, one_smul]

theorem character_hom_on_rightDual_eq_value_inv_smul_identity
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (simple : 𝒞.simples.Simple) :
    character.iso.hom.app
        ((𝒞.simples.simpleObject simple)ᘁ) =
      (((character.value simple)⁻¹ : Kˣ) : K) •
        𝟙 ((𝒞.simples.simpleObject simple)ᘁ) := by
  rw [character.hom_app_rightDual]
  rw [character_inv_on_simple_eq_value_inv_smul_identity]
  exact TensorIdentityCharacter.rightAdjointMate_smul_identity
    (𝒞 := 𝒞)
    (((character.value simple)⁻¹ : Kˣ) : K)
    (𝒞.simples.simpleObject simple)

theorem character_inv_on_rightDual_eq_value_smul_identity
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (simple : 𝒞.simples.Simple) :
    character.iso.inv.app
        ((𝒞.simples.simpleObject simple)ᘁ) =
      (character.value simple : K) •
        𝟙 ((𝒞.simples.simpleObject simple)ᘁ) := by
  apply (cancel_epi
    (character.iso.hom.app
      ((𝒞.simples.simpleObject simple)ᘁ))).1
  rw [character.iso.hom_inv_id_app]
  rw [character_hom_on_rightDual_eq_value_inv_smul_identity]
  let X : 𝒞.C := (𝒞.simples.simpleObject simple)ᘁ
  change
    𝟙 X =
      ((((character.value simple)⁻¹ : Kˣ) : K) •
          𝟙 X) ≫
        ((character.value simple : K) • 𝟙 X)
  rw [Linear.smul_comp]
  simp only [Category.id_comp]
  rw [← mul_smul]
  have scalar_cancel :
      (((character.value simple)⁻¹ : Kˣ) : K) *
          (character.value simple : K) =
        1 := by
    exact Units.inv_mul (character.value simple)
  rw [scalar_cancel, one_smul]

/--
On a positively oriented simple strand, an integral character coupon is the
corresponding integral power of the derived simple scalar.
-/
theorem characterCoupon_on_forwardSimple
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (simple : 𝒞.simples.Simple)
    (exponent : ℤ) :
    isoIntPowerHom
        (character.iso.app (𝒞.simples.simpleObject simple))
        exponent =
      (((character.value simple) ^ exponent : Kˣ) : K) •
        𝟙 (𝒞.simples.simpleObject simple) := by
  exact isoIntPowerHom_eq_unit_zpow_smul_identity
    (character.iso.app (𝒞.simples.simpleObject simple))
    (character.value simple)
    (character.component_on_simple_eq_value_smul_identity simple)
    (character_inv_on_simple_eq_value_inv_smul_identity character simple)
    exponent

/--
On the right dual strand, the same coupon carries the inverse scalar power.
This is derived from rigidity, not supplied as an orientation convention.
-/
theorem characterCoupon_on_dualSimple
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (simple : 𝒞.simples.Simple)
    (exponent : ℤ) :
    isoIntPowerHom
        (character.iso.app
          ((𝒞.simples.simpleObject simple)ᘁ))
        exponent =
      (((character.value simple) ^ (-exponent) : Kˣ) : K) •
        𝟙 ((𝒞.simples.simpleObject simple)ᘁ) := by
  simpa [zpow_neg] using
    isoIntPowerHom_eq_unit_zpow_smul_identity
      (character.iso.app
        ((𝒞.simples.simpleObject simple)ᘁ))
      (character.value simple)⁻¹
      (character_hom_on_rightDual_eq_value_inv_smul_identity
        character simple)
      (by
        simpa using
          character_inv_on_rightDual_eq_value_smul_identity
            character simple)
      exponent

/--
Proof-relevant typed transport of a character coupon.

The base constructor is naturality across an arbitrary actual morphism.  The
remaining constructors place that local rewrite inside composition, tensor,
linear combination, and scalar contexts.  Thus no topology axiom states an
evaluation equality, and no caller may label two unrelated expressions as one
transport step.
-/
inductive CharacterCouponTransport
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory.{v, uK, uC, uS} K}
    (character : TensorIdentityCharacter (C := 𝒞.C)) :
    {X Y : 𝒞.C} →
      RibbonExpression 𝒞 X Y →
      RibbonExpression 𝒞 X Y → Type (max uK uC uS v)
  | naturality
      {X Y : 𝒞.C}
      (f : X ⟶ Y)
      (exponent : ℤ) :
      CharacterCouponTransport character
        (.compose
          (characterCoupon character X exponent)
          (.morphism f))
        (.compose
          (.morphism f)
          (characterCoupon character Y exponent))
  | refl
      {X Y : 𝒞.C}
      (term : RibbonExpression 𝒞 X Y) :
      CharacterCouponTransport character term term
  | trans
      {X Y : 𝒞.C}
      {first middle last : RibbonExpression 𝒞 X Y}
      (left : CharacterCouponTransport character first middle)
      (right : CharacterCouponTransport character middle last) :
      CharacterCouponTransport character first last
  | composeLeft
      {W X Y : 𝒞.C}
      (prefixTerm : RibbonExpression 𝒞 W X)
      {before after : RibbonExpression 𝒞 X Y}
      (step : CharacterCouponTransport character before after) :
      CharacterCouponTransport character
        (.compose prefixTerm before)
        (.compose prefixTerm after)
  | composeRight
      {X Y Z : 𝒞.C}
      {before after : RibbonExpression 𝒞 X Y}
      (step : CharacterCouponTransport character before after)
      (suffix : RibbonExpression 𝒞 Y Z) :
      CharacterCouponTransport character
        (.compose before suffix)
        (.compose after suffix)
  | tensorLeft
      {X₁ Y₁ X₂ Y₂ : 𝒞.C}
      (left : RibbonExpression 𝒞 X₁ Y₁)
      {before after : RibbonExpression 𝒞 X₂ Y₂}
      (step : CharacterCouponTransport character before after) :
      CharacterCouponTransport character
        (.tensor left before)
        (.tensor left after)
  | tensorRight
      {X₁ Y₁ X₂ Y₂ : 𝒞.C}
      {before after : RibbonExpression 𝒞 X₁ Y₁}
      (step : CharacterCouponTransport character before after)
      (right : RibbonExpression 𝒞 X₂ Y₂) :
      CharacterCouponTransport character
        (.tensor before right)
        (.tensor after right)
  | addLeft
      {X Y : 𝒞.C}
      (left : RibbonExpression 𝒞 X Y)
      {before after : RibbonExpression 𝒞 X Y}
      (step : CharacterCouponTransport character before after) :
      CharacterCouponTransport character
        (.add left before)
        (.add left after)
  | addRight
      {X Y : 𝒞.C}
      {before after : RibbonExpression 𝒞 X Y}
      (step : CharacterCouponTransport character before after)
      (right : RibbonExpression 𝒞 X Y) :
      CharacterCouponTransport character
        (.add before right)
        (.add after right)
  | smul
      {X Y : 𝒞.C}
      (scalar : K)
      {before after : RibbonExpression 𝒞 X Y}
      (step : CharacterCouponTransport character before after) :
      CharacterCouponTransport character
        (.smul scalar before)
        (.smul scalar after)

theorem CharacterCouponTransport.interpret_eq
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory.{v, uK, uC, uS} K}
    {character : TensorIdentityCharacter (C := 𝒞.C)}
    {X Y : 𝒞.C}
    {before after : RibbonExpression 𝒞 X Y}
    (transport : CharacterCouponTransport character before after) :
    before.interpret = after.interpret := by
  induction transport with
  | naturality f exponent =>
      exact characterCoupon_naturality character f exponent
  | refl term =>
      rfl
  | trans left right leftHypothesis rightHypothesis =>
      exact leftHypothesis.trans rightHypothesis
  | composeLeft prefixTerm step inductionHypothesis =>
      simp only [RibbonExpression.interpret]
      rw [inductionHypothesis]
  | composeRight step suffix inductionHypothesis =>
      simp only [RibbonExpression.interpret]
      rw [inductionHypothesis]
  | tensorLeft left step inductionHypothesis =>
      simp only [RibbonExpression.interpret]
      rw [inductionHypothesis]
  | tensorRight step right inductionHypothesis =>
      simp only [RibbonExpression.interpret]
      rw [inductionHypothesis]
  | addLeft left step inductionHypothesis =>
      simp only [RibbonExpression.interpret]
      rw [inductionHypothesis]
  | addRight step right inductionHypothesis =>
      simp only [RibbonExpression.interpret]
      rw [inductionHypothesis]
  | smul scalar step inductionHypothesis =>
      simp only [RibbonExpression.interpret]
      rw [inductionHypothesis]

/--
A typed one-hole ribbon-expression context.

`RibbonExpressionContext 𝒞 X Y A B` takes an expression `X ⟶ Y` and places it
inside a larger expression `A ⟶ B`.  Every constructor is genuine graphical
syntax; there is no arbitrary function field and no correctness proposition.
-/
inductive RibbonExpressionContext
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory.{v, uK, uC, uS} K)
    (X Y : 𝒞.C) :
    𝒞.C → 𝒞.C → Type (max uK uC uS v)
  | hole :
      RibbonExpressionContext 𝒞 X Y X Y
  | composeLeft {A P Q : 𝒞.C}
      (before : RibbonExpression 𝒞 A P)
      (context : RibbonExpressionContext 𝒞 X Y P Q) :
      RibbonExpressionContext 𝒞 X Y A Q
  | composeRight {P Q B : 𝒞.C}
      (context : RibbonExpressionContext 𝒞 X Y P Q)
      (suffix : RibbonExpression 𝒞 Q B) :
      RibbonExpressionContext 𝒞 X Y P B
  | tensorLeft {A B P Q : 𝒞.C}
      (left : RibbonExpression 𝒞 A B)
      (context : RibbonExpressionContext 𝒞 X Y P Q) :
      RibbonExpressionContext 𝒞 X Y (A ⊗ P) (B ⊗ Q)
  | tensorRight {A B P Q : 𝒞.C}
      (context : RibbonExpressionContext 𝒞 X Y A B)
      (right : RibbonExpression 𝒞 P Q) :
      RibbonExpressionContext 𝒞 X Y (A ⊗ P) (B ⊗ Q)
  | addLeft {A B : 𝒞.C}
      (left : RibbonExpression 𝒞 A B)
      (context : RibbonExpressionContext 𝒞 X Y A B) :
      RibbonExpressionContext 𝒞 X Y A B
  | addRight {A B : 𝒞.C}
      (context : RibbonExpressionContext 𝒞 X Y A B)
      (right : RibbonExpression 𝒞 A B) :
      RibbonExpressionContext 𝒞 X Y A B
  | smul {A B : 𝒞.C}
      (scalar : K)
      (context : RibbonExpressionContext 𝒞 X Y A B) :
      RibbonExpressionContext 𝒞 X Y A B

def RibbonExpressionContext.plug
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory.{v, uK, uC, uS} K}
    {X Y A B : 𝒞.C}
    (context : RibbonExpressionContext 𝒞 X Y A B)
    (term : RibbonExpression 𝒞 X Y) :
    RibbonExpression 𝒞 A B :=
  match context with
  | .hole => term
  | .composeLeft before rest =>
      .compose before (rest.plug term)
  | .composeRight rest suffix =>
      .compose (rest.plug term) suffix
  | .tensorLeft left rest =>
      .tensor left (rest.plug term)
  | .tensorRight rest right =>
      .tensor (rest.plug term) right
  | .addLeft left rest =>
      .add left (rest.plug term)
  | .addRight rest right =>
      .add (rest.plug term) right
  | .smul scalar rest =>
      .smul scalar (rest.plug term)

theorem RibbonExpressionContext.plug_interpret_eq_of_interpret_eq
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory.{v, uK, uC, uS} K}
    {X Y A B : 𝒞.C}
    (context : RibbonExpressionContext 𝒞 X Y A B)
    {left right : RibbonExpression 𝒞 X Y}
    (equality : left.interpret = right.interpret) :
    (context.plug left).interpret = (context.plug right).interpret := by
  induction context with
  | hole => exact equality
  | composeLeft before context inductionHypothesis =>
      simp only [RibbonExpressionContext.plug, RibbonExpression.interpret]
      rw [inductionHypothesis]
  | composeRight context suffix inductionHypothesis =>
      simp only [RibbonExpressionContext.plug, RibbonExpression.interpret]
      rw [inductionHypothesis]
  | tensorLeft left context inductionHypothesis =>
      simp only [RibbonExpressionContext.plug, RibbonExpression.interpret]
      rw [inductionHypothesis]
  | tensorRight context right inductionHypothesis =>
      simp only [RibbonExpressionContext.plug, RibbonExpression.interpret]
      rw [inductionHypothesis]
  | addLeft left context inductionHypothesis =>
      simp only [RibbonExpressionContext.plug, RibbonExpression.interpret]
      rw [inductionHypothesis]
  | addRight context right inductionHypothesis =>
      simp only [RibbonExpressionContext.plug, RibbonExpression.interpret]
      rw [inductionHypothesis]
  | smul scalar context inductionHypothesis =>
      simp only [RibbonExpressionContext.plug, RibbonExpression.interpret]
      rw [inductionHypothesis]

/-!
## Linear one-hole contexts

Representative independence needs an exterior context which is genuinely
linear in the local cut morphism.  The more general context above also has
`addLeft` and `addRight` constructors, so it is affine in its hole.  The
restricted grammar below contains only operations which preserve zero and
addition in the distinguished hole.
-/

/--
A typed one-hole ribbon-expression context that is linear in its hole.

This is graphical syntax, not an arbitrary function and not a correctness
certificate.  In particular, there are no constructors that add a fixed
summand to the hole.
-/
inductive LinearRibbonExpressionContext
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory.{v, uK, uC, uS} K)
    (X Y : 𝒞.C) :
    𝒞.C → 𝒞.C → Type (max uK uC uS v)
  | hole :
      LinearRibbonExpressionContext 𝒞 X Y X Y
  | composeLeft {A P Q : 𝒞.C}
      (before : RibbonExpression 𝒞 A P)
      (context : LinearRibbonExpressionContext 𝒞 X Y P Q) :
      LinearRibbonExpressionContext 𝒞 X Y A Q
  | composeRight {P Q B : 𝒞.C}
      (context : LinearRibbonExpressionContext 𝒞 X Y P Q)
      (suffix : RibbonExpression 𝒞 Q B) :
      LinearRibbonExpressionContext 𝒞 X Y P B
  | tensorLeft {A B P Q : 𝒞.C}
      (left : RibbonExpression 𝒞 A B)
      (context : LinearRibbonExpressionContext 𝒞 X Y P Q) :
      LinearRibbonExpressionContext 𝒞 X Y (A ⊗ P) (B ⊗ Q)
  | tensorRight {A B P Q : 𝒞.C}
      (context : LinearRibbonExpressionContext 𝒞 X Y A B)
      (right : RibbonExpression 𝒞 P Q) :
      LinearRibbonExpressionContext 𝒞 X Y (A ⊗ P) (B ⊗ Q)

def LinearRibbonExpressionContext.plug
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory.{v, uK, uC, uS} K}
    {X Y A B : 𝒞.C}
    (context : LinearRibbonExpressionContext 𝒞 X Y A B)
    (term : RibbonExpression 𝒞 X Y) :
    RibbonExpression 𝒞 A B :=
  match context with
  | .hole => term
  | .composeLeft before rest =>
      .compose before (rest.plug term)
  | .composeRight rest suffix =>
      .compose (rest.plug term) suffix
  | .tensorLeft left rest =>
      .tensor left (rest.plug term)
  | .tensorRight rest right =>
      .tensor (rest.plug term) right

/-- Interpretation of a linear graphical context as an actual linear map. -/
noncomputable def LinearRibbonExpressionContext.interpretLinearMap
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory.{v, uK, uC, uS} K}
    {X Y A B : 𝒞.C}
    (context : LinearRibbonExpressionContext 𝒞 X Y A B) :
    (X ⟶ Y) →ₗ[K] (A ⟶ B) :=
  match context with
  | .hole => LinearMap.id
  | .composeLeft before rest =>
      { toFun := fun term => before.interpret ≫ rest.interpretLinearMap term
        map_add' := by intro left right; simp
        map_smul' := by intro scalar term; simp }
  | .composeRight rest suffix =>
      { toFun := fun term => rest.interpretLinearMap term ≫ suffix.interpret
        map_add' := by intro left right; simp
        map_smul' := by intro scalar term; simp }
  | .tensorLeft left rest =>
      { toFun := fun term => left.interpret ⊗ₘ rest.interpretLinearMap term
        map_add' := by
          intro first second
          rw [map_add]
          exact MonoidalPreadditive.tensor_add _ _ _
        map_smul' := by
          intro scalar term
          rw [map_smul]
          simp [MonoidalCategory.tensorHom_def] }
  | .tensorRight rest right =>
      { toFun := fun term => rest.interpretLinearMap term ⊗ₘ right.interpret
        map_add' := by
          intro first second
          rw [map_add]
          exact MonoidalPreadditive.add_tensor _ _ _
        map_smul' := by
          intro scalar term
          rw [map_smul]
          simp [MonoidalCategory.tensorHom_def] }

theorem LinearRibbonExpressionContext.plug_interpret
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory.{v, uK, uC, uS} K}
    {X Y A B : 𝒞.C}
    (context : LinearRibbonExpressionContext 𝒞 X Y A B)
    (term : X ⟶ Y) :
    (context.plug (.morphism term)).interpret =
      context.interpretLinearMap term := by
  induction context with
  | hole => rfl
  | composeLeft before context inductionHypothesis =>
      simp only [LinearRibbonExpressionContext.plug,
        RibbonExpression.interpret,
        LinearRibbonExpressionContext.interpretLinearMap]
      rw [inductionHypothesis]
      rfl
  | composeRight context suffix inductionHypothesis =>
      simp only [LinearRibbonExpressionContext.plug,
        RibbonExpression.interpret,
        LinearRibbonExpressionContext.interpretLinearMap]
      rw [inductionHypothesis]
      rfl
  | tensorLeft left context inductionHypothesis =>
      simp only [LinearRibbonExpressionContext.plug,
        RibbonExpression.interpret,
        LinearRibbonExpressionContext.interpretLinearMap]
      rw [inductionHypothesis]
      rfl
  | tensorRight context right inductionHypothesis =>
      simp only [LinearRibbonExpressionContext.plug,
        RibbonExpression.interpret,
        LinearRibbonExpressionContext.interpretLinearMap]
      rw [inductionHypothesis]
      rfl

/-- The tensor-product object resolved by one standard fusion expansion. -/
def fusionPairObject
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (left right : 𝒞.simples.Simple) : 𝒞.C :=
  𝒞.simples.simpleObject left ⊗ 𝒞.simples.simpleObject right

/-- The chosen finite simple decomposition of one tensor product. -/
noncomputable def fusionDecomposition
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (left right : 𝒞.simples.Simple) :
    FiniteSimpleDecomposition (fusionPairObject 𝒞 left right) :=
  𝒞.decomposition (fusionPairObject 𝒞 left right)

abbrev FusionChannel
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (left right : 𝒞.simples.Simple) :=
  (fusionDecomposition 𝒞 left right).SummandIndex

def fusionInclusionExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (left right : 𝒞.simples.Simple)
    (channel : FusionChannel 𝒞 left right) :
    RibbonExpression 𝒞
      ((fusionDecomposition 𝒞 left right).summandObject channel)
      (fusionPairObject 𝒞 left right) :=
  .morphism ((fusionDecomposition 𝒞 left right).inclusion channel)

def fusionProjectionExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (left right : 𝒞.simples.Simple)
    (channel : FusionChannel 𝒞 left right) :
    RibbonExpression 𝒞
      (fusionPairObject 𝒞 left right)
      ((fusionDecomposition 𝒞 left right).summandObject channel) :=
  .morphism ((fusionDecomposition 𝒞 left right).projection channel)

/-- The tensor unit, exposed without notation for dependent signatures. -/
def categoryUnitObject
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) : 𝒞.C :=
  𝟙_ 𝒞.C

/--
The explicit complete fusion-channel resolution of the identity on
`left ⊗ right`.
-/
def fusionResolutionExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (left right : 𝒞.simples.Simple) :
    RibbonExpression 𝒞
      (fusionPairObject 𝒞 left right)
      (fusionPairObject 𝒞 left right) :=
  .morphism
    (∑ channel : FusionChannel 𝒞 left right,
      (fusionDecomposition 𝒞 left right).projection channel ≫
        (fusionDecomposition 𝒞 left right).inclusion channel)

theorem fusionResolutionExpression_interpret
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (left right : 𝒞.simples.Simple) :
    (fusionResolutionExpression 𝒞 left right).interpret =
      (identityExpression 𝒞
        (fusionPairObject 𝒞 left right)).interpret := by
  exact (fusionDecomposition 𝒞 left right).resolution_identity

/--
The tensor-unit summand projector of an object, derived from the chosen
semisimple decomposition.
-/
def IsTensorUnitSummand
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (X : 𝒞.C) (i : (𝒞.decomposition X).SummandIndex) : Prop :=
  Nonempty ((𝒞.decomposition X).summandObject i ≅ 𝟙_ 𝒞.C)

def tensorUnitProjector
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (X : 𝒞.C) : X ⟶ X := by
  classical
  exact
    ∑ i : (𝒞.decomposition X).SummandIndex,
      if IsTensorUnitSummand 𝒞 X i then
        (𝒞.decomposition X).projection i ≫
          (𝒞.decomposition X).inclusion i
      else 0

/--
On a chosen simple representative, the tensor-unit projector is the identity
exactly for the tensor-unit label and zero for every other label.
-/
theorem tensorUnitProjector_simple
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple) :
    tensorUnitProjector 𝒞 (𝒞.simples.simpleObject simple) =
      if simple = 𝒞.simples.tensorUnit then
        𝟙 (𝒞.simples.simpleObject simple)
      else
        0 := by
  classical
  let X := 𝒞.simples.simpleObject simple
  let decomposition := 𝒞.decomposition X
  have summandIso (i : decomposition.SummandIndex) :
      Nonempty (decomposition.summandObject i ≅ X) := by
    letI : CategoryTheory.Simple (decomposition.summandObject i) :=
      decomposition.summand_isSimple i
    letI : CategoryTheory.Simple X := 𝒞.simples.simple_isSimple simple
    have inclusion_ne_zero : decomposition.inclusion i ≠ 0 := by
      intro inclusion_zero
      have identity_zero : 𝟙 (decomposition.summandObject i) = 0 := by
        rw [← decomposition.pairing_same i, inclusion_zero,
          CategoryTheory.Limits.zero_comp]
      exact CategoryTheory.id_nonzero _ identity_zero
    letI : IsIso (decomposition.inclusion i) :=
      CategoryTheory.isIso_of_hom_simple inclusion_ne_zero
    exact ⟨asIso (decomposition.inclusion i)⟩
  have unitSummand_iff (i : decomposition.SummandIndex) :
      IsTensorUnitSummand 𝒞 X i ↔ simple = 𝒞.simples.tensorUnit := by
    constructor
    · rintro ⟨summandToUnit⟩
      obtain ⟨summandToX⟩ := summandIso i
      apply 𝒞.simples.simple_pairwise
      exact ⟨summandToX.symm ≪≫ summandToUnit ≪≫ 𝒞.simples.unitIso.symm⟩
    · intro unitCase
      subst simple
      obtain ⟨summandToX⟩ := summandIso i
      exact ⟨summandToX ≪≫ 𝒞.simples.unitIso⟩
  by_cases unitCase : simple = 𝒞.simples.tensorUnit
  · simp only [unitCase, if_pos]
    unfold tensorUnitProjector
    change
      (∑ i : decomposition.SummandIndex,
        if IsTensorUnitSummand 𝒞 X i then
          decomposition.projection i ≫ decomposition.inclusion i else 0) = 𝟙 X
    rw [show
      (∑ i : decomposition.SummandIndex,
        if IsTensorUnitSummand 𝒞 X i then
          decomposition.projection i ≫ decomposition.inclusion i else 0) =
        ∑ i : decomposition.SummandIndex,
          decomposition.projection i ≫ decomposition.inclusion i by
      apply Finset.sum_congr rfl
      intro i _
      rw [if_pos ((unitSummand_iff i).2 unitCase)]]
    exact decomposition.resolution_identity
  · simp only [unitCase, if_false]
    unfold tensorUnitProjector
    change
      (∑ i : decomposition.SummandIndex,
        if IsTensorUnitSummand 𝒞 X i then
          decomposition.projection i ≫ decomposition.inclusion i else 0) = 0
    apply Finset.sum_eq_zero
    intro i _
    have notUnitSummand : ¬ IsTensorUnitSummand 𝒞 X i :=
      fun isUnit => unitCase ((unitSummand_iff i).1 isUnit)
    rw [if_neg notUnitSummand]

/--
Close one endomorphism using the pivotal trace of the canonical spherical
structure induced by the input ribbon structure. Thus the evaluator uses the
EGNO ribbon-to-spherical construction rather than maintaining a second trace
convention.
-/
noncomputable def ribbonTraceMorphism
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple)
    (endomorphism :
      𝒞.simples.simpleObject simple ⟶
        𝒞.simples.simpleObject simple) :
    𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C :=
  𝒞.canonicalRibbonTrace endomorphism

theorem ribbonTraceMorphism_identity
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple) :
    ribbonTraceMorphism 𝒞 simple
        (𝟙 (𝒞.simples.simpleObject simple)) =
      𝒞.simples.quantumDimension simple • 𝟙 (𝟙_ 𝒞.C) := by
  exact 𝒞.canonicalRibbonTrace_identity simple

theorem ribbonTraceMorphism_zero
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple) :
    ribbonTraceMorphism 𝒞 simple 0 = 0 := by
  exact 𝒞.canonicalRibbonTrace_zero
    (𝒞.simples.simpleObject simple)

/-- The closed local value of one dotted cut around a simple meridian. -/
noncomputable def specialCutMeridianClosedValue
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple) : K :=
  𝒞.closedScalar
    (ribbonTraceMorphism 𝒞 simple
      (tensorUnitProjector 𝒞
        (𝒞.simples.simpleObject simple)))

theorem specialCutMeridianClosedValue_eq
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple) :
    specialCutMeridianClosedValue 𝒞 simple =
      if simple = 𝒞.simples.tensorUnit then
        𝒞.simples.quantumDimension 𝒞.simples.tensorUnit
      else 0 := by
  classical
  rw [specialCutMeridianClosedValue, tensorUnitProjector_simple]
  by_cases unitCase : simple = 𝒞.simples.tensorUnit
  · subst simple
    simp only [if_pos]
    rw [ribbonTraceMorphism_identity]
    exact 𝒞.closedScalar_smul_identity _
  · simp only [unitCase, if_false]
    rw [ribbonTraceMorphism_zero]
    exact map_zero 𝒞.unitEndLinearEquiv.symm

theorem specialCutMeridianSum_eq_one
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (unitQuantumDimension :
      𝒞.simples.quantumDimension 𝒞.simples.tensorUnit = 1) :
    (∑ simple : 𝒞.simples.Simple,
      𝒞.simples.quantumDimension simple *
        specialCutMeridianClosedValue 𝒞 simple) = 1 := by
  classical
  simp [specialCutMeridianClosedValue_eq, unitQuantumDimension]

theorem ordinaryKirbyLoopSum_eq_globalDimension
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) :
    (∑ simple : 𝒞.simples.Simple,
      𝒞.simples.quantumDimension simple *
        𝒞.closedScalar
          (ribbonTraceMorphism 𝒞 simple
            (𝟙 (𝒞.simples.simpleObject simple)))) =
      𝒞.globalDimension := by
  classical
  apply Finset.sum_congr rfl
  intro simple _
  rw [ribbonTraceMorphism_identity]
  rw [𝒞.closedScalar_smul_identity]
  rw [𝒞.simples_quantumDimension_eq simple]

/-- The local closed graph for a canceling dotted-one/two-handle pair. -/
noncomputable def specialCutMeridianExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple) :
    RibbonExpression 𝒞 (𝟙_ 𝒞.C) (𝟙_ 𝒞.C) :=
  .morphism
    (ribbonTraceMorphism 𝒞 simple
      (tensorUnitProjector 𝒞
        (𝒞.simples.simpleObject simple)))

/-- The local closed graph for an ordinary zero-framed Kirby-coloured loop. -/
noncomputable def ordinaryKirbyLoopExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (simple : 𝒞.simples.Simple) :
    RibbonExpression 𝒞 (𝟙_ 𝒞.C) (𝟙_ 𝒞.C) :=
  .morphism
    (ribbonTraceMorphism 𝒞 simple
      (𝟙 (𝒞.simples.simpleObject simple)))

/--
Compose two closed graphical expressions.  This is the typed closed-diagram
operation used for a local cancellation factor followed by its unchanged
exterior.
-/
def closedComposeExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (localTerm exterior :
      RibbonExpression 𝒞 (𝟙_ 𝒞.C) (𝟙_ 𝒞.C)) :
    RibbonExpression 𝒞 (𝟙_ 𝒞.C) (𝟙_ 𝒞.C) :=
  .compose localTerm exterior

theorem closedComposeExpression_scalar
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (localTerm exterior :
      RibbonExpression 𝒞 (𝟙_ 𝒞.C) (𝟙_ 𝒞.C)) :
    𝒞.closedScalar
        (closedComposeExpression localTerm exterior).interpret =
      𝒞.closedScalar localTerm.interpret *
        𝒞.closedScalar exterior.interpret := by
  exact 𝒞.closedScalar_comp localTerm.interpret exterior.interpret

/-- A forward character coupon disappears immediately before the unit projector. -/
theorem character_hom_tensorUnitProjector_left
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (X : 𝒞.C) :
    character.iso.hom.app X ≫ tensorUnitProjector 𝒞 X =
      tensorUnitProjector 𝒞 X := by
  classical
  unfold tensorUnitProjector
  have distribute :
    character.iso.hom.app X ≫
        (∑ i : (𝒞.decomposition X).SummandIndex,
          if IsTensorUnitSummand 𝒞 X i then
            (𝒞.decomposition X).projection i ≫
              (𝒞.decomposition X).inclusion i else 0) =
      ∑ i : (𝒞.decomposition X).SummandIndex,
        character.iso.hom.app X ≫
          (if IsTensorUnitSummand 𝒞 X i then
            (𝒞.decomposition X).projection i ≫
              (𝒞.decomposition X).inclusion i else 0) := by
    simpa using Preadditive.comp_sum (Finset.univ)
      (character.iso.hom.app X)
      (fun i : (𝒞.decomposition X).SummandIndex =>
        if IsTensorUnitSummand 𝒞 X i then
          (𝒞.decomposition X).projection i ≫
            (𝒞.decomposition X).inclusion i else 0)
  refine distribute.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with isUnit
  · obtain ⟨unitIso⟩ := isUnit
    have characterOnSummand :
        character.iso.hom.app ((𝒞.decomposition X).summandObject i) =
          𝟙 ((𝒞.decomposition X).summandObject i) := by
      apply (cancel_mono unitIso.hom).1
      simpa [CategoryTheory.TensorIdentityCharacter.unit_hom character] using
        (character.iso.hom.naturality unitIso.hom).symm
    have naturalityAtProjection :
        character.iso.hom.app X ≫ (𝒞.decomposition X).projection i =
          (𝒞.decomposition X).projection i ≫
            character.iso.hom.app ((𝒞.decomposition X).summandObject i) := by
      simpa using (character.iso.hom.naturality
        ((𝒞.decomposition X).projection i)).symm
    rw [← Category.assoc, naturalityAtProjection]
    rw [characterOnSummand]
    simp
  · simp only [CategoryTheory.Limits.comp_zero]
    rfl

/-- An inverse character coupon disappears immediately before the unit projector. -/
theorem character_inv_tensorUnitProjector_left
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (X : 𝒞.C) :
    character.iso.inv.app X ≫ tensorUnitProjector 𝒞 X =
      tensorUnitProjector 𝒞 X := by
  classical
  unfold tensorUnitProjector
  have distribute :
    character.iso.inv.app X ≫
        (∑ i : (𝒞.decomposition X).SummandIndex,
          if IsTensorUnitSummand 𝒞 X i then
            (𝒞.decomposition X).projection i ≫
              (𝒞.decomposition X).inclusion i else 0) =
      ∑ i : (𝒞.decomposition X).SummandIndex,
        character.iso.inv.app X ≫
          (if IsTensorUnitSummand 𝒞 X i then
            (𝒞.decomposition X).projection i ≫
              (𝒞.decomposition X).inclusion i else 0) := by
    simpa using Preadditive.comp_sum (Finset.univ)
      (character.iso.inv.app X)
      (fun i : (𝒞.decomposition X).SummandIndex =>
        if IsTensorUnitSummand 𝒞 X i then
          (𝒞.decomposition X).projection i ≫
            (𝒞.decomposition X).inclusion i else 0)
  refine distribute.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with isUnit
  · obtain ⟨unitIso⟩ := isUnit
    have characterOnSummand :
        character.iso.inv.app ((𝒞.decomposition X).summandObject i) =
          𝟙 ((𝒞.decomposition X).summandObject i) := by
      apply (cancel_mono unitIso.hom).1
      have inverseUnit : character.iso.inv.app (𝟙_ 𝒞.C) = 𝟙 (𝟙_ 𝒞.C) := by
        rw [← cancel_epi (character.iso.hom.app (𝟙_ 𝒞.C))]
        rw [character.iso.hom_inv_id_app]
        simp [CategoryTheory.TensorIdentityCharacter.unit_hom character]
      simpa [inverseUnit] using
        (character.iso.inv.naturality unitIso.hom).symm
    have naturalityAtProjection :
        character.iso.inv.app X ≫ (𝒞.decomposition X).projection i =
          (𝒞.decomposition X).projection i ≫
            character.iso.inv.app ((𝒞.decomposition X).summandObject i) := by
      simpa using (character.iso.inv.naturality
        ((𝒞.decomposition X).projection i)).symm
    rw [← Category.assoc, naturalityAtProjection]
    rw [characterOnSummand]
    simp
  · simp only [CategoryTheory.Limits.comp_zero]
    rfl

/-- A finite power remains invisible whenever one copy is absorbed. -/
private theorem isoNatPowerHom_absorbed
    {C : Type uC} [Category.{v} C]
    {X : C}
    (iso : X ≅ X)
    (projector : X ⟶ X)
    (absorbed : iso.hom ≫ projector = projector)
    (power : ℕ) :
    isoNatPowerHom iso power ≫ projector = projector := by
  induction power with
  | zero => simp [isoNatPowerHom]
  | succ power ih =>
      simp only [isoNatPowerHom]
      rw [Category.assoc, absorbed]
      exact ih

/-- Every integral character power disappears before the unit projector. -/
theorem characterCoupon_tensorUnitProjector_left
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (X : 𝒞.C)
    (exponent : ℤ) :
    isoIntPowerHom (character.iso.app X) exponent ≫
        tensorUnitProjector 𝒞 X =
      tensorUnitProjector 𝒞 X := by
  cases exponent with
  | ofNat n =>
      exact isoNatPowerHom_absorbed
        (character.iso.app X)
        (tensorUnitProjector 𝒞 X)
        (character_hom_tensorUnitProjector_left character X)
        n
  | negSucc n =>
      exact isoNatPowerHom_absorbed
        (character.iso.app X).symm
        (tensorUnitProjector 𝒞 X)
        (character_inv_tensorUnitProjector_left character X)
        (n + 1)

def tensorUnitProjectorExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 X X :=
  .morphism (tensorUnitProjector 𝒞 X)

abbrev ClosedRibbonExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) :=
  RibbonExpression 𝒞 (𝟙_ 𝒞.C) (𝟙_ 𝒞.C)

/--
Canonical evaluation of a closed expression.  No caller supplies an evaluator.
-/
noncomputable def canonicalRibbonGraphicalEvaluation
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (expression : ClosedRibbonExpression 𝒞) : K :=
  𝒞.closedScalar expression.interpret

end

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 122
