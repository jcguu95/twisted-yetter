import TwistedYetter.Kirby.Final.Semantics.Independent.Algebra

/-!
# Independent semantics: typed ribbon graphical calculus

Every expression is indexed by its categorical source and target.  General
coupons contain actual morphisms; names and parser identifiers are not part of
their mathematical meaning.  Closed evaluation is derived by interpreting the
expression as an endomorphism of the tensor unit and then applying Schur
scalarization.

The sole external graphical theorem is Shum's coherence theorem for ribbon
categories:

M.-C. Shum, *Tortile tensor categories*, Journal of Pure and Applied Algebra
93 (1994), Theorem 2.6.
-/

namespace TwistedYetter.Semantics.Independent

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe uK uC uS v

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
    (𝒞 : PremodularFusionCategory K) where
  label : 𝒞.simples.Simple
  direction : RibbonDirection

def RibbonWord
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :=
  List (OrientedSimple 𝒞)

def orientedSimpleObject
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (strand : OrientedSimple 𝒞) : 𝒞.C :=
  match strand.direction with
  | .forward => 𝒞.simples.simpleObject strand.label
  | .dual => (𝒞.simples.simpleObject strand.label)ᘁ

def ribbonWordObject
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
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
    (𝒞 : PremodularFusionCategory.{uK, uC, v, uS} K) :
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
    {𝒞 : PremodularFusionCategory K}
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
    (𝒞 : PremodularFusionCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 X X :=
  .morphism (𝟙 X)

def positiveCrossing
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (X Y : 𝒞.C) :
    RibbonExpression 𝒞 (X ⊗ Y) (Y ⊗ X) :=
  .morphism (β_ X Y).hom

def negativeCrossing
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (X Y : 𝒞.C) :
    RibbonExpression 𝒞 (X ⊗ Y) (Y ⊗ X) :=
  .morphism (β_ Y X).inv

def coevaluationExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 (𝟙_ 𝒞.C) (X ⊗ Xᘁ) :=
  .morphism (η_ X (Xᘁ))

def evaluationExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 (Xᘁ ⊗ X) (𝟙_ 𝒞.C) :=
  .morphism (ε_ X (Xᘁ))

def positiveTwist
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 X X :=
  .morphism (𝒞.ribbon.twist.hom.app X)

def negativeTwist
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 X X :=
  .morphism (𝒞.ribbon.twist.inv.app X)

/-- A general coupon is an actual categorical morphism. -/
def morphismCoupon
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
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

/-- The actual character morphism on an arbitrary object. -/
def characterCoupon
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    (character : TensorIdentityCharacter 𝒞)
    (X : 𝒞.C)
    (exponent : ℤ) :
    RibbonExpression 𝒞 X X :=
  .morphism (isoIntPowerHom (character.iso.app X) exponent)

private theorem characterCoupon_natPower_naturality
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    (character : TensorIdentityCharacter 𝒞)
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
    {𝒞 : PremodularFusionCategory K}
    (character : TensorIdentityCharacter 𝒞)
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
    {𝒞 : PremodularFusionCategory K}
    (character : TensorIdentityCharacter 𝒞)
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
    {𝒞 : PremodularFusionCategory.{uK, uC, v, uS} K}
    (character : TensorIdentityCharacter 𝒞) :
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
    {𝒞 : PremodularFusionCategory.{uK, uC, v, uS} K}
    {character : TensorIdentityCharacter 𝒞}
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

def fusionInclusionExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (left right output : 𝒞.simples.Simple)
    (i : Fin (𝒞.fusionMultiplicity left right output)) :
    RibbonExpression 𝒞
      (𝒞.simples.simpleObject output)
      (𝒞.simples.simpleObject left ⊗ 𝒞.simples.simpleObject right) :=
  .morphism (𝒞.fusionInclusion left right output i)

def fusionProjectionExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (left right output : 𝒞.simples.Simple)
    (i : Fin (𝒞.fusionMultiplicity left right output)) :
    RibbonExpression 𝒞
      (𝒞.simples.simpleObject left ⊗ 𝒞.simples.simpleObject right)
      (𝒞.simples.simpleObject output) :=
  .morphism (𝒞.fusionProjection left right output i)

/--
The tensor-unit summand projector of an object, derived from the chosen
semisimple decomposition.
-/
def tensorUnitProjector
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (X : 𝒞.C) : X ⟶ X :=
  ∑ i : Fin (𝒞.simples.multiplicity X 𝒞.simples.tensorUnit),
    𝒞.simples.summandProjection X ⟨𝒞.simples.tensorUnit, i⟩ ≫
      𝒞.simples.summandInclusion X ⟨𝒞.simples.tensorUnit, i⟩

def tensorUnitProjectorExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (X : 𝒞.C) :
    RibbonExpression 𝒞 X X :=
  .morphism (tensorUnitProjector 𝒞 X)

abbrev ClosedRibbonExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :=
  RibbonExpression 𝒞 (𝟙_ 𝒞.C) (𝟙_ 𝒞.C)

/--
Canonical evaluation of a closed expression.  No caller supplies an evaluator.
-/
noncomputable def canonicalRibbonGraphicalEvaluation
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
    (expression : ClosedRibbonExpression 𝒞) : K :=
  𝒞.closedScalar expression.interpret

/--
Category-level relation saying that two typed expressions represent framed
isotopic ribbon diagrams with the same boundary.

This relation is category-neutral and does not mention scalar evaluation.
-/
opaque FramedRibbonIsotopic
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    {X Y : 𝒞.C} :
    RibbonExpression 𝒞 X Y → RibbonExpression 𝒞 X Y → Prop

/--
Shum 1994, Theorem 2.6: framed-isotopic typed ribbon diagrams determine the
same morphism in a ribbon category.
-/
axiom shum_framedRibbonCoherence
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    {X Y : 𝒞.C}
    {left right : RibbonExpression 𝒞 X Y} :
    FramedRibbonIsotopic left right →
    left.interpret = right.interpret

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 93
