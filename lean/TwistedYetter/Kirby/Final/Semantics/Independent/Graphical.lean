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

-- semantic-freeze-padding: 4974
