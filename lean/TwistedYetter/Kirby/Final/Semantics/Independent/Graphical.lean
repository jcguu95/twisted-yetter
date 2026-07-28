import TwistedYetter.Kirby.Final.Semantics.Independent.Algebra

/-!
# Independent semantics: typed ribbon graphical calculus

This syntax is deliberately smaller than a planar parser.  It records the
typed ribbon operations that the combinatorial diagram compiler may emit.
General morphism coupons are first-class generators.
-/

namespace TwistedYetter.Semantics.Independent

inductive RibbonDirection
  | forward
  | dual
  deriving DecidableEq, Repr

inductive RibbonCrossingSign
  | positive
  | negative
  deriving DecidableEq, Repr

structure OrientedSimple
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) where
  label : 𝒞.simples.Simple
  direction : RibbonDirection

def RibbonWord
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :=
  List (OrientedSimple 𝒞)

inductive RibbonGenerator
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
  | identity (word : RibbonWord 𝒞)
  | crossing
      (overStrand underStrand : OrientedSimple 𝒞)
      (sign : RibbonCrossingSign)
  | cup (label : 𝒞.simples.Simple)
  | cap (label : 𝒞.simples.Simple)
  | twist (strand : OrientedSimple 𝒞) (sign : RibbonCrossingSign)
  | coupon
      (name : String)
      (source target : RibbonWord 𝒞)
  | characterCoupon
      (label : 𝒞.simples.Simple)
      (exponent : ℤ)
  | fusionInclusion
      (left right output : 𝒞.simples.Simple)
      (multiplicityIndex :
        Fin (𝒞.simples.fusionMultiplicity left right output))
  | fusionProjection
      (left right output : 𝒞.simples.Simple)
      (multiplicityIndex :
        Fin (𝒞.simples.fusionMultiplicity left right output))
  | tensorUnitProjector (label : 𝒞.simples.Simple)

inductive RibbonExpression
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K)
  | generator (term : RibbonGenerator 𝒞)
  | compose (first second : RibbonExpression 𝒞)
  | tensor (left right : RibbonExpression 𝒞)
  | finiteSum (terms : List (K × RibbonExpression 𝒞))

opaque CompositionRespectsEvaluation
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    (evaluate : RibbonExpression 𝒞 → K) : Prop

opaque TensorRespectsEvaluation
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    (evaluate : RibbonExpression 𝒞 → K) : Prop

opaque FiniteSumRespectsEvaluation
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    (evaluate : RibbonExpression 𝒞 → K) : Prop

opaque BraidingNaturalityLaw
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    (evaluate : RibbonExpression 𝒞 → K) : Prop

opaque CupCapNaturalityLaw
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    (evaluate : RibbonExpression 𝒞 → K) : Prop

opaque TwistNaturalityLaw
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    (evaluate : RibbonExpression 𝒞 → K) : Prop

opaque CouponNaturalityLaw
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    (evaluate : RibbonExpression 𝒞 → K) : Prop

opaque FusionCompletenessLaw
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    (evaluate : RibbonExpression 𝒞 → K) : Prop

opaque TensorUnitProjectorLaw
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    (evaluate : RibbonExpression 𝒞 → K) : Prop

/--
An interpretation of the independent graphical syntax.  The listed laws are
the exact theorem obligations expected from a premodular ribbon calculus;
they are not Kirby-move or evaluator equalities.
-/
structure RibbonGraphicalEvaluation
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) where
  evaluate : RibbonExpression 𝒞 → K
  compositionRespectsEvaluation :
    CompositionRespectsEvaluation evaluate
  tensorRespectsEvaluation :
    TensorRespectsEvaluation evaluate
  finiteSumRespectsEvaluation :
    FiniteSumRespectsEvaluation evaluate
  braidingNaturality :
    BraidingNaturalityLaw evaluate
  cupCapNaturality :
    CupCapNaturalityLaw evaluate
  twistNaturality :
    TwistNaturalityLaw evaluate
  couponNaturality :
    CouponNaturalityLaw evaluate
  fusionCompleteness :
    FusionCompletenessLaw evaluate
  tensorUnitProjectorLaw :
    TensorUnitProjectorLaw evaluate

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 2344
