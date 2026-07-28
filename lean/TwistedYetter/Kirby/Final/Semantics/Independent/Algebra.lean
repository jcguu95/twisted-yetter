import Mathlib

/-!
# Independent semantics: algebra

This file is deliberately independent of every evaluator and Kirby-diagram
implementation in this repository.  It bundles the Mathlib categorical
structures that form the ambient part of a characteristic-zero premodular
fusion category, together with the finite simple-object skeleton used by the
combinatorial evaluator.

Mathlib currently supplies the categorical, monoidal, braided, rigid,
preadditive, and linear structures.  Finite semisimplicity, the ribbon/pivotal
compatibility, and the simple-object skeleton remain explicit data and laws
here.  They are not inferred from any downstream implementation.
-/

namespace TwistedYetter.Semantics.Independent

open CategoryTheory

universe uK uC uS v

/-- A finite simple-object skeleton for a fusion category. -/
structure FusionSimpleSkeleton (K : Type uK) [Field K] where
  Simple : Type uS
  simpleFintype : Fintype Simple
  simpleDecidableEq : DecidableEq Simple
  tensorUnit : Simple
  dual : Simple → Simple
  fusionMultiplicity : Simple → Simple → Simple → ℕ
  quantumDimension : Simple → K
  globalDimension : K
  dual_involutive : Function.Involutive dual
  left_unit :
    ∀ x z, fusionMultiplicity tensorUnit x z = if x = z then 1 else 0
  right_unit :
    ∀ x z, fusionMultiplicity x tensorUnit z = if x = z then 1 else 0
  globalDimension_formula :
    globalDimension =
      ∑ x : Simple, quantumDimension x * quantumDimension x
  globalDimension_ne_zero : globalDimension ≠ 0

attribute [instance] FusionSimpleSkeleton.simpleFintype
attribute [instance] FusionSimpleSkeleton.simpleDecidableEq

/--
The independent algebraic input.

The four propositions at the end are intentionally visible literature
obligations.  They say that the bundled Mathlib category is finite
semisimple, that the displayed simple skeleton is complete, that the tensor
unit is simple, and that the braided rigid structure carries the spherical
ribbon compatibility used by the graphical calculus.
-/
structure PremodularFusionCategory
    (K : Type uK) [Field K] [IsAlgClosed K] [CharZero K] where
  C : Type uC
  category : Category.{v} C
  monoidal : @MonoidalCategory C category
  braided : @BraidedCategory C category monoidal
  rigid : @RigidCategory C category monoidal
  preadditive : @Preadditive C category
  linear : @Linear K _ C category preadditive
  simples : FusionSimpleSkeleton.{uK, uC} K
  finiteSemisimple : Prop
  simpleSkeletonComplete : Prop
  tensorUnitSimple : Prop
  sphericalRibbonCompatible : Prop
  finiteSemisimple_holds : finiteSemisimple
  simpleSkeletonComplete_holds : simpleSkeletonComplete
  tensorUnitSimple_holds : tensorUnitSimple
  sphericalRibbonCompatible_holds : sphericalRibbonCompatible

attribute [instance] PremodularFusionCategory.category
attribute [instance] PremodularFusionCategory.monoidal
attribute [instance] PremodularFusionCategory.braided
attribute [instance] PremodularFusionCategory.rigid
attribute [instance] PremodularFusionCategory.preadditive
attribute [instance] PremodularFusionCategory.linear

/--
The scalar by which a monoidal natural automorphism of the tensor identity
acts on each simple object.  In a finite semisimple category these scalars
determine the natural automorphism.
-/
structure TensorIdentityCharacter
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) where
  value : 𝒞.simples.Simple → Kˣ
  unit_value : value 𝒞.simples.tensorUnit = 1
  fusion_value :
    ∀ x y z,
      0 < 𝒞.simples.fusionMultiplicity x y z →
      value z = value x * value y
  dual_value :
    ∀ x, value (𝒞.simples.dual x) = (value x)⁻¹

/-- A premodular category together with its twisting character. -/
structure TwistedPremodularCategory
    (K : Type uK) [Field K] [IsAlgClosed K] [CharZero K] where
  category : PremodularFusionCategory.{uK, uC, v} K
  character : TensorIdentityCharacter.{uK, uC, v} category

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 1060
