import TwistedYetter.Fusion.EGNOTensorAutomorphism
import TwistedYetter.Kirby.CategoricalTangle
import TwistedYetter.Kirby.ComponentBoundaryCharacter
import TwistedYetter.Kirby.ComponentRibbonDiagram
import TwistedYetter.Kirby.EGNOCategoryBoundSliding
import TwistedYetter.Kirby.LinearContext
import TwistedYetter.Kirby.LinearDiagram

/-!
# Explicit fusion channels for the twisted two-over-two calculation

The edge between the two trivalent coupons is an internal simple fusion
channel, not a new closed Kirby component.  It is therefore indexed by a
simple `z` and a multiplicity coordinate
`μ : Fin (N x y z)`, with unit coefficient in the stored EGNO biproduct
resolution.

This file deliberately does not choose a handle-slide orientation.  The
positive and negative geometric compilers must supply the actual ordered
boundary labels, including duals when required.
-/

namespace TwistedYetter.Kirby.TwoOverTwoFusionChannel

open scoped BigOperators
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentBoundaryCharacter
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.EGNOCategoryBoundSliding
open TwistedYetter.Kirby.LinearContext
open TwistedYetter.Kirby.LinearDiagram
open TwistedYetter.Kirby.ModularVacuumProjector

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance twoOverTwoFusionChannelRightRigid : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/-- The actual object meeting the two trivalent coupons. -/
abbrev TensorObject
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (x y : S) : C :=
  data.simple x ⊗ data.simple y

/--
One internal edge is exactly a simple label `z` together with one basis
coordinate in `Hom(z, x ⊗ y)`.
-/
abbrev Channel
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (x y : S) : Type :=
  data.SummandIndex (TensorObject data x y)

/-- The simple label carried by one internal fusion edge. -/
def Channel.simpleLabel
    {data : FusionCategoryData (K := K) (C := C) (S := S)}
    {x y : S}
    (channel : Channel data x y) : S :=
  channel.1

/-- The multiplicity coordinate carried by one internal fusion edge. -/
def Channel.multiplicityIndex
    {data : FusionCategoryData (K := K) (C := C) (S := S)}
    {x y : S}
    (channel : Channel data x y) :
    Fin (data.fusionMultiplicity x y channel.1) := by
  change Fin (data.multiplicity (TensorObject data x y) channel.1)
  exact channel.2

/--
The two original character coupons.  They remain separate here because two
different exponents do not canonically define one integral power on `z`.
-/
noncomputable def tensorCharacterCoupon
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) :
    TensorObject data x y ⟶ TensorObject data x y :=
  data.automorphismCouponPower η x xExponent ⊗ₘ
    data.automorphismCouponPower η y yExponent

/-- Scalar carried by every `(z, μ)` channel for fixed `x`, `y`. -/
noncomputable def mixedCharacterScalar
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) : K :=
  data.automorphismScalarPower η x xExponent *
    data.automorphismScalarPower η y yExponent

/--
One explicit `z, μ` channel: project `x ⊗ y` to `z`, place the mixed
character scalar on that edge, and include it back into `x ⊗ y`.
-/
noncomputable def channelMorphism
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ)
    (channel : Channel data x y) :
    TensorObject data x y ⟶ TensorObject data x y :=
  data.projection (TensorObject data x y) channel ≫
    (mixedCharacterScalar data η x y xExponent yExponent •
      𝟙 (data.simple channel.simpleLabel)) ≫
    data.inclusion (TensorObject data x y) channel

/-- The same channel as a visible two-trivalent-coupon diagram. -/
noncomputable def channelDiagram
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ)
    (channel : Channel data x y) :
    Diagram C
      (.atom (TensorObject data x y))
      (.atom (TensorObject data x y)) :=
  atomicCoupon "fusion-projection"
      (data.projection (TensorObject data x y) channel) ≫ᵈ
    atomicCoupon "mixed-character-on-fusion-channel"
      (mixedCharacterScalar data η x y xExponent yExponent •
        𝟙 (data.simple channel.simpleLabel)) ≫ᵈ
    atomicCoupon "fusion-inclusion"
      (data.inclusion (TensorObject data x y) channel)

/-- Complete explicit sum over all simple labels and multiplicity indices. -/
noncomputable def resolvedCharacterDiagram
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) :
    LinearDiagram (R := K) (C := C)
      (.atom (TensorObject data x y))
      (.atom (TensorObject data x y)) :=
  ∑ channel : Channel data x y,
    LinearDiagram.atom (R := K)
      (channelDiagram data η x y xExponent yExponent channel)

/-- The two original coupons are the product scalar on `x ⊗ y`. -/
theorem tensorCharacterCoupon_eq_smul_identity
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) :
    tensorCharacterCoupon data η x y xExponent yExponent =
      mixedCharacterScalar data η x y xExponent yExponent •
        𝟙 (TensorObject data x y) := by
  rw [tensorCharacterCoupon,
    data.automorphismCouponPower_eq_smul_identity,
    data.automorphismCouponPower_eq_smul_identity]
  simpa [mixedCharacterScalar, TensorObject, tensorHom_def', mul_smul]

/-- Evaluation of one visible channel is its categorical channel morphism. -/
@[simp]
theorem channelDiagram_eval
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ)
    (channel : Channel data x y) :
    Diagram.eval C
        (channelDiagram data η x y xExponent yExponent channel) =
      channelMorphism data η x y xExponent yExponent channel := by
  rfl

/--
The complete `(z, μ)` channel sum is exactly the original pair of character
coupons.  No extra Kirby-colour factor or independent third-component label
is introduced.
-/
theorem resolvedCharacterDiagram_eval
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) :
    LinearDiagram.eval
        (resolvedCharacterDiagram data η x y xExponent yExponent) =
      tensorCharacterCoupon data η x y xExponent yExponent := by
  classical
  rw [resolvedCharacterDiagram]
  simp only [map_sum, LinearDiagram.eval_atom, channelDiagram_eval]
  rw [tensorCharacterCoupon_eq_smul_identity]
  calc
    (∑ channel : Channel data x y,
        channelMorphism data η x y xExponent yExponent channel) =
      ∑ channel : Channel data x y,
        mixedCharacterScalar data η x y xExponent yExponent •
          (data.projection (TensorObject data x y) channel ≫
            data.inclusion (TensorObject data x y) channel) := by
        apply Finset.sum_congr rfl
        intro channel _
        unfold channelMorphism
        have first :
            data.projection (TensorObject data x y) channel ≫
                (mixedCharacterScalar data η x y xExponent yExponent •
                  𝟙 (data.simple channel.simpleLabel)) =
              mixedCharacterScalar data η x y xExponent yExponent •
                data.projection (TensorObject data x y) channel := by
          simpa only [Category.comp_id] using
            CategoryTheory.Linear.comp_smul
              (TensorObject data x y)
              (data.simple channel.simpleLabel)
              (data.simple channel.simpleLabel)
              (data.projection (TensorObject data x y) channel)
              (mixedCharacterScalar data η x y xExponent yExponent)
              (𝟙 (data.simple channel.simpleLabel))
        rw [← Category.assoc]
        rw [first]
        exact
          CategoryTheory.Linear.smul_comp
            (TensorObject data x y)
            (data.simple channel.simpleLabel)
            (TensorObject data x y)
            (mixedCharacterScalar data η x y xExponent yExponent)
            (data.projection (TensorObject data x y) channel)
            (data.inclusion (TensorObject data x y) channel)
    _ =
      mixedCharacterScalar data η x y xExponent yExponent •
        ∑ channel : Channel data x y,
          data.projection (TensorObject data x y) channel ≫
            data.inclusion (TensorObject data x y) channel := by
        rw [Finset.smul_sum]
    _ =
      mixedCharacterScalar data η x y xExponent yExponent •
        𝟙 (TensorObject data x y) := by
        rw [data.sum_projection_inclusion (TensorObject data x y)]

/-!
## The oriented trace-dual resolution used by the actual 2/2 slide

The generic biproduct resolution above is useful algebra, but the
Bärenz--Barrett slide has a specific orientation.  Its insertion object is
`x ⊗ yᘁ`; its dual basis is normalized by pivotal trace; and consequently the
`z`-channel carries the quantum-dimension factor `d_z`.
-/

section OrientedSlidingResolution

/-- The oriented tensor object at the two trivalent vertices of the slide. -/
abbrev OrientedTensorObject
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (x y : S) : C :=
  data.simple x ⊗ (data.simple y)ᘁ

/--
The actual internal edge: a simple `z` and a basis coordinate in
`Hom(x ⊗ yᘁ, z)`.
-/
abbrev OrientedChannel
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (x y : S) : Type vC :=
  Σ z, data.InsertionIndex
    (data.simple x ⊗ (data.simple y)ᘁ) z

/-- A fixed free boundary realizing the oriented pair `x ⊗ yᘁ`. -/
private def orientedBoundary : ComponentBoundary :=
  .tensor
    (.atom (positiveAtom "two-over-two-left"))
    (.atom (negativeAtom "two-over-two-right"))

/-- Labels for the two distinguished atoms of `orientedBoundary`. -/
private def orientedLabelOf (x y : S) : String → S :=
  fun componentId =>
    if componentId = "two-over-two-left" then x else y

/-- The free oriented boundary interprets to the actual insertion object. -/
private theorem orientedBoundary_interpret
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (x y : S) :
    (orientedBoundary.interpret data (orientedLabelOf x y)).denote =
      OrientedTensorObject data x y := by
  rfl

/--
The two original character coupons on the oriented pair.  Reversing the
orientation of `y` changes exponent `b` to `-b` before taking the right mate.
-/
noncomputable def orientedCharacterCoupon
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) :
    OrientedTensorObject data x y ⟶ OrientedTensorObject data x y :=
  data.toFusionCategoryData.automorphismCouponPower η x xExponent ⊗ₘ
    (data.toFusionCategoryData.automorphismCouponPower
      η y (-yExponent))ᘁ

/-- The scalar represented by the two oriented character coupons. -/
noncomputable def orientedCharacterScalar
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) : K :=
  data.toFusionCategoryData.automorphismScalarPower η x xExponent *
    data.toFusionCategoryData.automorphismScalarPower η y (-yExponent)

/--
On `x ⊗ yᘁ`, one common exponent `n` acts by
`χ_x^n χ_y^{-n}`.  This is derived from monoidality and duality of the
tensor-identity automorphism.
-/
theorem automorphismObjectPower_oriented_eq_smul_identity
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (exponent : ℤ) :
    automorphismObjectPower η
        (OrientedTensorObject data x y) exponent =
      orientedCharacterScalar data η x y exponent exponent •
        𝟙 (OrientedTensorObject data x y) := by
  have boundaryFormula :=
    automorphismObjectPower_eq_boundaryCharacterPower_smul_identity
      data η (orientedLabelOf x y) orientedBoundary exponent
  rw [orientedBoundary_interpret] at boundaryFormula
  simpa [
    boundaryCharacterPower_tensor,
    boundaryCharacterPower_positive,
    boundaryCharacterPower_negative,
    orientedCharacterScalar,
    orientedBoundary,
    orientedLabelOf,
  ] using boundaryFormula

/--
The oriented pair of coupons is exactly
`χ_x^a χ_y^{-b} id_{x ⊗ yᘁ}`.
-/
theorem orientedCharacterCoupon_eq_smul_identity
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) :
    orientedCharacterCoupon data η x y xExponent yExponent =
      orientedCharacterScalar data η x y xExponent yExponent •
        𝟙 (OrientedTensorObject data x y) := by
  rw [orientedCharacterCoupon,
    data.toFusionCategoryData.automorphismCouponPower_eq_smul_identity,
    data.toFusionCategoryData.automorphismCouponPower_eq_smul_identity,
    rightAdjointMate_smul_id]
  simpa [orientedCharacterScalar, OrientedTensorObject, tensorHom_def',
    mul_smul]

/--
One visible trace-dual channel, including the `d_z` coefficient required by
the spherical insertion law.
-/
noncomputable def orientedChannelMorphism
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ)
    (channel : OrientedChannel data x y) :
    OrientedTensorObject data x y ⟶ OrientedTensorObject data x y :=
  data.quantumDimension channel.1 •
    ((CategoryData.slidingForwardBasis data x y channel.1).primal channel.2 ≫
      (orientedCharacterScalar data η x y xExponent yExponent •
        𝟙 (data.simple channel.1)) ≫
      (CategoryData.slidingForwardBasis data x y channel.1).dual channel.2)

/--
After summing every simple channel `z` and every multiplicity coordinate
`μ`, the explicit two-trivalent-vertex expansion is exactly the original
oriented character coupon.
-/
theorem sum_orientedChannelMorphism
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) :
    ∑ channel : OrientedChannel data x y,
        orientedChannelMorphism data η x y
          xExponent yExponent channel =
      orientedCharacterCoupon data η x y xExponent yExponent := by
  classical
  rw [orientedCharacterCoupon_eq_smul_identity]
  rw [show
      (∑ channel : OrientedChannel data x y,
          orientedChannelMorphism data η x y
            xExponent yExponent channel) =
        orientedCharacterScalar data η x y xExponent yExponent •
          (∑ z, ∑ i : data.InsertionIndex
              (data.simple x ⊗ (data.simple y)ᘁ) z,
            data.quantumDimension z •
              ((CategoryData.slidingForwardBasis data x y z).primal i ≫
                (CategoryData.slidingForwardBasis data x y z).dual i)) by
    rw [Fintype.sum_sigma]
    simp only [orientedChannelMorphism, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro i _
    simp only [← Category.assoc]
    rw [CategoryTheory.Linear.comp_smul]
    simp only [Category.comp_id]
    rw [CategoryTheory.Linear.smul_comp]
    simp only [smul_smul]
    rw [mul_comm
      (data.quantumDimension z)
      (orientedCharacterScalar data η x y xExponent yExponent)]]
  rw [CategoryData.slidingForwardSound data insertionLaw x y]

/--
Integral powers of a tensor-identity automorphism remain natural.  This is
proved from the naturality of the forward and inverse components; it is not
an extra graphical law.
-/
theorem automorphismObjectPower_naturality
    (η : TensorIdentityAutomorphism C)
    {X Y : C}
    (f : X ⟶ Y)
    (exponent : ℤ) :
    automorphismObjectPower η X exponent ≫ f =
      f ≫ automorphismObjectPower η Y exponent := by
  let componentX : Aut X := η.iso.app X
  let componentY : Aut Y := η.iso.app Y
  change (componentX ^ exponent).hom ≫ f =
    f ≫ (componentY ^ exponent).hom
  induction exponent using Int.induction_on with
  | zero =>
      change 𝟙 X ≫ f = f ≫ 𝟙 Y
      simp
  | @succ n ih =>
      have hx :
          componentX ^ ((n : ℤ) + 1) =
            componentX ^ (n : ℤ) * componentX := by
        rw [zpow_add, zpow_one]
      have hy :
          componentY ^ ((n : ℤ) + 1) =
            componentY ^ (n : ℤ) * componentY := by
        rw [zpow_add, zpow_one]
      rw [hx, hy, CategoryTheory.Aut.Aut_mul_def,
        CategoryTheory.Aut.Aut_mul_def, Iso.trans_hom, Iso.trans_hom]
      calc
        (componentX.hom ≫ (componentX ^ (n : ℤ)).hom) ≫ f =
            componentX.hom ≫
              ((componentX ^ (n : ℤ)).hom ≫ f) :=
          Category.assoc _ _ _
        _ = componentX.hom ≫
              (f ≫ (componentY ^ (n : ℤ)).hom) := by rw [ih]
        _ = (componentX.hom ≫ f) ≫
              (componentY ^ (n : ℤ)).hom :=
          (Category.assoc _ _ _).symm
        _ = (f ≫ componentY.hom) ≫
              (componentY ^ (n : ℤ)).hom := by
          rw [show componentX.hom ≫ f = f ≫ componentY.hom by
            exact (η.iso.hom.naturality f).symm]
        _ = f ≫
              (componentY.hom ≫ (componentY ^ (n : ℤ)).hom) :=
          Category.assoc _ _ _
  | @pred n ih =>
      have hx :
          componentX ^ (-(n : ℤ) - 1) =
            componentX ^ (-(n : ℤ)) * componentX ^ (-1 : ℤ) := by
        exact zpow_add componentX (-(n : ℤ)) (-1)
      have hy :
          componentY ^ (-(n : ℤ) - 1) =
            componentY ^ (-(n : ℤ)) * componentY ^ (-1 : ℤ) := by
        exact zpow_add componentY (-(n : ℤ)) (-1)
      rw [hx, hy, zpow_neg_one, CategoryTheory.Aut.Aut_mul_def,
        CategoryTheory.Aut.Aut_mul_def, Iso.trans_hom, Iso.trans_hom]
      calc
        ((componentX⁻¹).hom ≫
            (componentX ^ (-(n : ℤ))).hom) ≫ f =
            (componentX⁻¹).hom ≫
              ((componentX ^ (-(n : ℤ))).hom ≫ f) :=
          Category.assoc _ _ _
        _ = (componentX⁻¹).hom ≫
              (f ≫ (componentY ^ (-(n : ℤ))).hom) := by rw [ih]
        _ = ((componentX⁻¹).hom ≫ f) ≫
              (componentY ^ (-(n : ℤ))).hom :=
          (Category.assoc _ _ _).symm
        _ = (f ≫ (componentY⁻¹).hom) ≫
              (componentY ^ (-(n : ℤ))).hom := by
          rw [show (componentX⁻¹).hom ≫ f =
              f ≫ (componentY⁻¹).hom by
            exact (η.iso.inv.naturality f).symm]
        _ = f ≫
              ((componentY ^ (-1 : ℤ)).hom ≫
                (componentY ^ (-(n : ℤ))).hom) := by
          rw [zpow_neg_one]
          exact Category.assoc _ _ _

/--
One oriented trace-dual channel with the actual character coupon `η_z^n`
placed on its internal simple edge.
-/
noncomputable def orientedChannelCouponMorphism
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (exponent : ℤ)
    (channel : OrientedChannel data x y) :
    OrientedTensorObject data x y ⟶ OrientedTensorObject data x y :=
  data.quantumDimension channel.1 •
    ((CategoryData.slidingForwardBasis data x y channel.1).primal channel.2 ≫
      data.toFusionCategoryData.automorphismCouponPower
        η channel.1 exponent ≫
      (CategoryData.slidingForwardBasis data x y channel.1).dual channel.2)

/--
The full `d_z`-weighted channel sum transports the character coupon exactly:
placing `η_z^n` on every internal edge is the same as placing `η^n` on
`x ⊗ yᘁ` before the first trivalent vertex.
-/
theorem sum_orientedChannelCouponMorphism
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (exponent : ℤ) :
    ∑ channel : OrientedChannel data x y,
        orientedChannelCouponMorphism data η x y exponent channel =
      automorphismObjectPower η
        (OrientedTensorObject data x y) exponent := by
  classical
  rw [Fintype.sum_sigma]
  calc
    (∑ z, ∑ i : data.InsertionIndex
        (data.simple x ⊗ (data.simple y)ᘁ) z,
        orientedChannelCouponMorphism data η x y exponent ⟨z, i⟩) =
      automorphismObjectPower η (OrientedTensorObject data x y) exponent ≫
        (∑ z, ∑ i : data.InsertionIndex
            (data.simple x ⊗ (data.simple y)ᘁ) z,
          data.quantumDimension z •
            ((CategoryData.slidingForwardBasis data x y z).primal i ≫
              (CategoryData.slidingForwardBasis data x y z).dual i)) := by
        rw [Preadditive.comp_sum]
        apply Finset.sum_congr rfl
        intro z _
        rw [Preadditive.comp_sum]
        apply Finset.sum_congr rfl
        intro i _
        unfold orientedChannelCouponMorphism
        rw [CategoryTheory.Linear.comp_smul]
        apply congrArg (fun morphism =>
          data.quantumDimension z • morphism)
        have naturality :=
          automorphismObjectPower_naturality η
            ((CategoryData.slidingForwardBasis data x y z).primal i)
            exponent
        simpa only [
          FusionCategoryData.automorphismCouponPower,
          automorphismObjectPower,
          OrientedTensorObject,
          Category.assoc
        ] using
          (congrArg
            (fun morphism =>
              morphism ≫
                (CategoryData.slidingForwardBasis data x y z).dual i)
            naturality.symm)
    _ =
      automorphismObjectPower η (OrientedTensorObject data x y) exponent ≫
        𝟙 (OrientedTensorObject data x y) := by
      rw [CategoryData.slidingForwardSound data insertionLaw x y]
    _ = _ := Category.comp_id _

/--
When both original handles carry the same exponent, the mixed
`χ_x^n χ_y^{-n}` channel and the visible internal coupon `η_z^n` agree after
the complete `z, μ` sum.
-/
theorem sum_orientedChannelMorphism_eq_sum_orientedChannelCouponMorphism
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (exponent : ℤ) :
    ∑ channel : OrientedChannel data x y,
        orientedChannelMorphism data η x y
          exponent exponent channel =
      ∑ channel : OrientedChannel data x y,
        orientedChannelCouponMorphism data η x y
          exponent channel := by
  rw [sum_orientedChannelMorphism data insertionLaw η x y
    exponent exponent]
  rw [sum_orientedChannelCouponMorphism data insertionLaw η x y exponent]
  rw [orientedCharacterCoupon_eq_smul_identity]
  exact automorphismObjectPower_oriented_eq_smul_identity
    data η x y exponent |>.symm

/--
The internal `z, μ` resolution remains valid after inserting it into any
surrounding tangle.  Thus the third internal edge is an honest fusion channel
inside the original diagram, not a new closed Kirby component.
-/
theorem sum_orientedChannelCouponMorphism_inContext
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (exponent : ℤ)
    {wholeSource wholeTarget : Boundary C}
    (context :
      Context C
        (.atom (OrientedTensorObject data x y))
        (.atom (OrientedTensorObject data x y))
        wholeSource wholeTarget) :
    ∑ channel : OrientedChannel data x y,
        evalContextLinearMap (R := K) context
          (orientedChannelCouponMorphism
            data η x y exponent channel) =
      evalContextLinearMap (R := K) context
        (automorphismObjectPower η
          (OrientedTensorObject data x y) exponent) := by
  rw [← map_sum]
  exact congrArg
    (evalContextLinearMap (R := K) context)
    (sum_orientedChannelCouponMorphism
      data insertionLaw η x y exponent)

/--
Transport an endomorphism across an explicitly proved object equality.
Both directions are visible; this is not an arbitrary coercion.
-/
noncomputable def transportEndomorphism
    {X Y : C}
    (objectSound : X = Y)
    (morphism : Y ⟶ Y) :
    X ⟶ X :=
  eqToHom objectSound ≫ morphism ≫ eqToHom objectSound.symm

@[simp]
theorem transportEndomorphism_rfl
    {X : C}
    (morphism : X ⟶ X) :
    transportEndomorphism (C := C) rfl morphism = morphism := by
  simp [transportEndomorphism]

/--
Boundary-syntax version of the context theorem.  It is the bridge from a
two-strand free-diagram hole to the single tensor object used by the fusion
calculation.
-/
theorem sum_orientedChannelCouponMorphism_inBoundaryContext
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (exponent : ℤ)
    {hole wholeSource wholeTarget : Boundary C}
    (objectSound :
      hole.denote = OrientedTensorObject data x y)
    (context :
      Context C hole hole wholeSource wholeTarget) :
    ∑ channel : OrientedChannel data x y,
        evalContextLinearMap (R := K) context
          (transportEndomorphism objectSound
            (orientedChannelCouponMorphism
              data η x y exponent channel)) =
      evalContextLinearMap (R := K) context
        (transportEndomorphism objectSound
          (automorphismObjectPower η
            (OrientedTensorObject data x y) exponent)) := by
  rw [← map_sum]
  apply congrArg (evalContextLinearMap (R := K) context)
  simp only [transportEndomorphism]
  rw [← Preadditive.comp_sum, ← Preadditive.sum_comp]
  rw [sum_orientedChannelCouponMorphism
    data insertionLaw η x y exponent]

/-!
## Unequal character exponents

For a genuine handle slide the two participating components may carry
different exponents `a` and `b`.  The common `b`-part moves onto the internal
fusion channel, while the difference `a - b` remains on the `x`-strand.
-/

/-- The residual character coupon left on `x` after moving the common
`b`-power onto the internal channel. -/
noncomputable def leftResidualCoupon
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) :
    OrientedTensorObject data x y ⟶ OrientedTensorObject data x y :=
  data.toFusionCategoryData.automorphismCouponPower
      η x (xExponent - yExponent) ⊗ₘ
    𝟙 ((data.simple y)ᘁ)

/-- The residual coupon is the expected scalar on `x ⊗ yᘁ`. -/
theorem leftResidualCoupon_eq_smul_identity
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) :
    leftResidualCoupon data η x y xExponent yExponent =
      data.toFusionCategoryData.automorphismScalarPower
          η x (xExponent - yExponent) •
        𝟙 (OrientedTensorObject data x y) := by
  rw [leftResidualCoupon,
    data.toFusionCategoryData.automorphismCouponPower_eq_smul_identity]
  simp [OrientedTensorObject, tensorHom_def']

/--
One general `(z, μ)` term.  The common `yExponent` is carried by the
internal simple edge `z`; the exponent difference remains visibly outside
the two trivalent coupons.
-/
noncomputable def unequalExponentChannelMorphism
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ)
    (channel : OrientedChannel data x y) :
    OrientedTensorObject data x y ⟶ OrientedTensorObject data x y :=
  data.quantumDimension channel.1 •
    (leftResidualCoupon data η x y xExponent yExponent ≫
      (CategoryData.slidingForwardBasis data x y channel.1).primal channel.2 ≫
      data.toFusionCategoryData.automorphismCouponPower
        η channel.1 yExponent ≫
      (CategoryData.slidingForwardBasis data x y channel.1).dual channel.2)

/--
The residual `a-b` coupon followed by the common `b` coupon is exactly the
original pair of oriented coupons with exponents `a` and `b`.
-/
theorem leftResidual_comp_commonPower
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) :
    leftResidualCoupon data η x y xExponent yExponent ≫
        automorphismObjectPower η
          (OrientedTensorObject data x y) yExponent =
      orientedCharacterCoupon data η x y xExponent yExponent := by
  rw [leftResidualCoupon_eq_smul_identity,
    automorphismObjectPower_oriented_eq_smul_identity,
    orientedCharacterCoupon_eq_smul_identity]
  simp only [CategoryTheory.Linear.smul_comp,
    CategoryTheory.Linear.comp_smul, Category.comp_id, smul_smul]
  apply congrArg (fun scalar : K =>
    scalar • 𝟙 (OrientedTensorObject data x y))
  rw [orientedCharacterScalar]
  calc
    (data.toFusionCategoryData.automorphismScalarPower η x yExponent *
          data.toFusionCategoryData.automorphismScalarPower
            η y (-yExponent)) *
        data.toFusionCategoryData.automorphismScalarPower
          η x (xExponent - yExponent) =
      (data.toFusionCategoryData.automorphismScalarPower
            η x (xExponent - yExponent) *
          data.toFusionCategoryData.automorphismScalarPower η x yExponent) *
        data.toFusionCategoryData.automorphismScalarPower
          η y (-yExponent) := by
      ac_rfl
    _ =
      data.toFusionCategoryData.automorphismScalarPower η x xExponent *
        data.toFusionCategoryData.automorphismScalarPower
          η y (-yExponent) := by
      rw [← data.toFusionCategoryData.automorphismScalarPower_add]
      congr 2
      omega

/--
For arbitrary character exponents `a,b`, the full `d_z`-weighted channel
sum reconstructs the original two coupons.  This is the form required by the
twisted 2/2 handle-slide proof.
-/
theorem sum_unequalExponentChannelMorphism
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ) :
    ∑ channel : OrientedChannel data x y,
        unequalExponentChannelMorphism
          data η x y xExponent yExponent channel =
      orientedCharacterCoupon data η x y xExponent yExponent := by
  classical
  calc
    (∑ channel : OrientedChannel data x y,
        unequalExponentChannelMorphism
          data η x y xExponent yExponent channel) =
      leftResidualCoupon data η x y xExponent yExponent ≫
        (∑ channel : OrientedChannel data x y,
          orientedChannelCouponMorphism
            data η x y yExponent channel) := by
        rw [Preadditive.comp_sum]
        apply Finset.sum_congr rfl
        intro channel _
        unfold unequalExponentChannelMorphism
        unfold orientedChannelCouponMorphism
        rw [CategoryTheory.Linear.comp_smul]
    _ =
      leftResidualCoupon data η x y xExponent yExponent ≫
        automorphismObjectPower η
          (OrientedTensorObject data x y) yExponent := by
      rw [sum_orientedChannelCouponMorphism
        data insertionLaw η x y yExponent]
    _ = _ :=
      leftResidual_comp_commonPower
        data η x y xExponent yExponent

/--
The unequal-exponent channel identity remains valid in any explicitly
identified boundary context.
-/
theorem sum_unequalExponentChannelMorphism_inBoundaryContext
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (xExponent yExponent : ℤ)
    {hole wholeSource wholeTarget : Boundary C}
    (objectSound :
      hole.denote = OrientedTensorObject data x y)
    (context :
      Context C hole hole wholeSource wholeTarget) :
    ∑ channel : OrientedChannel data x y,
        evalContextLinearMap (R := K) context
          (transportEndomorphism objectSound
            (unequalExponentChannelMorphism
              data η x y xExponent yExponent channel)) =
      evalContextLinearMap (R := K) context
        (transportEndomorphism objectSound
          (orientedCharacterCoupon
            data η x y xExponent yExponent)) := by
  rw [← map_sum]
  apply congrArg (evalContextLinearMap (R := K) context)
  simp only [transportEndomorphism]
  rw [← Preadditive.comp_sum, ← Preadditive.sum_comp]
  rw [sum_unequalExponentChannelMorphism
    data insertionLaw η x y xExponent yExponent]

/-!
## Global component exponents in the positive endpoint convention

The local positive endpoint is `x ⊗ yᘁ`.  A global exponent `b` on the
stationary component is therefore passed to the oriented formula as `-b`.
-/

/-- The two global component coupons represented on `x ⊗ yᘁ`. -/
noncomputable def globalPositiveEndpointCoupon
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (movingExponent stationaryExponent : ℤ) :
    OrientedTensorObject data x y ⟶ OrientedTensorObject data x y :=
  orientedCharacterCoupon data η x y
    movingExponent (-stationaryExponent)

/--
At a positive endpoint, the internal channel carries exponent `-b` and the
residual moving-strand coupon carries `a+b`.
-/
theorem sum_globalPositiveEndpointChannelMorphism
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (η : TensorIdentityAutomorphism C)
    (x y : S)
    (movingExponent stationaryExponent : ℤ) :
    ∑ channel : OrientedChannel data x y,
        unequalExponentChannelMorphism
          data η x y movingExponent (-stationaryExponent) channel =
      globalPositiveEndpointCoupon
        data η x y movingExponent stationaryExponent := by
  exact sum_unequalExponentChannelMorphism
    data insertionLaw η x y movingExponent (-stationaryExponent)

/-- The residual exponent in the positive endpoint convention is `a+b`. -/
theorem positiveEndpoint_residualExponent
    (movingExponent stationaryExponent : ℤ) :
    movingExponent - (-stationaryExponent) =
      movingExponent + stationaryExponent := by
  omega

end OrientedSlidingResolution

end TwistedYetter.Kirby.TwoOverTwoFusionChannel
