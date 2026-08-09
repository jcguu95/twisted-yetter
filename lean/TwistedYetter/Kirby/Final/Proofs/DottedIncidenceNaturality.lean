import TwistedYetter.Kirby.Final.Proofs.IntrinsicDottedCutInterpretation

/-!
# Character naturality at a dotted incidence boundary

This file isolates the categorical core of representative independence.
The dotted disk is used only to partition incidence occurrences into the
domain and codomain of a local morphism.  It does not determine whether a
component is labelled by `X` or `X*`, and it does not determine a character
exponent.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
An integral power of the twisting character can be transported through the
entire local dotted-incidence morphism.  The incidence directions occur only
in the source and target words used by `DottedIncidenceMorphism`.
-/
theorem dottedIncidenceMorphism_character_naturality
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (punctures : List (DottedPuncture diagram.trace))
    (T :
      simpleLabelWordObject 𝒞η.category
            (dottedInboundLabelWord
              𝒞η.category diagram labeling punctures) ⟶
        simpleLabelWordObject 𝒞η.category
            (dottedOutboundLabelWord
              𝒞η.category diagram labeling punctures))
    (exponent : ℤ) :
    isoIntPowerHom
          (𝒞η.character.iso.app
            (simpleLabelWordObject 𝒞η.category
              (dottedInboundLabelWord
                𝒞η.category diagram labeling punctures)))
          exponent ≫ T =
      T ≫ isoIntPowerHom
          (𝒞η.character.iso.app
            (simpleLabelWordObject 𝒞η.category
              (dottedOutboundLabelWord
                𝒞η.category diagram labeling punctures)))
          exponent := by
  exact characterCoupon_naturality 𝒞η.character T exponent

/--
Character naturality for the morphism interpreted from an intrinsic dotted
cut tangle.  Neither the statement nor the construction reads a planar strand
orientation or a puncture-dependent character exponent.
-/
theorem intrinsicDottedCut_character_naturality
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    {punctures : List (DottedPuncture diagram.trace)}
    (cut : IntrinsicDottedCutTangle diagram punctures)
    (exponent : ℤ) :
    isoIntPowerHom
          (𝒞η.character.iso.app
            (simpleLabelWordObject 𝒞η.category
              (dottedInboundLabelWord
                𝒞η.category diagram labeling punctures)))
          exponent ≫
        intrinsicDottedCutMorphism
          𝒞η.category diagram labeling cut =
      intrinsicDottedCutMorphism
          𝒞η.category diagram labeling cut ≫
        isoIntPowerHom
          (𝒞η.character.iso.app
            (simpleLabelWordObject 𝒞η.category
              (dottedOutboundLabelWord
                𝒞η.category diagram labeling punctures)))
          exponent := by
  exact dottedIncidenceMorphism_character_naturality
    𝒞η diagram labeling punctures
      (intrinsicDottedCutMorphism
        𝒞η.category diagram labeling cut)
      exponent

private theorem character_tensor_inv
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (X Y : 𝒞.C) :
    character.iso.inv.app (X ⊗ Y) =
      character.iso.inv.app X ⊗ₘ character.iso.inv.app Y := by
  apply (cancel_epi (character.iso.hom.app (X ⊗ Y))).1
  rw [character.iso.hom_inv_id_app]
  rw [character.tensor_hom]
  calc
    𝟙 (X ⊗ Y) = 𝟙 X ⊗ₘ 𝟙 Y := by simp
    _ =
        (character.iso.hom.app X ≫ character.iso.inv.app X) ⊗ₘ
          (character.iso.hom.app Y ≫ character.iso.inv.app Y) := by
      rw [character.iso.hom_inv_id_app, character.iso.hom_inv_id_app]
      simp
    _ =
        (character.iso.hom.app X ⊗ₘ character.iso.hom.app Y) ≫
          (character.iso.inv.app X ⊗ₘ character.iso.inv.app Y) := by
      simp

private theorem character_natPower_tensor
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (X Y : 𝒞.C)
    (power : ℕ) :
    isoNatPowerHom (character.iso.app (X ⊗ Y)) power =
      isoNatPowerHom (character.iso.app X) power ⊗ₘ
        isoNatPowerHom (character.iso.app Y) power := by
  induction power with
  | zero => simp [isoNatPowerHom]
  | succ power ih =>
      simp only [isoNatPowerHom]
      rw [ih]
      change
        (isoNatPowerHom (character.iso.app X) power ⊗ₘ
            isoNatPowerHom (character.iso.app Y) power) ≫
            character.iso.hom.app (X ⊗ Y) =
          (isoNatPowerHom (character.iso.app X) power ≫
              character.iso.hom.app X) ⊗ₘ
            (isoNatPowerHom (character.iso.app Y) power ≫
              character.iso.hom.app Y)
      rw [character.tensor_hom]
      simp

private theorem character_invNatPower_tensor
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (X Y : 𝒞.C)
    (power : ℕ) :
    isoNatPowerHom (character.iso.app (X ⊗ Y)).symm power =
      isoNatPowerHom (character.iso.app X).symm power ⊗ₘ
        isoNatPowerHom (character.iso.app Y).symm power := by
  induction power with
  | zero => simp [isoNatPowerHom]
  | succ power ih =>
      simp only [isoNatPowerHom]
      rw [ih]
      change
        (isoNatPowerHom (character.iso.app X).symm power ⊗ₘ
            isoNatPowerHom (character.iso.app Y).symm power) ≫
            character.iso.inv.app (X ⊗ Y) =
          (isoNatPowerHom (character.iso.app X).symm power ≫
              character.iso.inv.app X) ⊗ₘ
            (isoNatPowerHom (character.iso.app Y).symm power ≫
              character.iso.inv.app Y)
      rw [character_tensor_inv]
      simp

private theorem character_intPower_tensor
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (X Y : 𝒞.C)
    (exponent : ℤ) :
    isoIntPowerHom (character.iso.app (X ⊗ Y)) exponent =
      isoIntPowerHom (character.iso.app X) exponent ⊗ₘ
        isoIntPowerHom (character.iso.app Y) exponent := by
  cases exponent with
  | ofNat power => exact character_natPower_tensor character X Y power
  | negSucc power =>
      exact character_invNatPower_tensor character X Y (power + 1)

private theorem isoNatPowerHom_eq_id
    {C : Type*} [Category C]
    {X : C}
    (iso : X ≅ X)
    (hom_eq : iso.hom = 𝟙 X)
    (power : ℕ) :
    isoNatPowerHom iso power = 𝟙 X := by
  induction power with
  | zero => rfl
  | succ power ih => simp [isoNatPowerHom, hom_eq, ih]

private theorem character_intPower_unit
    {𝒞 : BundledPremodularCategory K}
    (character : TensorIdentityCharacter (C := 𝒞.C))
    (exponent : ℤ) :
    isoIntPowerHom (character.iso.app (𝟙_ 𝒞.C)) exponent =
      𝟙 (𝟙_ 𝒞.C) := by
  have hom_eq := character.unit_hom
  have inv_eq :
      character.iso.inv.app (𝟙_ 𝒞.C) = 𝟙 (𝟙_ 𝒞.C) := by
    rw [← cancel_epi (character.iso.hom.app (𝟙_ 𝒞.C))]
    rw [character.iso.hom_inv_id_app]
    simp [hom_eq]
  cases exponent with
  | ofNat power =>
      exact isoNatPowerHom_eq_id (character.iso.app (𝟙_ 𝒞.C)) hom_eq power
  | negSucc power =>
      exact isoNatPowerHom_eq_id
        (character.iso.app (𝟙_ 𝒞.C)).symm inv_eq (power + 1)

/-- The character scalar on a public component-colour boundary word. -/
def componentWordCharacterUnit
    (𝒞η : TwistedPremodularCategory K)
    (labels : List 𝒞η.category.simples.Simple)
    (exponent : ℤ) : Kˣ :=
  (labels.map fun label => 𝒞η.character.value label ^ exponent).prod

/--
On a public intrinsic-cut boundary, one uniform character coupon is the
product of the character scalars of the component colours.  No dotted-disk
direction and no planar strand orientation occurs in this statement.
-/
theorem characterCoupon_on_componentWord
    (𝒞η : TwistedPremodularCategory K)
    (labels : List 𝒞η.category.simples.Simple)
    (exponent : ℤ) :
    isoIntPowerHom
        (𝒞η.character.iso.app
          (simpleLabelWordObject 𝒞η.category labels))
        exponent =
      ((componentWordCharacterUnit 𝒞η labels exponent : Kˣ) : K) •
        𝟙 (simpleLabelWordObject 𝒞η.category labels) := by
  induction labels with
  | nil =>
      simp only [simpleLabelWordObject, componentWordCharacterUnit,
        List.map_nil, List.prod_nil, Units.val_one]
      rw [character_intPower_unit]
      exact (one_smul K _).symm
  | cons label rest ih =>
      simp only [simpleLabelWordObject, componentWordCharacterUnit,
        List.map_cons, List.prod_cons]
      rw [character_intPower_tensor]
      rw [characterCoupon_on_forwardSimple]
      rw [ih]
      simp [MonoidalCategory.tensorHom_def, ← mul_smul]
      rw [mul_comm]
      rfl

/--
The output-to-input character ratio of one dotted incidence boundary acts
trivially on every morphism with that exact boundary.  This is the local
categorical core of representative independence; no particular graphical
syntax is used.
-/
theorem dottedIncidenceMorphism_boundaryRatio_absorbs
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (punctures : List (DottedPuncture diagram.trace))
    (T :
      simpleLabelWordObject 𝒞η.category
            (dottedInboundLabelWord
              𝒞η.category diagram labeling punctures) ⟶
        simpleLabelWordObject 𝒞η.category
            (dottedOutboundLabelWord
              𝒞η.category diagram labeling punctures))
    (exponent : ℤ) :
    let inputFactor := componentWordCharacterUnit 𝒞η
      (dottedInboundLabelWord 𝒞η.category diagram labeling punctures)
      exponent
    let outputFactor := componentWordCharacterUnit 𝒞η
      (dottedOutboundLabelWord 𝒞η.category diagram labeling punctures)
      exponent
    (((outputFactor * inputFactor⁻¹ : Kˣ) : K) • T) = T := by
  dsimp only
  have naturality :
      isoIntPowerHom
            (𝒞η.character.iso.app
              (simpleLabelWordObject 𝒞η.category
                (dottedInboundLabelWord
                  𝒞η.category diagram labeling punctures)))
            exponent ≫ T =
        T ≫ isoIntPowerHom
          (𝒞η.character.iso.app
            (simpleLabelWordObject 𝒞η.category
              (dottedOutboundLabelWord
                𝒞η.category diagram labeling punctures)))
          exponent :=
    dottedIncidenceMorphism_character_naturality
      𝒞η diagram labeling punctures T exponent
  have scalarNaturality :
      ((componentWordCharacterUnit 𝒞η
          (dottedInboundLabelWord
            𝒞η.category diagram labeling punctures) exponent : Kˣ) : K) •
          T =
        ((componentWordCharacterUnit 𝒞η
          (dottedOutboundLabelWord
            𝒞η.category diagram labeling punctures) exponent : Kˣ) : K) •
          T := by
    calc
      _ =
          isoIntPowerHom
                (𝒞η.character.iso.app
                  (simpleLabelWordObject 𝒞η.category
                    (dottedInboundLabelWord
                      𝒞η.category diagram labeling punctures)))
                exponent ≫
            T := by
        rw [characterCoupon_on_componentWord]
        simp
      _ =
          T ≫
            isoIntPowerHom
              (𝒞η.character.iso.app
                (simpleLabelWordObject 𝒞η.category
                  (dottedOutboundLabelWord
                    𝒞η.category diagram labeling punctures)))
              exponent := naturality
      _ = _ := by
        have outputFormula := characterCoupon_on_componentWord 𝒞η
          (dottedOutboundLabelWord
            𝒞η.category diagram labeling punctures) exponent
        calc
          _ = T ≫
              (((componentWordCharacterUnit 𝒞η
                (dottedOutboundLabelWord
                  𝒞η.category diagram labeling punctures)
                exponent : Kˣ) : K) •
                𝟙 (simpleLabelWordObject 𝒞η.category
                  (dottedOutboundLabelWord
                    𝒞η.category diagram labeling punctures))) :=
            congrArg (fun morphism => T ≫ morphism) outputFormula
          _ = _ := by simp
  rw [mul_comm]
  rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_smul]
  rw [← scalarNaturality]
  rw [← mul_smul]
  simp

/--
The preceding syntax-free theorem specializes to the morphism interpreted
from an intrinsic dotted cut tangle.
-/
theorem intrinsicDottedCut_boundaryRatio_absorbs
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    {punctures : List (DottedPuncture diagram.trace)}
    (cut : IntrinsicDottedCutTangle diagram punctures)
    (exponent : ℤ) :
    let inputFactor := componentWordCharacterUnit 𝒞η
      (dottedInboundLabelWord 𝒞η.category diagram labeling punctures)
      exponent
    let outputFactor := componentWordCharacterUnit 𝒞η
      (dottedOutboundLabelWord 𝒞η.category diagram labeling punctures)
      exponent
    let T :
        simpleLabelWordObject 𝒞η.category
              (dottedInboundLabelWord
                𝒞η.category diagram labeling punctures) ⟶
          simpleLabelWordObject 𝒞η.category
              (dottedOutboundLabelWord
                𝒞η.category diagram labeling punctures) :=
      intrinsicDottedCutMorphism
        𝒞η.category diagram labeling cut
    (((outputFactor * inputFactor⁻¹ : Kˣ) : K) • T) = T := by
  exact dottedIncidenceMorphism_boundaryRatio_absorbs
    𝒞η diagram labeling punctures
      (intrinsicDottedCutMorphism
        𝒞η.category diagram labeling cut)
      exponent

end

end TwistedYetter.Kirby.Final.Proofs
