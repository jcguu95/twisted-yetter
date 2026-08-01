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
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (punctures : List (DottedPuncture diagram.trace))
    (T : DottedIncidenceMorphism
      𝒞η.category diagram labeling punctures)
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
    (diagram : CombinatorialSpecialKirbyDiagram)
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

end

end TwistedYetter.Kirby.Final.Proofs
