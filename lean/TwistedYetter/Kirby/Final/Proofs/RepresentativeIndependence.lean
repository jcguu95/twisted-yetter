import TwistedYetter.Kirby.Final.Semantics.Independent.Entry

/-!
# Representative independence for the frozen evaluator

This file proves the algebraic and graphical lemmas needed to descend the
cycle-level frozen evaluator to the THAM-side second homology quotient.  It
does not modify the frozen semantic definitions.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
The character coupon on one puncture carries precisely the signed scalar
prescribed by the puncture direction.
-/
theorem characterCoupon_on_puncture
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (puncture : DottedPuncture diagram.trace)
    (exponent : ℤ) :
    isoIntPowerHom
        (𝒞η.character.iso.app
          (orientedSimpleObject 𝒞η.category
            (orientedExteriorStrand
              𝒞η.category diagram labeling puncture.inputStrand)))
        exponent =
      (((𝒞η.character.value
          (exteriorStrandLabel
            𝒞η.category diagram labeling puncture.inputStrand)) ^
          (puncture.characterExponentSign * exponent) : Kˣ) : K) •
        𝟙
          (orientedSimpleObject 𝒞η.category
            (orientedExteriorStrand
              𝒞η.category diagram labeling puncture.inputStrand)) := by
  have orientation :=
    puncture.input_orientation_matches_direction
  cases direction : puncture.direction with
  | withDiskOrientation =>
      have strandPositive :
          (diagram.trace.strands puncture.inputStrand).orientation =
            .positive := by
        simpa [PunctureDirection.strandOrientation, direction] using orientation
      have signPositive :
          puncture.characterExponentSign = 1 := by
        simpa [PunctureDirection.characterExponentSign, direction] using
          puncture.exponent_matches_direction
      unfold orientedSimpleObject orientedExteriorStrand
      rw [strandPositive]
      simp only [ribbonDirectionOfStrandOrientation]
      simpa [signPositive] using
        characterCoupon_on_forwardSimple
          𝒞η.character
          (exteriorStrandLabel
            𝒞η.category diagram labeling puncture.inputStrand)
          exponent
  | againstDiskOrientation =>
      have strandNegative :
          (diagram.trace.strands puncture.inputStrand).orientation =
            .negative := by
        simpa [PunctureDirection.strandOrientation, direction] using orientation
      have signNegative :
          puncture.characterExponentSign = -1 := by
        simpa [PunctureDirection.characterExponentSign, direction] using
          puncture.exponent_matches_direction
      unfold orientedSimpleObject orientedExteriorStrand
      rw [strandNegative]
      simp only [ribbonDirectionOfStrandOrientation]
      simpa [signNegative] using
        characterCoupon_on_dualSimple
          𝒞η.character
          (exteriorStrandLabel
            𝒞η.category diagram labeling puncture.inputStrand)
          exponent

private theorem character_tensor_inv
    {𝒞 : PremodularFusionCategory K}
    (character : TensorIdentityCharacter 𝒞)
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
    {𝒞 : PremodularFusionCategory K}
    (character : TensorIdentityCharacter 𝒞)
    (X Y : 𝒞.C)
    (power : ℕ) :
    isoNatPowerHom (character.iso.app (X ⊗ Y)) power =
      isoNatPowerHom (character.iso.app X) power ⊗ₘ
        isoNatPowerHom (character.iso.app Y) power := by
  induction power with
  | zero =>
      simp [isoNatPowerHom]
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
    {𝒞 : PremodularFusionCategory K}
    (character : TensorIdentityCharacter 𝒞)
    (X Y : 𝒞.C)
    (power : ℕ) :
    isoNatPowerHom (character.iso.app (X ⊗ Y)).symm power =
      isoNatPowerHom (character.iso.app X).symm power ⊗ₘ
        isoNatPowerHom (character.iso.app Y).symm power := by
  induction power with
  | zero =>
      simp [isoNatPowerHom]
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
    {𝒞 : PremodularFusionCategory K}
    (character : TensorIdentityCharacter 𝒞)
    (X Y : 𝒞.C)
    (exponent : ℤ) :
    isoIntPowerHom (character.iso.app (X ⊗ Y)) exponent =
      isoIntPowerHom (character.iso.app X) exponent ⊗ₘ
        isoIntPowerHom (character.iso.app Y) exponent := by
  cases exponent with
  | ofNat power =>
      exact character_natPower_tensor character X Y power
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
  | succ power ih =>
      simp only [isoNatPowerHom]
      rw [hom_eq, Category.comp_id, ih]

private theorem character_intPower_unit
    {𝒞 : PremodularFusionCategory K}
    (character : TensorIdentityCharacter 𝒞)
    (exponent : ℤ) :
    isoIntPowerHom
        (character.iso.app (𝟙_ 𝒞.C))
        exponent =
      𝟙 (𝟙_ 𝒞.C) := by
  have hom_eq := character.unit_hom
  have inv_eq :
      character.iso.inv.app (𝟙_ 𝒞.C) =
        𝟙 (𝟙_ 𝒞.C) := by
    rw [← cancel_epi
      (character.iso.hom.app (𝟙_ 𝒞.C))]
    rw [character.iso.hom_inv_id_app]
    simp [hom_eq]
  cases exponent with
  | ofNat power =>
      exact isoNatPowerHom_eq_id
        (character.iso.app (𝟙_ 𝒞.C)) hom_eq power
  | negSucc power =>
      exact isoNatPowerHom_eq_id
        (character.iso.app (𝟙_ 𝒞.C)).symm inv_eq (power + 1)

def punctureWordCharacterUnit
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (punctures : List (DottedPuncture diagram.trace))
    (exponent : ℤ) : K :=
  (punctures.map fun puncture =>
    ((𝒞η.character.value
          (exteriorStrandLabel
            𝒞η.category diagram labeling puncture.inputStrand) ^
        (puncture.characterExponentSign * exponent) : Kˣ) : K)).prod

/--
One uniform character coupon on the puncture boundary word is the product of
the signed simple-label scalars recorded by that word.
-/
theorem characterCoupon_on_punctureWord
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (punctures : List (DottedPuncture diagram.trace))
    (exponent : ℤ) :
    isoIntPowerHom
        (𝒞η.character.iso.app
          (ribbonWordObject 𝒞η.category
            (exteriorWord 𝒞η.category diagram labeling
              (punctures.map DottedPuncture.inputStrand))))
        exponent =
      punctureWordCharacterUnit
          𝒞η diagram labeling punctures exponent •
        𝟙
          (ribbonWordObject 𝒞η.category
            (exteriorWord 𝒞η.category diagram labeling
              (punctures.map DottedPuncture.inputStrand))) := by
  induction punctures with
  | nil =>
      simp only [List.map_nil, exteriorWord, ribbonWordObject,
        punctureWordCharacterUnit, List.prod_nil, Units.val_one]
      rw [character_intPower_unit]
      exact (one_smul K _).symm
  | cons puncture rest ih =>
      simp only [List.map_cons, exteriorWord, ribbonWordObject,
        punctureWordCharacterUnit, List.prod_cons]
      rw [character_intPower_tensor]
      rw [characterCoupon_on_puncture 𝒞η diagram labeling puncture exponent]
      rw [show
        isoIntPowerHom
            (𝒞η.character.iso.app
              (ribbonWordObject 𝒞η.category
                (List.map
                  (orientedExteriorStrand
                    𝒞η.category diagram labeling)
                  (List.map DottedPuncture.inputStrand rest))))
            exponent =
          punctureWordCharacterUnit
              𝒞η diagram labeling rest exponent •
            𝟙
              (ribbonWordObject 𝒞η.category
                (List.map
                  (orientedExteriorStrand
                    𝒞η.category diagram labeling)
                  (List.map DottedPuncture.inputStrand rest))) by
        simpa [exteriorWord] using ih]
      simp [MonoidalCategory.tensorHom_def, ← mul_smul]
      simp only [punctureWordCharacterUnit]
      rw [mul_comm]
      have restScalar :
          (List.map
              (fun puncture =>
                ((𝒞η.character.value
                    (exteriorStrandLabel
                      𝒞η.category diagram labeling puncture.inputStrand) ^
                  (puncture.characterExponentSign * exponent) : Kˣ) : K))
              rest).prod =
            (List.map
              (fun puncture =>
                𝒞η.character.simpleScalar
                    (exteriorStrandLabel
                      𝒞η.category diagram labeling puncture.inputStrand) ^
                  (puncture.characterExponentSign * exponent))
              rest).prod := by
        simp only [Units.val_zpow_eq_zpow_val,
          TensorIdentityCharacter.value_val]
      rw [restScalar]
      congr 1

private def explicitProjectorHoleMorphism
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (punctures : List (DottedPuncture diagram.trace)) :
    ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (punctures.map DottedPuncture.inputStrand)) ⟶
      ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (punctures.map DottedPuncture.outputStrand)) :=
  tensorUnitProjector 𝒞
      (ribbonWordObject 𝒞
        (exteriorWord 𝒞 diagram labeling
          (punctures.map DottedPuncture.inputStrand))) ≫
    eqToHom
      (congrArg (ribbonWordObject 𝒞)
        (exteriorWord_of_punctures_eq 𝒞 diagram labeling punctures))

private theorem compile_projectorHole_eq_explicit
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (dotted : diagram.trace.ComponentId)
    (punctures : List (DottedPuncture diagram.trace))
    (pairing :
      (CutOpenEvent.projectorHole dotted punctures).PairingCompatible) :
    compileCutOpenEventMorphism
        𝒞 diagram labeling (.projectorHole dotted punctures) pairing =
      explicitProjectorHoleMorphism 𝒞 diagram labeling punctures := by
  let X :=
    ribbonWordObject 𝒞
      (exteriorWord 𝒞 diagram labeling
        (punctures.map DottedPuncture.inputStrand))
  let Y :=
    ribbonWordObject 𝒞
      (exteriorWord 𝒞 diagram labeling
        (punctures.map DottedPuncture.outputStrand))
  have object_eq : X = Y :=
    congrArg (ribbonWordObject 𝒞)
      (exteriorWord_of_punctures_eq 𝒞 diagram labeling punctures)
  simp only [compileCutOpenEventMorphism, id_eq]
  change Eq.mpr _ (tensorUnitProjector 𝒞 X) =
    tensorUnitProjector 𝒞 X ≫ eqToHom object_eq
  calc
    Eq.mpr _ (tensorUnitProjector 𝒞 X) =
        Eq.mpr
          (congrArg (fun W => X ⟶ W) object_eq.symm)
          (tensorUnitProjector 𝒞 X) := by
            congr 1
    _ = tensorUnitProjector 𝒞 X ≫ eqToHom object_eq :=
      congrArg_mpr_hom_right
        (tensorUnitProjector 𝒞 X) object_eq.symm

/--
A uniform character coupon immediately before a literal dotted projector
hole is absorbed.  This is the local graphical calculation; no closed-link
evaluation or homology quotient is used here.
-/
theorem characterCoupon_projectorHole_left
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (dotted : diagram.trace.ComponentId)
    (punctures : List (DottedPuncture diagram.trace))
    (pairing :
      (CutOpenEvent.projectorHole dotted punctures).PairingCompatible)
    (exponent : ℤ) :
    isoIntPowerHom
        (𝒞η.character.iso.app
          (ribbonWordObject 𝒞η.category
            (exteriorWord 𝒞η.category diagram labeling
              ((CutOpenEvent.projectorHole dotted punctures).beforeWord))))
        exponent ≫
      compileCutOpenEventMorphism
        𝒞η.category diagram labeling
        (.projectorHole dotted punctures) pairing =
      compileCutOpenEventMorphism
        𝒞η.category diagram labeling
        (.projectorHole dotted punctures) pairing := by
  rw [compile_projectorHole_eq_explicit]
  unfold explicitProjectorHoleMorphism
  change
    isoIntPowerHom
          (𝒞η.character.iso.app
            (ribbonWordObject 𝒞η.category
              (exteriorWord 𝒞η.category diagram labeling
                (punctures.map DottedPuncture.inputStrand))))
          exponent ≫
        (tensorUnitProjector 𝒞η.category
            (ribbonWordObject 𝒞η.category
              (exteriorWord 𝒞η.category diagram labeling
                (punctures.map DottedPuncture.inputStrand))) ≫
          eqToHom _) =
      tensorUnitProjector 𝒞η.category
          (ribbonWordObject 𝒞η.category
            (exteriorWord 𝒞η.category diagram labeling
              (punctures.map DottedPuncture.inputStrand))) ≫
        eqToHom _
  rw [← Category.assoc]
  rw [characterCoupon_tensorUnitProjector_left]
  congr 1

/--
The signed puncture-word scalar is invisible on the literal dotted projector
edge.  This is the scalar form used by the finite labeling sum.
-/
theorem punctureWordCharacterUnit_smul_projectorHole
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (dotted : diagram.trace.ComponentId)
    (punctures : List (DottedPuncture diagram.trace))
    (pairing :
      (CutOpenEvent.projectorHole dotted punctures).PairingCompatible)
    (exponent : ℤ) :
    punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
        compileCutOpenEventMorphism
          𝒞η.category diagram labeling
          (.projectorHole dotted punctures) pairing =
      compileCutOpenEventMorphism
        𝒞η.category diagram labeling
        (.projectorHole dotted punctures) pairing := by
  let X :=
    ribbonWordObject 𝒞η.category
      (exteriorWord 𝒞η.category diagram labeling
        (punctures.map DottedPuncture.inputStrand))
  have coupon_eq :
      isoIntPowerHom (𝒞η.character.iso.app X) exponent =
        punctureWordCharacterUnit
            𝒞η diagram labeling punctures exponent • 𝟙 X := by
    simpa [X] using
      characterCoupon_on_punctureWord
        𝒞η diagram labeling punctures exponent
  have projector_eq :
    punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
        tensorUnitProjector 𝒞η.category X =
      tensorUnitProjector 𝒞η.category X := by
    rw [show
      punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
          tensorUnitProjector 𝒞η.category X =
        (punctureWordCharacterUnit
            𝒞η diagram labeling punctures exponent • 𝟙 X) ≫
          tensorUnitProjector 𝒞η.category X by simp]
    rw [← coupon_eq]
    exact characterCoupon_tensorUnitProjector_left
      𝒞η.character X exponent
  rw [compile_projectorHole_eq_explicit]
  unfold explicitProjectorHoleMorphism
  simpa [X] using congrArg
    (fun map => map ≫
      eqToHom
        (congrArg (ribbonWordObject 𝒞η.category)
          (exteriorWord_of_punctures_eq
            𝒞η.category diagram labeling punctures)))
    projector_eq

/--
Adding a fixed left and right exterior context is linear in the local
morphism.  This is the bookkeeping bridge from a literal projector edge to
the same edge inside the complete cut-open trace.
-/
theorem contextualizeRibbonMorphism_smul
    (𝒞 : PremodularFusionCategory K)
    (left before after right : RibbonWord 𝒞)
    (map :
      ribbonWordObject 𝒞 before ⟶
        ribbonWordObject 𝒞 after)
    (scalar : K) :
    contextualizeRibbonMorphism 𝒞 left before after right (scalar • map) =
      scalar •
        contextualizeRibbonMorphism 𝒞 left before after right map := by
  simp [contextualizeRibbonMorphism]

/-- A scalar absorbed by a local edge remains absorbed after adding context. -/
theorem contextualizeRibbonMorphism_absorbs
    (𝒞 : PremodularFusionCategory K)
    (left before after right : RibbonWord 𝒞)
    (map :
      ribbonWordObject 𝒞 before ⟶
        ribbonWordObject 𝒞 after)
    (scalar : K)
    (absorbed : scalar • map = map) :
    scalar • contextualizeRibbonMorphism 𝒞 left before after right map =
      contextualizeRibbonMorphism 𝒞 left before after right map := by
  rw [← contextualizeRibbonMorphism_smul]
  rw [absorbed]

/--
The puncture character scalar is absorbed by a dotted projector in every
fixed exterior context.
-/
theorem punctureWordCharacterUnit_smul_contextualProjectorHole
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (dotted : diagram.trace.ComponentId)
    (punctures : List (DottedPuncture diagram.trace))
    (pairing :
      (CutOpenEvent.projectorHole dotted punctures).PairingCompatible)
    (left right : List diagram.trace.StrandId)
    (exponent : ℤ) :
    punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
        contextualizeRibbonMorphism 𝒞η.category
          (exteriorWord 𝒞η.category diagram labeling left)
          (exteriorWord 𝒞η.category diagram labeling
            (CutOpenEvent.projectorHole dotted punctures).beforeWord)
          (exteriorWord 𝒞η.category diagram labeling
            (CutOpenEvent.projectorHole dotted punctures).afterWord)
          (exteriorWord 𝒞η.category diagram labeling right)
          (compileCutOpenEventMorphism
            𝒞η.category diagram labeling
            (.projectorHole dotted punctures) pairing) =
      contextualizeRibbonMorphism 𝒞η.category
        (exteriorWord 𝒞η.category diagram labeling left)
        (exteriorWord 𝒞η.category diagram labeling
          (CutOpenEvent.projectorHole dotted punctures).beforeWord)
        (exteriorWord 𝒞η.category diagram labeling
          (CutOpenEvent.projectorHole dotted punctures).afterWord)
        (exteriorWord 𝒞η.category diagram labeling right)
        (compileCutOpenEventMorphism
          𝒞η.category diagram labeling
          (.projectorHole dotted punctures) pairing) := by
  apply contextualizeRibbonMorphism_absorbs
  exact punctureWordCharacterUnit_smul_projectorHole
    𝒞η diagram labeling dotted punctures pairing exponent

/--
Absorption by one middle morphism survives arbitrary morphisms before and
after it.  This lemma will be applied first to the equality transports around
one contextual edge and then to the prefix and suffix of the finite trace.
-/
theorem comp_middle_absorbs
    {𝒞 : PremodularFusionCategory K}
    {W X Y Z : 𝒞.C}
    (beforeMap : W ⟶ X)
    (middle : X ⟶ Y)
    (afterMap : Y ⟶ Z)
    (scalar : K)
    (absorbed : scalar • middle = middle) :
    scalar • (beforeMap ≫ middle ≫ afterMap) =
      beforeMap ≫ middle ≫ afterMap := by
  calc
    scalar • (beforeMap ≫ middle ≫ afterMap) =
        beforeMap ≫ (scalar • middle) ≫ afterMap := by simp
    _ = beforeMap ≫ middle ≫ afterMap := by rw [absorbed]

end

end TwistedYetter.Kirby.Final.Proofs
