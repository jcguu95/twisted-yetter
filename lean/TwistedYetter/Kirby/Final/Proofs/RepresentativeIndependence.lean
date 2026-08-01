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

private def strandCharacterExponentSign : StrandOrientation → ℤ
  | .positive => 1
  | .negative => -1

/--
Bending a negatively powered character coupon on a fixed simple-labelled
strand produces the positively powered coupon on the right-dual boundary
object.  This is a rigidity statement: it does not change the component label
and does not mention a dotted-disk intersection sign.
-/
theorem characterCoupon_negativeExponent_rightMate
    (𝒞η : TwistedPremodularCategory K)
    (simple : 𝒞η.category.simples.Simple)
    (exponent : ℤ) :
    (isoIntPowerHom
        (𝒞η.character.iso.app
          (𝒞η.category.simples.simpleObject simple))
        (-exponent))ᘁ =
      isoIntPowerHom
        (𝒞η.character.iso.app
          ((𝒞η.category.simples.simpleObject simple)ᘁ))
        exponent := by
  calc
    _ = (((𝒞η.character.value simple) ^ (-exponent) : Kˣ) : K) •
          𝟙 ((𝒞η.category.simples.simpleObject simple)ᘁ) := by
      rw [characterCoupon_on_forwardSimple]
      exact TensorIdentityCharacter.rightAdjointMate_smul_identity
        (((𝒞η.character.value simple) ^ (-exponent) : Kˣ) : K)
        (𝒞η.category.simples.simpleObject simple)
    _ = _ :=
      (characterCoupon_on_dualSimple
        𝒞η.character simple exponent).symm

/--
At a cut-boundary endpoint, one uniform character coupon has the scalar
prescribed by the orientation of that ribbon strand.  The independent
intersection sign with the dotted disk plays no role in choosing `X` or `Xᘁ`.
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
          (strandCharacterExponentSign
              (diagram.trace.strands puncture.inputStrand).orientation *
            exponent) : Kˣ) : K) •
        𝟙
          (orientedSimpleObject 𝒞η.category
            (orientedExteriorStrand
              𝒞η.category diagram labeling puncture.inputStrand)) := by
  cases orientation :
      (diagram.trace.strands puncture.inputStrand).orientation with
  | positive =>
      unfold orientedSimpleObject orientedExteriorStrand
      rw [orientation]
      simp only [ribbonDirectionOfStrandOrientation]
      simpa [strandCharacterExponentSign, orientation] using
        characterCoupon_on_forwardSimple
          𝒞η.character
          (exteriorStrandLabel
            𝒞η.category diagram labeling puncture.inputStrand)
          exponent
  | negative =>
      unfold orientedSimpleObject orientedExteriorStrand
      rw [orientation]
      simp only [ribbonDirectionOfStrandOrientation]
      simpa [strandCharacterExponentSign, orientation] using
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
        (strandCharacterExponentSign
            (diagram.trace.strands puncture.inputStrand).orientation *
          exponent) : Kˣ) : K)).prod

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
                  (strandCharacterExponentSign
                      (diagram.trace.strands
                        puncture.inputStrand).orientation *
                    exponent) : Kˣ) : K))
              rest).prod =
            (List.map
              (fun puncture =>
                𝒞η.character.simpleScalar
                    (exteriorStrandLabel
                      𝒞η.category diagram labeling puncture.inputStrand) ^
                  (strandCharacterExponentSign
                      (diagram.trace.strands
                        puncture.inputStrand).orientation *
                    exponent))
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
  eqToHom
      (congrArg (ribbonWordObject 𝒞)
        (exteriorInputWord_eq_cutBoundaryWord
          𝒞 diagram labeling punctures)) ≫
    tensorUnitProjector 𝒞
      (ribbonWordObject 𝒞
        (cutBoundaryWord 𝒞 diagram labeling punctures)) ≫
    eqToHom
      (congrArg (ribbonWordObject 𝒞)
        (exteriorOutputWord_eq_cutBoundaryWord
          𝒞 diagram labeling punctures).symm)

private theorem compile_projectorHole_eq_explicit
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (dotted : diagram.trace.ComponentId)
    (punctures : List (DottedPuncture diagram.trace))
    (pairing :
      (CutOpenEvent.projectorHole dotted punctures).StrandContinuationsAreWellFormed) :
    compileCutOpenEventMorphism
        𝒞 diagram labeling (.projectorHole dotted punctures) pairing =
      explicitProjectorHoleMorphism 𝒞 diagram labeling punctures := by
  unfold compileCutOpenEventMorphism explicitProjectorHoleMorphism
  simp only [CutOpenEvent.beforeWord, CutOpenEvent.afterWord, id_eq]

/--
A uniform character coupon on the exact input word of a certified dotted
collar is absorbed by the collar morphism.  Naturality transports the coupon
through `bendIn`; the tensor-unit projector then absorbs it at the waist.
-/
theorem characterCoupon_dottedCollar_left
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted)
    (script : DottedCollarScript diagram.trace
      (diagram.dottedCuts.punctureWord dotted role))
    (exactPaths : script.HasExactBendingPaths)
    (exponent : ℤ) :
    isoIntPowerHom
        (𝒞η.character.iso.app
          (ribbonWordObject 𝒞η.category
            (exteriorWord 𝒞η.category diagram labeling
              ((diagram.dottedCuts.punctureWord dotted role).map
                DottedPuncture.inputStrand))))
        exponent ≫
      compileDottedCollarMorphism
        𝒞η.category diagram labeling dotted role script exactPaths =
      compileDottedCollarMorphism
        𝒞η.category diagram labeling dotted role script exactPaths := by
  let inputObject :=
    ribbonWordObject 𝒞η.category
      (exteriorWord 𝒞η.category diagram labeling
        ((diagram.dottedCuts.punctureWord dotted role).map
          DottedPuncture.inputStrand))
  let waistObject :=
    ribbonWordObject 𝒞η.category
      (exteriorWord 𝒞η.category diagram labeling script.waistWord)
  let bendIn : inputObject ⟶ waistObject :=
    compileDottedCollarBendingPathMorphism
      𝒞η.category diagram labeling script.bendIn exactPaths.1
  let bendOut :=
    compileDottedCollarBendingPathMorphism
      𝒞η.category diagram labeling script.bendOut exactPaths.2
  have move_coupon :
      isoIntPowerHom (𝒞η.character.iso.app inputObject) exponent ≫ bendIn =
        bendIn ≫
          isoIntPowerHom (𝒞η.character.iso.app waistObject) exponent :=
    characterCoupon_naturality 𝒞η.character bendIn exponent
  have absorbed :
      isoIntPowerHom (𝒞η.character.iso.app waistObject) exponent ≫
          tensorUnitProjector 𝒞η.category waistObject =
        tensorUnitProjector 𝒞η.category waistObject :=
    characterCoupon_tensorUnitProjector_left
      𝒞η.character waistObject exponent
  change
    isoIntPowerHom (𝒞η.character.iso.app inputObject) exponent ≫
          bendIn ≫ tensorUnitProjector 𝒞η.category waistObject ≫ bendOut =
      bendIn ≫ tensorUnitProjector 𝒞η.category waistObject ≫ bendOut
  calc
    _ = (isoIntPowerHom
          (𝒞η.character.iso.app inputObject) exponent ≫ bendIn) ≫
          tensorUnitProjector 𝒞η.category waistObject ≫ bendOut := by
        simp only [Category.assoc]
    _ = (bendIn ≫
          isoIntPowerHom (𝒞η.character.iso.app waistObject) exponent) ≫
          tensorUnitProjector 𝒞η.category waistObject ≫ bendOut := by
        exact congrArg
          (fun first => first ≫
            tensorUnitProjector 𝒞η.category waistObject ≫ bendOut)
          move_coupon
    _ = bendIn ≫
          (isoIntPowerHom (𝒞η.character.iso.app waistObject) exponent ≫
            tensorUnitProjector 𝒞η.category waistObject) ≫ bendOut := by
        simp only [Category.assoc]
    _ = _ := by
      exact congrArg
        (fun middle => bendIn ≫ middle ≫ bendOut) absorbed

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
      (CutOpenEvent.projectorHole dotted punctures).StrandContinuationsAreWellFormed)
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
  simp only [CutOpenEvent.beforeWord]
  let X :=
    ribbonWordObject 𝒞η.category
      (exteriorWord 𝒞η.category diagram labeling
        (punctures.map DottedPuncture.inputStrand))
  let W :=
    ribbonWordObject 𝒞η.category
      (cutBoundaryWord 𝒞η.category diagram labeling punctures)
  let Y :=
    ribbonWordObject 𝒞η.category
      (exteriorWord 𝒞η.category diagram labeling
        (punctures.map DottedPuncture.outputStrand))
  let inputMap : X ⟶ W :=
    eqToHom
      (congrArg (ribbonWordObject 𝒞η.category)
        (exteriorInputWord_eq_cutBoundaryWord
          𝒞η.category diagram labeling punctures))
  let outputMap : W ⟶ Y :=
    eqToHom
      (congrArg (ribbonWordObject 𝒞η.category)
        (exteriorOutputWord_eq_cutBoundaryWord
          𝒞η.category diagram labeling punctures).symm)
  have move_coupon :
      isoIntPowerHom (𝒞η.character.iso.app X) exponent ≫ inputMap =
        inputMap ≫
          isoIntPowerHom (𝒞η.character.iso.app W) exponent :=
    characterCoupon_naturality 𝒞η.character inputMap exponent
  have absorbed :
      isoIntPowerHom (𝒞η.character.iso.app W) exponent ≫
          tensorUnitProjector 𝒞η.category W =
        tensorUnitProjector 𝒞η.category W :=
    characterCoupon_tensorUnitProjector_left
      𝒞η.character W exponent
  change
    isoIntPowerHom (𝒞η.character.iso.app X) exponent ≫
          inputMap ≫ tensorUnitProjector 𝒞η.category W ≫ outputMap =
      inputMap ≫ tensorUnitProjector 𝒞η.category W ≫ outputMap
  calc
    isoIntPowerHom (𝒞η.character.iso.app X) exponent ≫
          (inputMap ≫
            (tensorUnitProjector 𝒞η.category W ≫ outputMap)) =
        (isoIntPowerHom (𝒞η.character.iso.app X) exponent ≫
          inputMap) ≫
            (tensorUnitProjector 𝒞η.category W ≫ outputMap) := by
              rw [Category.assoc]
    _ = (inputMap ≫
          isoIntPowerHom (𝒞η.character.iso.app W) exponent) ≫
            (tensorUnitProjector 𝒞η.category W ≫ outputMap) := by
              rw [move_coupon]
              rfl
    _ = inputMap ≫
          (isoIntPowerHom (𝒞η.character.iso.app W) exponent ≫
            (tensorUnitProjector 𝒞η.category W ≫ outputMap)) := by
              rw [Category.assoc]
    _ = inputMap ≫
          ((isoIntPowerHom (𝒞η.character.iso.app W) exponent ≫
            tensorUnitProjector 𝒞η.category W) ≫ outputMap) := by
              rw [Category.assoc]
    _ = inputMap ≫
          (tensorUnitProjector 𝒞η.category W ≫ outputMap) := by
              exact congrArg
                (fun middle => inputMap ≫ (middle ≫ outputMap)) absorbed

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
      (CutOpenEvent.projectorHole dotted punctures).StrandContinuationsAreWellFormed)
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
  let compiled :=
    compileCutOpenEventMorphism
      𝒞η.category diagram labeling
      (.projectorHole dotted punctures) pairing
  have scalar_identity_comp :
      punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
          compiled =
        (punctureWordCharacterUnit
          𝒞η diagram labeling punctures exponent • CategoryStruct.id X) ≫
          compiled := by
    simpa only [Category.id_comp] using
      (Linear.smul_comp X X _
        (punctureWordCharacterUnit
          𝒞η diagram labeling punctures exponent)
        (CategoryStruct.id X) compiled).symm
  have scalar_as_coupon :
      punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
          compileCutOpenEventMorphism
            𝒞η.category diagram labeling
            (.projectorHole dotted punctures) pairing =
        isoIntPowerHom (𝒞η.character.iso.app X) exponent ≫
          compileCutOpenEventMorphism
            𝒞η.category diagram labeling
            (.projectorHole dotted punctures) pairing := by
    change
      punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
          compiled =
        isoIntPowerHom (𝒞η.character.iso.app X) exponent ≫ compiled
    calc
      _ = (punctureWordCharacterUnit
          𝒞η diagram labeling punctures exponent • CategoryStruct.id X) ≫
            compiled := scalar_identity_comp
      _ = _ := congrArg (fun map => map ≫ compiled) coupon_eq.symm
  exact scalar_as_coupon.trans
    (characterCoupon_projectorHole_left
      𝒞η diagram labeling dotted punctures pairing exponent)

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
      (CutOpenEvent.projectorHole dotted punctures).StrandContinuationsAreWellFormed)
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

/--
An event identified with a projector hole inherits the projector-hole
absorption theorem.  Keeping the event as an explicit variable lets Lean
transport its pairing proof and its source/target words together.
-/
theorem compileEvent_absorbs_of_eq_projectorHole
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (event : CutOpenEvent diagram.trace)
    (dotted : diagram.trace.ComponentId)
    (punctures : List (DottedPuncture diagram.trace))
    (event_eq : event = .projectorHole dotted punctures)
    (pairing : event.StrandContinuationsAreWellFormed)
    (exponent : ℤ) :
    punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
        compileCutOpenEventMorphism
          𝒞η.category diagram labeling event pairing =
      compileCutOpenEventMorphism
        𝒞η.category diagram labeling event pairing := by
  subst event
  exact punctureWordCharacterUnit_smul_projectorHole
    𝒞η diagram labeling dotted punctures pairing exponent

/--
If an exact event of the frozen trace is the recorded projector hole, then
the corresponding fully contextualized compiled edge absorbs the signed
puncture-word character scalar.
-/
theorem contextualTraceEdge_absorbs_of_projectorSite
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (site : Fin diagram.dottedCuts.exterior.eventCount)
    (dotted : diagram.trace.ComponentId)
    (punctures : List (DottedPuncture diagram.trace))
    (site_exact :
      diagram.dottedCuts.exterior.events site =
        .projectorHole dotted punctures)
    (exponent : ℤ) :
    punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
        compileContextualCutOpenEventMorphism
          𝒞η.category diagram labeling site =
      compileContextualCutOpenEventMorphism
        𝒞η.category diagram labeling site := by
  let event := diagram.dottedCuts.exterior.events site
  let left := eventLeftContext diagram site
  let right := eventRightContext diagram site
  have before_object_eq :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞η.category
          (exteriorWord 𝒞η.category diagram labeling word))
      (eventTransitionEquations diagram site).1
  have after_object_eq :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞η.category
          (exteriorWord 𝒞η.category diagram labeling word))
      (eventTransitionEquations diagram site).2
  have before_context_object_eq :
      ribbonWordObject 𝒞η.category
          (exteriorWord 𝒞η.category diagram labeling
            (left ++ event.beforeWord ++ right)) =
        ribbonWordObject 𝒞η.category
          (List.append
            (List.append
              (exteriorWord 𝒞η.category diagram labeling left)
              (exteriorWord 𝒞η.category diagram labeling event.beforeWord))
            (exteriorWord 𝒞η.category diagram labeling right)) := by
    simp [exteriorWord, List.map_append]
  have after_context_object_eq :
      ribbonWordObject 𝒞η.category
          (exteriorWord 𝒞η.category diagram labeling
            (left ++ event.afterWord ++ right)) =
        ribbonWordObject 𝒞η.category
          (List.append
            (List.append
              (exteriorWord 𝒞η.category diagram labeling left)
              (exteriorWord 𝒞η.category diagram labeling event.afterWord))
            (exteriorWord 𝒞η.category diagram labeling right)) := by
    simp [exteriorWord, List.map_append]
  have event_absorbed :
      punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
          compileCutOpenEventMorphism
            𝒞η.category diagram labeling event
            (diagram.dottedCuts.exterior.strandContinuationsAreWellFormed site) =
        compileCutOpenEventMorphism
          𝒞η.category diagram labeling event
          (diagram.dottedCuts.exterior.strandContinuationsAreWellFormed site) := by
    exact compileEvent_absorbs_of_eq_projectorHole
      𝒞η diagram labeling event dotted punctures
      (by simpa only [event] using site_exact)
      (diagram.dottedCuts.exterior.strandContinuationsAreWellFormed site)
      exponent
  have middle_absorbed :=
    contextualizeRibbonMorphism_absorbs
      𝒞η.category
      (exteriorWord 𝒞η.category diagram labeling left)
      (exteriorWord 𝒞η.category diagram labeling event.beforeWord)
      (exteriorWord 𝒞η.category diagram labeling event.afterWord)
      (exteriorWord 𝒞η.category diagram labeling right)
      (compileCutOpenEventMorphism
        𝒞η.category diagram labeling event
        (diagram.dottedCuts.exterior.strandContinuationsAreWellFormed site))
      (punctureWordCharacterUnit
        𝒞η diagram labeling punctures exponent)
      event_absorbed
  have whole_absorbed :=
    comp_middle_absorbs
      (eqToHom before_object_eq ≫
        eqToHom before_context_object_eq)
      (contextualizeRibbonMorphism 𝒞η.category
        (exteriorWord 𝒞η.category diagram labeling left)
        (exteriorWord 𝒞η.category diagram labeling event.beforeWord)
        (exteriorWord 𝒞η.category diagram labeling event.afterWord)
        (exteriorWord 𝒞η.category diagram labeling right)
        (compileCutOpenEventMorphism
          𝒞η.category diagram labeling event
          (diagram.dottedCuts.exterior.strandContinuationsAreWellFormed site)))
      (eqToHom after_context_object_eq.symm ≫
        eqToHom after_object_eq.symm)
      (punctureWordCharacterUnit
        𝒞η diagram labeling punctures exponent)
      middle_absorbed
  unfold compileContextualCutOpenEventMorphism
  simpa only [event, left, right, Category.assoc] using whole_absorbed

/--
The projector site selected by `DottedCutData` is therefore an absorbing edge
of the actual frozen evaluator trace.
-/
theorem projectorSite_contextualTraceEdge_absorbs
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted)
    (exponent : ℤ) :
    let punctures := diagram.dottedCuts.punctureWord dotted role
    let site := diagram.dottedCuts.projectorSite dotted role
    punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
        compileContextualCutOpenEventMorphism
          𝒞η.category diagram labeling site =
      compileContextualCutOpenEventMorphism
        𝒞η.category diagram labeling site := by
  dsimp only
  exact contextualTraceEdge_absorbs_of_projectorSite
    𝒞η diagram labeling
    (diagram.dottedCuts.projectorSite dotted role)
    dotted
    (diagram.dottedCuts.punctureWord dotted role)
    (diagram.dottedCuts.projectorSite_exact dotted role)
    exponent

/--
If one edge of a finite composable trace absorbs a scalar, then every prefix
ending strictly after that edge absorbs the same scalar.  The proof does not
inspect any other event in the trace.
-/
theorem FiniteMorphismTrace.composePrefix_absorbs_of_edge
    {C : Type*} [Category C] [Preadditive C] [Linear K C]
    {eventCount : ℕ}
    (trace : FiniteMorphismTrace C eventCount)
    (scalar : K)
    (site : Fin eventCount)
    (edge_absorbed : scalar • trace.edge site = trace.edge site) :
    ∀ (k : ℕ) (bound : k ≤ eventCount),
      site.val < k →
      scalar • trace.composePrefix k bound =
        trace.composePrefix k bound := by
  intro k
  induction k with
  | zero =>
      intro bound site_before
      omega
  | succ k ih =>
      intro bound site_before
      rw [FiniteMorphismTrace.composePrefix]
      by_cases site_is_last : site.val = k
      · have site_eq :
            site = (⟨k, Nat.lt_of_succ_le bound⟩ : Fin eventCount) :=
          Fin.ext site_is_last
        subst site
        calc
          scalar •
              (trace.composePrefix k
                  (Nat.le_trans (Nat.le_succ k) bound) ≫
                trace.edge ⟨k, Nat.lt_of_succ_le bound⟩) =
                trace.composePrefix k
                  (Nat.le_trans (Nat.le_succ k) bound) ≫
                (scalar •
                  trace.edge ⟨k, Nat.lt_of_succ_le bound⟩) := by
                    symm
                    apply Linear.comp_smul
          _ = trace.composePrefix k
                  (Nat.le_trans (Nat.le_succ k) bound) ≫
                trace.edge ⟨k, Nat.lt_of_succ_le bound⟩ := by
                  rw [edge_absorbed]
      · have site_before_prefix : site.val < k := by omega
        have prefix_absorbed :=
          ih
            (Nat.le_trans (Nat.le_succ k) bound)
            site_before_prefix
        calc
          scalar •
              (trace.composePrefix k
                  (Nat.le_trans (Nat.le_succ k) bound) ≫
                trace.edge ⟨k, Nat.lt_of_succ_le bound⟩) =
              (scalar •
                trace.composePrefix k
                  (Nat.le_trans (Nat.le_succ k) bound)) ≫
                trace.edge ⟨k, Nat.lt_of_succ_le bound⟩ := by
                  symm
                  apply Linear.smul_comp
          _ = trace.composePrefix k
                  (Nat.le_trans (Nat.le_succ k) bound) ≫
                trace.edge ⟨k, Nat.lt_of_succ_le bound⟩ := by
                  rw [prefix_absorbed]

/-- A scalar absorbed by one edge is absorbed by the complete finite trace. -/
theorem FiniteMorphismTrace.composeAll_absorbs_of_edge
    {C : Type*} [Category C] [Preadditive C] [Linear K C]
    {eventCount : ℕ}
    (trace : FiniteMorphismTrace C eventCount)
    (scalar : K)
    (site : Fin eventCount)
    (edge_absorbed : scalar • trace.edge site = trace.edge site) :
    scalar • trace.composeAll = trace.composeAll := by
  unfold FiniteMorphismTrace.composeAll
  exact
    TwistedYetter.Kirby.Final.Proofs.FiniteMorphismTrace.composePrefix_absorbs_of_edge
      trace scalar site edge_absorbed
      eventCount (Nat.le_refl eventCount) site.isLt

/--
The signed character scalar associated with one dotted puncture word is
absorbed by the complete closed cut-open diagram compiled by the frozen
evaluator.
-/
theorem projectorSite_compileCutOpenExteriorMorphism_absorbs
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted)
    (exponent : ℤ) :
    let punctures := diagram.dottedCuts.punctureWord dotted role
    punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent •
        compileCutOpenExteriorMorphism 𝒞η.category diagram labeling =
      compileCutOpenExteriorMorphism 𝒞η.category diagram labeling := by
  dsimp only
  let trace : FiniteMorphismTrace 𝒞η.category.C
      diagram.dottedCuts.exterior.eventCount :=
    {
      object := fun i =>
        ribbonWordObject 𝒞η.category
          (exteriorWord 𝒞η.category diagram labeling
            (diagram.dottedCuts.exterior.activeOrder i))
      edge := fun i =>
        compileContextualCutOpenEventMorphism
          𝒞η.category diagram labeling i
    }
  have initial_object_eq :
      trace.object 0 = 𝟙_ 𝒞η.category.C :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞η.category
          (exteriorWord 𝒞η.category diagram labeling word))
      diagram.dottedCuts.exterior.initialBoundaryEmpty
  have final_object_eq :
      trace.object (Fin.last diagram.dottedCuts.exterior.eventCount) =
        𝟙_ 𝒞η.category.C :=
    congrArg
      (fun word =>
        ribbonWordObject 𝒞η.category
          (exteriorWord 𝒞η.category diagram labeling word))
      diagram.dottedCuts.exterior.finalBoundaryEmpty
  let site := diagram.dottedCuts.projectorSite dotted role
  have edge_absorbed :
      punctureWordCharacterUnit 𝒞η diagram labeling
            (diagram.dottedCuts.punctureWord dotted role) exponent •
          trace.edge site =
        trace.edge site := by
    exact projectorSite_contextualTraceEdge_absorbs
      𝒞η diagram labeling dotted role exponent
  have trace_absorbed :
      punctureWordCharacterUnit 𝒞η diagram labeling
            (diagram.dottedCuts.punctureWord dotted role) exponent •
          trace.composeAll =
        trace.composeAll :=
    TwistedYetter.Kirby.Final.Proofs.FiniteMorphismTrace.composeAll_absorbs_of_edge
      trace
      (punctureWordCharacterUnit 𝒞η diagram labeling
        (diagram.dottedCuts.punctureWord dotted role) exponent)
      site edge_absorbed
  have closed_absorbed :=
    comp_middle_absorbs
      (eqToHom initial_object_eq.symm)
      trace.composeAll
      (eqToHom final_object_eq)
      (punctureWordCharacterUnit 𝒞η diagram labeling
        (diagram.dottedCuts.punctureWord dotted role) exponent)
      trace_absorbed
  unfold compileCutOpenExteriorMorphism
  simpa only [trace, initial_object_eq, final_object_eq, Category.assoc] using
    closed_absorbed

/--
After applying the canonical closed-diagram evaluation, the same signed
puncture-word scalar still acts trivially.
-/
theorem projectorSite_canonicalEvaluation_absorbs
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted)
    (exponent : ℤ) :
    let punctures := diagram.dottedCuts.punctureWord dotted role
    punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (.morphism
            (compileCutOpenExteriorMorphism
              𝒞η.category diagram labeling)) =
      canonicalRibbonGraphicalEvaluation 𝒞η.category
        (.morphism
          (compileCutOpenExteriorMorphism
            𝒞η.category diagram labeling)) := by
  dsimp only [canonicalRibbonGraphicalEvaluation,
    RibbonExpression.interpret]
  have morphism_absorbed :=
    projectorSite_compileCutOpenExteriorMorphism_absorbs
      𝒞η diagram labeling dotted role exponent
  have scalar_absorbed :=
    congrArg 𝒞η.category.closedScalar morphism_absorbed
  simpa [PremodularFusionCategory.closedScalar] using scalar_absorbed

/--
A signed accumulator over a finite list is its initial value plus the finite
sum of the selected occurrence weights.
-/
private theorem foldl_add_if_eq_add_sum_get
    {α : Type*}
    (items : List α)
    (selected : α → Prop)
    [DecidablePred selected]
    (weight : α → ℤ)
    (initial : ℤ) :
    items.foldl
        (fun total item =>
          if selected item then total + weight item else total)
        initial =
      initial +
        ∑ index : Fin items.length,
          if selected (items.get index) then
            weight (items.get index)
          else
            0 := by
  induction items generalizing initial with
  | nil =>
      simp
  | cons head tail ih =>
      simp only [List.foldl]
      rw [ih]
      change
        (if selected head then initial + weight head else initial) +
            (∑ index : Fin tail.length,
              if selected (tail.get index) then
                weight (tail.get index)
              else
                0) =
          initial +
            ∑ index : Fin (tail.length + 1),
              if selected ((head :: tail).get index) then
                weight ((head :: tail).get index)
              else
                0
      rw [Fin.sum_univ_succ]
      by_cases head_selected : selected head
      · simp [head_selected, add_assoc]
      · simp [head_selected]

/-- Signed contribution of one puncture to one fixed two-handle incidence. -/
private noncomputable def punctureIncidenceContribution
    {trace : CombinatorialLinkTrace}
    (twoHandle : trace.ComponentId)
    (puncture : DottedPuncture trace) : ℤ := by
  classical
  exact
    if puncture.twoHandleComponent = twoHandle then
      puncture.direction.intersectionSign
    else
      0

/--
The frozen primal `2 → 1` incidence coefficient is exactly the signed sum of
the corresponding puncture occurrences.  This unfolds, rather than assumes,
the incidence convention used by the turnover complex.
-/
theorem twoOneIncidence_eq_sum_punctureOccurrences
    (diagram : CombinatorialSpecialKirbyDiagram)
    (one : Fin diagram.handles.hOne)
    (two : Fin diagram.handles.hTwo) :
    let dotted := diagram.handles.oneHandleIndex one
    let twoHandle := diagram.handles.twoHandleIndex two
    let punctures :=
      diagram.dottedCuts.punctureWord dotted.1 dotted.2
    twoOneIncidence diagram one two =
      ∑ index : Fin punctures.length,
        punctureIncidenceContribution twoHandle.1
          (punctures.get index) := by
  classical
  dsimp only
  unfold twoOneIncidence
  simpa only [zero_add, punctureIncidenceContribution] using
    foldl_add_if_eq_add_sum_get
      (diagram.dottedCuts.punctureWord
        (diagram.handles.oneHandleIndex one).1
        (diagram.handles.oneHandleIndex one).2)
      (fun puncture =>
        puncture.twoHandleComponent =
          (diagram.handles.twoHandleIndex two).1)
      (fun puncture => puncture.direction.intersectionSign)
      0

/-- The unique primal two-handle index carried by one puncture occurrence. -/
private def punctureTwoHandleIndex
    (diagram : CombinatorialSpecialKirbyDiagram)
    (puncture : DottedPuncture diagram.trace) :
    Fin diagram.handles.hTwo :=
  diagram.handles.twoHandleIndex.symm
    ⟨puncture.twoHandleComponent, puncture.two_handle_role⟩

/-- The exterior compiler reads the same two-handle label as the puncture. -/
theorem exteriorStrandLabel_puncture_eq_labeling
    (𝒞 : PremodularFusionCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (puncture : DottedPuncture diagram.trace) :
    exteriorStrandLabel 𝒞 diagram labeling puncture.inputStrand =
      labeling (punctureTwoHandleIndex diagram puncture) := by
  unfold exteriorStrandLabel punctureTwoHandleIndex
  simp only [puncture.input_on_two_handle]
  split
  · congr
  · rename_i role_is_dotted
    exact False.elim (role_is_dotted puncture.two_handle_role)

/-- Component equality and the corresponding two-handle index equality agree. -/
private theorem punctureTwoHandleIndex_eq_iff
    (diagram : CombinatorialSpecialKirbyDiagram)
    (puncture : DottedPuncture diagram.trace)
    (two : Fin diagram.handles.hTwo) :
    punctureTwoHandleIndex diagram puncture = two ↔
      puncture.twoHandleComponent =
        (diagram.handles.twoHandleIndex two).1 := by
  constructor
  · intro index_eq
    have component_eq := congrArg
      (fun index => (diagram.handles.twoHandleIndex index).1)
      index_eq
    simpa [punctureTwoHandleIndex] using component_eq
  · intro component_eq
    apply diagram.handles.twoHandleIndex.injective
    apply Subtype.ext
    simpa [punctureTwoHandleIndex] using component_eq

/-- A finite product of powers with common base is the power of the sum. -/
private theorem finset_prod_zpow_eq_zpow_sum
    {G : Type*} [CommGroup G]
    {ι : Type*}
    (items : Finset ι)
    (base : G)
    (exponent : ι → ℤ) :
    (∏ item ∈ items, base ^ exponent item) =
      base ^ (∑ item ∈ items, exponent item) := by
  classical
  induction items using Finset.induction_on with
  | empty =>
      simp
  | @insert item items not_mem ih =>
      simp [not_mem, ih, zpow_add]

/-- A list product is the corresponding product over its finite positions. -/
private theorem list_map_prod_eq_fin_prod_get
    {α M : Type*} [CommMonoid M]
    (items : List α)
    (map : α → M) :
    (items.map map).prod =
      ∏ index : Fin items.length, map (items.get index) := by
  simpa using (Fin.prod_univ_fun_getElem items map).symm

/--
For one dotted handle, the puncture-word character factor is the product over
two-handle labels with exponents given by the frozen incidence row.
-/
theorem punctureWordCharacterUnit_eq_incidenceProduct
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (one : Fin diagram.handles.hOne)
    (exponent : ℤ) :
    let dotted := diagram.handles.oneHandleIndex one
    let punctures :=
      diagram.dottedCuts.punctureWord dotted.1 dotted.2
    punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent =
      ((∏ two,
        𝒞η.character.value (labeling two) ^
          (twoOneIncidence diagram one two * exponent) : Kˣ) : K) := by
  classical
  dsimp only
  let punctures :=
    diagram.dottedCuts.punctureWord
      (diagram.handles.oneHandleIndex one).1
      (diagram.handles.oneHandleIndex one).2
  have occurrence_label :
      ∀ index : Fin punctures.length,
        exteriorStrandLabel 𝒞η.category diagram labeling
            (punctures.get index).inputStrand =
          labeling (punctureTwoHandleIndex diagram
            (punctures.get index)) := by
    intro index
    exact exteriorStrandLabel_puncture_eq_labeling
      𝒞η.category diagram labeling (punctures.get index)
  have fiber_product :
      (∏ two : Fin diagram.handles.hTwo,
          ∏ index : Fin punctures.length with
            punctureTwoHandleIndex diagram (punctures.get index) = two,
            𝒞η.character.value (labeling two) ^
              ((punctures.get index).direction.intersectionSign * exponent)) =
        ∏ index : Fin punctures.length,
          𝒞η.character.value
              (labeling
                (punctureTwoHandleIndex diagram (punctures.get index))) ^
            ((punctures.get index).direction.intersectionSign * exponent) := by
    calc
      _ = ∏ two : Fin diagram.handles.hTwo,
          ∏ index : Fin punctures.length with
            punctureTwoHandleIndex diagram (punctures.get index) = two,
            𝒞η.character.value
                (labeling
                  (punctureTwoHandleIndex diagram (punctures.get index))) ^
              ((punctures.get index).direction.intersectionSign * exponent) := by
            apply Finset.prod_congr rfl
            intro two _
            apply Finset.prod_congr rfl
            intro index index_mem
            rw [(Finset.mem_filter.mp index_mem).2]
      _ = _ :=
        Finset.prod_fiberwise
          (Finset.univ : Finset (Fin punctures.length))
          (fun index =>
            punctureTwoHandleIndex diagram (punctures.get index))
          (fun index =>
            𝒞η.character.value
                (labeling
                  (punctureTwoHandleIndex diagram (punctures.get index))) ^
              ((punctures.get index).direction.intersectionSign * exponent))
  rw [show
    punctureWordCharacterUnit 𝒞η diagram labeling punctures exponent =
      ((∏ index : Fin punctures.length,
        𝒞η.character.value
            (exteriorStrandLabel 𝒞η.category diagram labeling
              (punctures.get index).inputStrand) ^
          ((punctures.get index).direction.intersectionSign * exponent) :
        Kˣ) : K) by
      unfold punctureWordCharacterUnit
      rw [list_map_prod_eq_fin_prod_get]
      simp]
  apply congrArg Units.val
  change
    (∏ index : Fin punctures.length,
      𝒞η.character.value
          (exteriorStrandLabel 𝒞η.category diagram labeling
            (punctures.get index).inputStrand) ^
        ((punctures.get index).direction.intersectionSign * exponent)) =
      ∏ two,
        𝒞η.character.value (labeling two) ^
          (twoOneIncidence diagram one two * exponent)
  rw [show
    (∏ index : Fin punctures.length,
      𝒞η.character.value
          (exteriorStrandLabel 𝒞η.category diagram labeling
            (punctures.get index).inputStrand) ^
        ((punctures.get index).direction.intersectionSign * exponent)) =
      ∏ index : Fin punctures.length,
        𝒞η.character.value
            (labeling
              (punctureTwoHandleIndex diagram (punctures.get index))) ^
          ((punctures.get index).direction.intersectionSign * exponent) by
      apply Finset.prod_congr rfl
      intro index _
      rw [occurrence_label index]]
  rw [← fiber_product]
  apply Finset.prod_congr rfl
  intro two _
  rw [finset_prod_zpow_eq_zpow_sum]
  congr 1
  rw [← Finset.sum_mul]
  rw [twoOneIncidence_eq_sum_punctureOccurrences]
  congr 1
  unfold punctureIncidenceContribution
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact punctureTwoHandleIndex_eq_iff
      diagram (punctures.get index) two
  · intro index _
    rfl

/--
The coordinate of a THAM degree-three boundary is the corresponding
incidence-column pairing with the one-handle chain.
-/
theorem thamBoundaryThree_apply_eq_sum_incidence
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (oneChain : HandleChainGroup diagram.handles.hOne)
    (two : Fin diagram.handles.hTwo) :
    primal.thamBoundaryThree oneChain two =
      ∑ one : Fin diagram.handles.hOne,
        twoOneIncidence diagram one two * oneChain one := by
  classical
  unfold PrimalDegreeThreeBoundaryData.thamBoundaryThree
    transposeAddHom coordinatePairing primalBoundaryTwo
  simp [coordinateUnit, eq_comm]

/--
Adding one THAM degree-three boundary multiplies the character weight by the
character product evaluated on that boundary.
-/
theorem characterWeight_add_thamBoundaryAsCycle
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (cycle : ThamTwoCycles primal)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    characterWeight 𝒞η labeling
        (cycle + thamBoundaryAsCycle primal oneChain) =
      characterWeight 𝒞η labeling cycle *
        ((∏ two : Fin diagram.handles.hTwo,
          𝒞η.character.value (labeling two) ^
            (primal.thamBoundaryThree oneChain two) : Kˣ) : K) := by
  unfold characterWeight
  change
    ((∏ two : Fin diagram.handles.hTwo,
      𝒞η.character.value (labeling two) ^
        (cycle.1 two + primal.thamBoundaryThree oneChain two) :
      Kˣ) : K) =
      ((∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^ cycle.1 two : Kˣ) : K) *
        ((∏ two : Fin diagram.handles.hTwo,
          𝒞η.character.value (labeling two) ^
            primal.thamBoundaryThree oneChain two : Kˣ) : K)
  simp only [zpow_add, Finset.prod_mul_distrib, Units.val_mul]

/--
The character factor of one THAM degree-three boundary is exactly the product
of the signed puncture-word factors over all dotted one-handles.
-/
theorem thamBoundaryCharacterProduct_eq_punctureWordProduct
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    ((∏ two : Fin diagram.handles.hTwo,
      𝒞η.character.value (labeling two) ^
        (primal.thamBoundaryThree oneChain two) : Kˣ) : K) =
      ∏ one : Fin diagram.handles.hOne,
        let dotted := diagram.handles.oneHandleIndex one
        punctureWordCharacterUnit 𝒞η diagram labeling
          (diagram.dottedCuts.punctureWord dotted.1 dotted.2)
          (oneChain one) := by
  classical
  have boundary_expansion :
      (∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^
          (primal.thamBoundaryThree oneChain two)) =
        ∏ two : Fin diagram.handles.hTwo,
          ∏ one : Fin diagram.handles.hOne,
            𝒞η.character.value (labeling two) ^
              (twoOneIncidence diagram one two * oneChain one) := by
    apply Finset.prod_congr rfl
    intro two _
    rw [thamBoundaryThree_apply_eq_sum_incidence
      diagram primal oneChain two]
    exact
      (finset_prod_zpow_eq_zpow_sum
        (Finset.univ : Finset (Fin diagram.handles.hOne))
        (𝒞η.character.value (labeling two))
        (fun one =>
          twoOneIncidence diagram one two * oneChain one)).symm
  rw [boundary_expansion]
  rw [Finset.prod_comm]
  rw [show
    ((∏ one : Fin diagram.handles.hOne,
      ∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^
          (twoOneIncidence diagram one two * oneChain one) : Kˣ) : K) =
      ∏ one : Fin diagram.handles.hOne,
        ((∏ two : Fin diagram.handles.hTwo,
          𝒞η.character.value (labeling two) ^
            (twoOneIncidence diagram one two * oneChain one) : Kˣ) : K) by
      simpa using
        Units.coe_prod
          (fun one : Fin diagram.handles.hOne =>
            ∏ two : Fin diagram.handles.hTwo,
              𝒞η.character.value (labeling two) ^
                (twoOneIncidence diagram one two * oneChain one))
          Finset.univ]
  apply Finset.prod_congr rfl
  intro one _
  exact
    (punctureWordCharacterUnit_eq_incidenceProduct
      𝒞η diagram labeling one (oneChain one)).symm

/--
If every member of a finite family acts trivially on one scalar, then their
product acts trivially as well.
-/
private theorem finset_prod_mul_eq_of_each_mul_eq
    {ι M : Type*} [CommMonoid M]
    (items : Finset ι)
    (factor : ι → M)
    (value : M)
    (absorbs : ∀ item ∈ items, factor item * value = value) :
    (∏ item ∈ items, factor item) * value = value := by
  classical
  induction items using Finset.induction_on with
  | empty =>
      simp
  | @insert item items not_mem ih =>
      rw [Finset.prod_insert not_mem]
      rw [mul_assoc, ih]
      exact absorbs item (Finset.mem_insert_self item items)
      intro other other_mem
      exact absorbs other (Finset.mem_insert_of_mem other_mem)

/--
The product of all dotted puncture-word factors acts trivially on the
canonical closed graphical evaluation.
-/
theorem punctureWordProduct_canonicalEvaluation_absorbs
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    (∏ one : Fin diagram.handles.hOne,
      let dotted := diagram.handles.oneHandleIndex one
      punctureWordCharacterUnit 𝒞η diagram labeling
        (diagram.dottedCuts.punctureWord dotted.1 dotted.2)
        (oneChain one)) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (.morphism
            (compileCutOpenExteriorMorphism
              𝒞η.category diagram labeling)) =
      canonicalRibbonGraphicalEvaluation 𝒞η.category
        (.morphism
          (compileCutOpenExteriorMorphism
            𝒞η.category diagram labeling)) := by
  apply finset_prod_mul_eq_of_each_mul_eq
    (Finset.univ : Finset (Fin diagram.handles.hOne))
  intro one _
  let dotted := diagram.handles.oneHandleIndex one
  exact projectorSite_canonicalEvaluation_absorbs
    𝒞η diagram labeling dotted.1 dotted.2 (oneChain one)

/--
For one fixed two-handle labeling, adding a THAM degree-three boundary does
not change the character-weighted canonical graphical evaluation.
-/
theorem characterWeight_mul_canonicalEvaluation_add_boundary
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (cycle : ThamTwoCycles primal)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    characterWeight 𝒞η labeling
          (cycle + thamBoundaryAsCycle primal oneChain) *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (.morphism
            (compileCutOpenExteriorMorphism
              𝒞η.category diagram labeling)) =
      characterWeight 𝒞η labeling cycle *
        canonicalRibbonGraphicalEvaluation 𝒞η.category
          (.morphism
            (compileCutOpenExteriorMorphism
              𝒞η.category diagram labeling)) := by
  let graphicalValue :=
    canonicalRibbonGraphicalEvaluation 𝒞η.category
      (.morphism
        (compileCutOpenExteriorMorphism
          𝒞η.category diagram labeling))
  let boundaryFactor :=
    ((∏ two : Fin diagram.handles.hTwo,
      𝒞η.character.value (labeling two) ^
        (primal.thamBoundaryThree oneChain two) : Kˣ) : K)
  calc
    _ =
        (characterWeight 𝒞η labeling cycle *
          boundaryFactor) * graphicalValue := by
      rw [characterWeight_add_thamBoundaryAsCycle
        𝒞η diagram primal labeling cycle oneChain]
    _ =
        characterWeight 𝒞η labeling cycle *
          (boundaryFactor * graphicalValue) := by
      rw [mul_assoc]
    _ =
        characterWeight 𝒞η labeling cycle *
          ((∏ one : Fin diagram.handles.hOne,
            let dotted := diagram.handles.oneHandleIndex one
            punctureWordCharacterUnit 𝒞η diagram labeling
              (diagram.dottedCuts.punctureWord dotted.1 dotted.2)
              (oneChain one)) * graphicalValue) := by
      dsimp only [boundaryFactor]
      rw [thamBoundaryCharacterProduct_eq_punctureWordProduct
        𝒞η diagram primal labeling oneChain]
    _ = _ := by
      dsimp only [graphicalValue]
      rw [punctureWordProduct_canonicalEvaluation_absorbs
        𝒞η diagram labeling oneChain]

/--
The complete frozen cycle evaluator is invariant under adding one THAM
degree-three boundary.
-/
theorem evaluateCycle_add_thamBoundaryAsCycle
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (cycle : ThamTwoCycles primal)
    (oneChain : HandleChainGroup diagram.handles.hOne) :
    evaluateCycle 𝒞η diagram primal
        (cycle + thamBoundaryAsCycle primal oneChain) =
      evaluateCycle 𝒞η diagram primal cycle := by
  unfold evaluateCycle
  apply congrArg
  apply Finset.sum_congr rfl
  intro labeling _
  dsimp only [canonicalRoleAwareGraphCompiler]
  let graphicalValue :=
    canonicalRibbonGraphicalEvaluation 𝒞η.category
      (.morphism
        (compileCutOpenExteriorMorphism
          𝒞η.category diagram labeling))
  calc
    ordinaryKirbyWeight 𝒞η.category labeling *
          characterWeight 𝒞η labeling
            (cycle + thamBoundaryAsCycle primal oneChain) *
        graphicalValue =
      ordinaryKirbyWeight 𝒞η.category labeling *
        (characterWeight 𝒞η labeling
            (cycle + thamBoundaryAsCycle primal oneChain) *
          graphicalValue) := by
      rw [mul_assoc]
    _ =
      ordinaryKirbyWeight 𝒞η.category labeling *
        (characterWeight 𝒞η labeling cycle *
          graphicalValue) := by
      rw [characterWeight_mul_canonicalEvaluation_add_boundary
        𝒞η diagram primal labeling cycle oneChain]
    _ =
      ordinaryKirbyWeight 𝒞η.category labeling *
          characterWeight 𝒞η labeling cycle *
        graphicalValue := by
      rw [mul_assoc]

/--
The frozen role-aware evaluator depends only on the THAM-side second homology
class, not on the chosen cycle representative.
-/
theorem frozenFrontendRepresentativeIndependence
    (𝒞η : TwistedPremodularCategory K)
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram) :
    RepresentativeIndependenceStatement
      𝒞η diagram primal := by
  intro left right same_class
  change
    (QuotientAddGroup.mk'
      (thamBoundaryAsCycle primal).range) left =
      (QuotientAddGroup.mk'
        (thamBoundaryAsCycle primal).range) right at same_class
  obtain ⟨boundary, boundary_mem, left_add_boundary_eq⟩ :=
    (QuotientAddGroup.mk'_eq_mk'
      (thamBoundaryAsCycle primal).range).mp same_class
  obtain ⟨oneChain, oneChain_eq⟩ := boundary_mem
  subst boundary
  rw [← left_add_boundary_eq]
  exact (evaluateCycle_add_thamBoundaryAsCycle
    𝒞η diagram primal left oneChain).symm

end

end TwistedYetter.Kirby.Final.Proofs
