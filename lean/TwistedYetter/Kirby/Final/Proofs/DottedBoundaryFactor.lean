import TwistedYetter.Kirby.Final.Proofs.DottedIncidenceNaturality

/-!
# Dotted-collar boundary factors

This file identifies the character factor of one THAM degree-three boundary
with the output-to-input ratio on the corresponding dotted collar.
Component colours, internal duality, and dotted incidence remain separate.
-/

namespace TwistedYetter.Kirby.Final.Proofs

open TwistedYetter.Semantics.Independent
open CategoryTheory

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
The character ratio between the public output and input component words of
one dotted collar.

The exponent is supplied once by the THAM-side degree-three chain.  Puncture
direction only partitions occurrences into the numerator or denominator; it
does not define a puncture-wise character exponent.
-/
def dottedBoundaryCharacterRatio
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (punctures : List (DottedPuncture diagram.trace))
    (exponent : ℤ) : Kˣ :=
  componentWordCharacterUnit 𝒞η
      ((dottedOutboundTwoHandleWord diagram punctures).map labeling)
      exponent *
    (componentWordCharacterUnit 𝒞η
      ((dottedInboundTwoHandleWord diagram punctures).map labeling)
      exponent)⁻¹

/--
The boundary ratio is definitionally the character product on the output
component word divided by the product on the input component word.
-/
theorem dottedBoundaryCharacterRatio_eq_output_mul_input_inv
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (punctures : List (DottedPuncture diagram.trace))
    (exponent : ℤ) :
    dottedBoundaryCharacterRatio
        𝒞η diagram labeling punctures exponent =
      componentWordCharacterUnit 𝒞η
          ((dottedOutboundTwoHandleWord diagram punctures).map labeling)
          exponent *
        (componentWordCharacterUnit 𝒞η
          ((dottedInboundTwoHandleWord diagram punctures).map labeling)
          exponent)⁻¹ := rfl

private def dottedOccurrenceCoefficient
    {trace : CombinatorialLinkTrace}
    (puncture : DottedPuncture trace)
    (twoHandle : trace.ComponentId) : ℤ := by
  classical
  exact
    if puncture.twoHandleComponent = twoHandle then
      match puncture.direction.incidenceSide with
      | .inbound => -1
      | .outbound => 1
    else
      0

private theorem dottedBoundaryCoefficient_eq_listSum
    {trace : CombinatorialLinkTrace}
    (punctures : List (DottedPuncture trace))
    (twoHandle : trace.ComponentId) :
    dottedBoundaryCoefficient punctures twoHandle =
      (punctures.map fun puncture =>
        dottedOccurrenceCoefficient puncture twoHandle).sum := by
  classical
  unfold dottedBoundaryCoefficient
  have fold_from :
      ∀ (items : List (DottedPuncture trace)) (total : ℤ),
        items.foldl
            (fun total puncture =>
              if puncture.twoHandleComponent = twoHandle then
                match puncture.direction.incidenceSide with
                | .inbound => total - 1
                | .outbound => total + 1
              else
                total)
            total =
          total +
            (items.map fun puncture =>
              dottedOccurrenceCoefficient puncture twoHandle).sum := by
    intro items
    induction items with
    | nil => simp
    | cons puncture rest ih =>
        intro total
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [ih]
        by_cases component_eq :
            puncture.twoHandleComponent = twoHandle
        · cases side : puncture.direction.incidenceSide <;>
            simp [dottedOccurrenceCoefficient, component_eq, side,
              add_assoc] <;> omega
        · simp [dottedOccurrenceCoefficient, component_eq]
  simpa using fold_from punctures 0

private theorem dottedPunctureTwoHandleIndex_eq_iff
    (diagram : SpecialKirbyDiagram)
    (puncture : DottedPuncture diagram.trace)
    (two : Fin diagram.handles.hTwo) :
    dottedPunctureTwoHandleIndex diagram puncture = two ↔
      puncture.twoHandleComponent =
        (diagram.handles.twoHandleIndex two).1 := by
  constructor
  · intro index_eq
    have component_eq := congrArg
      (fun index => (diagram.handles.twoHandleIndex index).1)
      index_eq
    simpa [dottedPunctureTwoHandleIndex] using component_eq
  · intro component_eq
    apply diagram.handles.twoHandleIndex.injective
    apply Subtype.ext
    simpa [dottedPunctureTwoHandleIndex] using component_eq

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
  | empty => simp
  | @insert item items not_mem ih =>
      simp [not_mem, ih, zpow_add]

private theorem list_map_prod_eq_fin_prod_get
    {α M : Type*} [CommMonoid M]
    (items : List α)
    (map : α → M) :
    (items.map map).prod =
      ∏ index : Fin items.length, map (items.get index) := by
  exact (Fin.prod_univ_fun_getElem items map).symm

private theorem list_map_sum_eq_fin_sum_get
    {α A : Type*} [AddCommMonoid A]
    (items : List α)
    (map : α → A) :
    (items.map map).sum =
      ∑ index : Fin items.length, map (items.get index) := by
  exact (Fin.sum_univ_fun_getElem items map).symm

private theorem dottedBoundaryCharacterRatio_eq_occurrenceProduct
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (punctures : List (DottedPuncture diagram.trace))
    (exponent : ℤ) :
    dottedBoundaryCharacterRatio
        𝒞η diagram labeling punctures exponent =
      (punctures.map fun puncture =>
        𝒞η.character.value
            (labeling (dottedPunctureTwoHandleIndex diagram puncture)) ^
          ((match puncture.direction.incidenceSide with
            | .inbound => -1
            | .outbound => 1) * exponent)).prod := by
  induction punctures with
  | nil =>
      simp [dottedBoundaryCharacterRatio,
        dottedInboundTwoHandleWord, dottedOutboundTwoHandleWord,
        dottedInboundPunctures, dottedOutboundPunctures,
        componentWordCharacterUnit]
  | cons puncture rest ih =>
      cases direction : puncture.direction with
      | withDiskOrientation =>
          have step := congrArg
            (fun ratio : Kˣ =>
              𝒞η.character.value
                  (labeling (dottedPunctureTwoHandleIndex diagram puncture)) ^
                  exponent * ratio)
            ih
          simpa [dottedBoundaryCharacterRatio,
            dottedInboundTwoHandleWord, dottedOutboundTwoHandleWord,
            dottedInboundPunctures, dottedOutboundPunctures,
            componentWordCharacterUnit, direction,
            PunctureDirection.incidenceSide, mul_assoc] using step
      | againstDiskOrientation =>
          have step := congrArg
            (fun ratio : Kˣ =>
              (𝒞η.character.value
                  (labeling (dottedPunctureTwoHandleIndex diagram puncture)) ^
                  exponent)⁻¹ * ratio)
            ih
          simpa [dottedBoundaryCharacterRatio,
            dottedInboundTwoHandleWord, dottedOutboundTwoHandleWord,
            dottedInboundPunctures, dottedOutboundPunctures,
            componentWordCharacterUnit, direction,
            PunctureDirection.incidenceSide, zpow_neg,
            mul_assoc, mul_left_comm, mul_comm] using step

/--
The output-to-input boundary ratio is the product over two-handle colours
with exponents given by the dotted output-minus-input incidence row.

The signed powers on the right are derived here from numerator versus
denominator.  They are not puncture data and are not evaluator exponents.
-/
theorem dottedBoundaryCharacterRatio_eq_incidenceProduct
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (punctures : List (DottedPuncture diagram.trace))
    (exponent : ℤ) :
    dottedBoundaryCharacterRatio
        𝒞η diagram labeling punctures exponent =
      ∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^
          (dottedBoundaryCoefficient punctures
            (diagram.handles.twoHandleIndex two).1 * exponent) := by
  classical
  rw [show
    dottedBoundaryCharacterRatio
        𝒞η diagram labeling punctures exponent =
      ∏ index : Fin punctures.length,
        𝒞η.character.value
            (labeling
              (dottedPunctureTwoHandleIndex diagram (punctures.get index))) ^
          ((match (punctures.get index).direction.incidenceSide with
            | .inbound => -1
            | .outbound => 1) * exponent) by
      rw [dottedBoundaryCharacterRatio_eq_occurrenceProduct]
      exact list_map_prod_eq_fin_prod_get _ _]
  rw [← Finset.prod_fiberwise
    (Finset.univ : Finset (Fin punctures.length))
    (fun index => dottedPunctureTwoHandleIndex diagram (punctures.get index))
    (fun index =>
      𝒞η.character.value
          (labeling
            (dottedPunctureTwoHandleIndex diagram (punctures.get index))) ^
        ((match (punctures.get index).direction.incidenceSide with
          | .inbound => -1
          | .outbound => 1) * exponent))]
  apply Finset.prod_congr rfl
  intro two _
  rw [show
    (∏ index : Fin punctures.length with
      dottedPunctureTwoHandleIndex diagram (punctures.get index) = two,
      𝒞η.character.value
          (labeling (dottedPunctureTwoHandleIndex diagram (punctures.get index))) ^
        ((match (punctures.get index).direction.incidenceSide with
          | .inbound => -1
          | .outbound => 1) * exponent)) =
      ∏ index : Fin punctures.length with
        dottedPunctureTwoHandleIndex diagram (punctures.get index) = two,
        𝒞η.character.value (labeling two) ^
          ((match (punctures.get index).direction.incidenceSide with
            | .inbound => -1
            | .outbound => 1) * exponent) by
      apply Finset.prod_congr rfl
      intro index index_mem
      rw [(Finset.mem_filter.mp index_mem).2]]
  rw [finset_prod_zpow_eq_zpow_sum]
  congr 1
  rw [← Finset.sum_mul]
  rw [dottedBoundaryCoefficient_eq_listSum]
  rw [list_map_sum_eq_fin_sum_get]
  congr 1
  unfold dottedOccurrenceCoefficient
  simp_rw [← dottedPunctureTwoHandleIndex_eq_iff]
  rw [← Finset.sum_filter]

/--
For one dotted handle, the corresponding THAM boundary-row character factor
acts trivially on every morphism with the exact incidence boundary.
-/
theorem twoOneBoundaryCharacterFactor_absorbs_incidenceMorphism
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (one : Fin diagram.handles.hOne)
    (exponent : ℤ)
    (T :
      simpleLabelWordObject 𝒞η.category
            (dottedInboundLabelWord 𝒞η.category diagram labeling
              (presentation.cut.punctureWord
                (diagram.handles.oneHandleIndex one).1
                (diagram.handles.oneHandleIndex one).2)) ⟶
        simpleLabelWordObject 𝒞η.category
            (dottedOutboundLabelWord 𝒞η.category diagram labeling
              (presentation.cut.punctureWord
                (diagram.handles.oneHandleIndex one).1
                (diagram.handles.oneHandleIndex one).2))) :
    (((∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^
          (twoOneIncidence diagram one two * exponent) : Kˣ) : K) •
        T) = T := by
  let punctures := presentation.cut.punctureWord
    (diagram.handles.oneHandleIndex one).1
    (diagram.handles.oneHandleIndex one).2
  have factor_eq :
      (∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^
          (twoOneIncidence diagram one two * exponent)) =
        componentWordCharacterUnit 𝒞η
            (dottedOutboundLabelWord
              𝒞η.category diagram labeling punctures) exponent *
          (componentWordCharacterUnit 𝒞η
            (dottedInboundLabelWord
              𝒞η.category diagram labeling punctures) exponent)⁻¹ := by
    calc
      _ = ∏ two : Fin diagram.handles.hTwo,
          𝒞η.character.value (labeling two) ^
            (dottedBoundaryCoefficient punctures
              (diagram.handles.twoHandleIndex two).1 * exponent) := by
        apply Finset.prod_congr rfl
        intro two _
        rw [twoOneIncidence_eq_dottedBoundaryCoefficient
          diagram presentation]
      _ = dottedBoundaryCharacterRatio
          𝒞η diagram labeling punctures exponent :=
        (dottedBoundaryCharacterRatio_eq_incidenceProduct
          𝒞η diagram labeling punctures exponent).symm
      _ = _ := by
        rw [dottedBoundaryCharacterRatio_eq_output_mul_input_inv]
        rfl
  rw [factor_eq]
  exact dottedIncidenceMorphism_boundaryRatio_absorbs
    𝒞η diagram labeling punctures T exponent

/--
The same boundary factor is invisible after placing an incidence morphism in
any linear exterior context.  The remaining topology obligation is only to
exhibit the actual frozen evaluator as one such context.
-/
theorem twoOneBoundaryCharacterFactor_absorbs_in_linearContext
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram)
    (one : Fin diagram.handles.hOne)
    (exponent : ℤ)
    (T :
      simpleLabelWordObject 𝒞η.category
            (dottedInboundLabelWord 𝒞η.category diagram labeling
              (presentation.cut.punctureWord
                (diagram.handles.oneHandleIndex one).1
                (diagram.handles.oneHandleIndex one).2)) ⟶
        simpleLabelWordObject 𝒞η.category
            (dottedOutboundLabelWord 𝒞η.category diagram labeling
              (presentation.cut.punctureWord
                (diagram.handles.oneHandleIndex one).1
                (diagram.handles.oneHandleIndex one).2)))
    (exterior :
      (simpleLabelWordObject 𝒞η.category
            (dottedInboundLabelWord 𝒞η.category diagram labeling
              (presentation.cut.punctureWord
                (diagram.handles.oneHandleIndex one).1
                (diagram.handles.oneHandleIndex one).2)) ⟶
        simpleLabelWordObject 𝒞η.category
            (dottedOutboundLabelWord 𝒞η.category diagram labeling
              (presentation.cut.punctureWord
                (diagram.handles.oneHandleIndex one).1
                (diagram.handles.oneHandleIndex one).2))) →ₗ[K] K) :
    (((∏ two : Fin diagram.handles.hTwo,
        𝒞η.character.value (labeling two) ^
          (twoOneIncidence diagram one two * exponent) : Kˣ) : K) *
        exterior T) =
      exterior T := by
  rw [← smul_eq_mul]
  rw [← exterior.map_smul]
  rw [twoOneBoundaryCharacterFactor_absorbs_incidenceMorphism
    𝒞η diagram presentation]

end

end TwistedYetter.Kirby.Final.Proofs
