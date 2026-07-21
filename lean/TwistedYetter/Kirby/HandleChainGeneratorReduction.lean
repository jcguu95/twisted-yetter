import TwistedYetter.Kirby.DualBoundaryGeneratorReduction
import TwistedYetter.Kirby.HandleHomologyBoundaryReduction

/-!
# Generator reduction for the actual Mathlib handle-chain model

This module transfers the finite-coordinate argument to the exact
`HandleChainModel` consumed by the canonical evaluator.  The incoming object
of `complex.sc 2` is canonically identified with degree three, then with the
stored finite handle basis.  As a result, checking one local rule for every
degree-three basis element and every integer coefficient proves
representative independence for all of `H₂`.

For the upside-down evaluator, this finite basis is the basis dual to the
primal one-handles.  Thus the remaining graphical checks are indexed by the
primal dotted handles, not by arbitrary pairs of cycles.
-/

namespace TwistedYetter.Kirby.HandleChainGeneratorReduction

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Kirby.DualBoundaryGeneratorReduction
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.HandleHomologyBoundaryReduction
open TwistedYetter.Kirby.KirbyCancellation

/-- The incoming short-complex object at degree two is the degree-three object. -/
noncomputable def degreeThreeScIso
    {counts : HandleCounts}
    (model : HandleChainModel counts) :
    (model.complex.sc 2).X₁ ≅ model.complex.X 3 :=
  (CategoryTheory.ShortComplex.π₁ (C := ModuleCat ℤ)).mapIso
    (model.complex.isoSc' 3 2 1 (by simp) (by simp))

/-- One integral multiple of one stored degree-three handle basis vector. -/
noncomputable def coordinateChain
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    (index : Fin counts.h3)
    (coefficient : ℤ) : (model.complex.sc 2).X₁ :=
  (degreeThreeScIso model).toLinearEquiv.symm
    (model.degreeThreeBasis.toLinearEquiv.symm
      (coordinateTerm (fun _ => coefficient) index))

/-- Add the boundary of a concrete degree-three chain to a degree-two cycle. -/
noncomputable def addBoundary
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    (cycle : model.complex.cycles 2)
    (chain : (model.complex.sc 2).X₁) : model.complex.cycles 2 :=
  let short := model.complex.sc 2
  short.moduleCatCyclesIso.toLinearEquiv.symm
    (short.moduleCatCyclesIso.toLinearEquiv cycle +
      short.moduleCatLeftHomologyData.f' chain)

@[simp] theorem addBoundary_zero
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    (cycle : model.complex.cycles 2) :
    addBoundary model cycle 0 = cycle := by
  simp only [addBoundary]
  rw [map_zero, add_zero, LinearEquiv.symm_apply_apply]

/-- Adding a sum of chains is successive boundary addition. -/
theorem addBoundary_add
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    (cycle : model.complex.cycles 2)
    (first second : (model.complex.sc 2).X₁) :
    addBoundary model cycle (first + second) =
      addBoundary model (addBoundary model cycle first) second := by
  unfold addBoundary
  apply_fun (model.complex.sc 2).moduleCatCyclesIso.toLinearEquiv
    using (model.complex.sc 2).moduleCatCyclesIso.toLinearEquiv.injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [map_add]
  exact (add_assoc _ _ _).symm

/-- Boundary addition is translation by the boundary added to the zero cycle. -/
theorem addBoundary_eq_add_zeroBoundary
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    (cycle : model.complex.cycles 2)
    (chain : (model.complex.sc 2).X₁) :
    addBoundary model cycle chain =
      cycle + addBoundary model 0 chain := by
  let e :
      model.complex.cycles 2 ≃ₗ[ℤ]
        (model.complex.sc 2).moduleCatLeftHomologyData.K :=
    (model.complex.sc 2).moduleCatCyclesIso.toLinearEquiv
  let boundary :=
    (model.complex.sc 2).moduleCatLeftHomologyData.f' chain
  change e.symm (e cycle + boundary) =
    cycle + e.symm (e 0 + boundary)
  calc
    e.symm (e cycle + boundary) =
        e.symm (e cycle) + e.symm boundary :=
      e.symm.map_add (e cycle) boundary
    _ = cycle + e.symm boundary := by rw [e.symm_apply_apply]
    _ = cycle + e.symm (e 0 + boundary) := by
      rw [e.map_zero, zero_add]

/-- The concrete degree-two chain inclusion preserves boundary translation. -/
theorem iCycles_addBoundary
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    (cycle : model.complex.cycles 2)
    (chain : (model.complex.sc 2).X₁) :
    model.complex.iCycles 2 (addBoundary model cycle chain) =
      model.complex.iCycles 2 cycle +
        model.complex.iCycles 2 (addBoundary model 0 chain) := by
  rw [addBoundary_eq_add_zeroBoundary]
  exact map_add (model.complex.iCycles 2).hom cycle
    (addBoundary model 0 chain)

/-- An integral coordinate chain is the corresponding multiple of its unit vector. -/
theorem coordinateChain_eq_zsmul_unit
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    (index : Fin counts.h3)
    (coefficient : ℤ) :
    coordinateChain model index coefficient =
      coefficient • coordinateChain model index 1 := by
  classical
  have coordinate_eq :
      coordinateTerm (fun _ => coefficient) index =
        coefficient • coordinateTerm (fun _ => (1 : ℤ)) index := by
    funext coordinate
    simp [coordinateTerm]
  unfold coordinateChain
  rw [coordinate_eq]
  calc
    (degreeThreeScIso model).toLinearEquiv.symm
        (model.degreeThreeBasis.toLinearEquiv.symm
          (coefficient • coordinateTerm (fun _ => (1 : ℤ)) index)) =
      (degreeThreeScIso model).toLinearEquiv.symm
        (coefficient •
          model.degreeThreeBasis.toLinearEquiv.symm
            (coordinateTerm (fun _ => (1 : ℤ)) index)) := by
        congr 1
        exact map_zsmul model.degreeThreeBasis.toLinearEquiv.symm
          coefficient (coordinateTerm (fun _ => (1 : ℤ)) index)
    _ = coefficient •
        (degreeThreeScIso model).toLinearEquiv.symm
          (model.degreeThreeBasis.toLinearEquiv.symm
            (coordinateTerm (fun _ => (1 : ℤ)) index)) :=
      map_zsmul (degreeThreeScIso model).toLinearEquiv.symm
        coefficient _

/-- The boundary of a coordinate chain scales with its integral coefficient. -/
theorem addBoundary_zero_coordinateChain
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    (index : Fin counts.h3)
    (coefficient : ℤ) :
    addBoundary model 0 (coordinateChain model index coefficient) =
      coefficient •
        addBoundary model 0 (coordinateChain model index 1) := by
  rw [coordinateChain_eq_zsmul_unit]
  let e :
      model.complex.cycles 2 ≃ₗ[ℤ]
        (model.complex.sc 2).moduleCatLeftHomologyData.K :=
    (model.complex.sc 2).moduleCatCyclesIso.toLinearEquiv
  let boundaryMap :=
    (model.complex.sc 2).moduleCatLeftHomologyData.f'.hom
  change e.symm (e 0 + boundaryMap
      (coefficient • coordinateChain model index 1)) =
    coefficient •
      e.symm (e 0 + boundaryMap (coordinateChain model index 1))
  rw [e.map_zero, zero_add]
  calc
    e.symm (boundaryMap
        (coefficient • coordinateChain model index 1)) =
      e.symm (coefficient •
        boundaryMap (coordinateChain model index 1)) := by
        congr 1
        exact map_zsmul boundaryMap coefficient
          (coordinateChain model index 1)
    _ = coefficient •
        e.symm (boundaryMap (coordinateChain model index 1)) :=
      map_zsmul e.symm coefficient _
    _ = coefficient •
        e.symm (0 + boundaryMap (coordinateChain model index 1)) := by
      rw [zero_add]

/--
Adding one integral degree-three basis boundary changes the concrete
degree-two chain by that multiple of the unit-generator boundary.
-/
theorem iCycles_addBoundary_coordinateChain
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    (cycle : model.complex.cycles 2)
    (index : Fin counts.h3)
    (coefficient : ℤ) :
    model.complex.iCycles 2
        (addBoundary model cycle
          (coordinateChain model index coefficient)) =
      model.complex.iCycles 2 cycle +
        coefficient •
          model.complex.iCycles 2
            (addBoundary model 0
              (coordinateChain model index 1)) := by
  rw [iCycles_addBoundary]
  rw [addBoundary_zero_coordinateChain]
  congr 1
  exact map_zsmul (model.complex.iCycles 2).hom coefficient
    (addBoundary model 0 (coordinateChain model index 1))

/-- Every incoming chain is the sum of its stored handle coordinates. -/
theorem sum_coordinateChain
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    (chain : (model.complex.sc 2).X₁) :
    (∑ index,
      coordinateChain model index
        (model.degreeThreeBasis.toLinearEquiv
          ((degreeThreeScIso model).toLinearEquiv chain) index)) =
      chain := by
  apply_fun (degreeThreeScIso model).toLinearEquiv
    using (degreeThreeScIso model).toLinearEquiv.injective
  apply_fun model.degreeThreeBasis.toLinearEquiv
    using model.degreeThreeBasis.toLinearEquiv.injective
  simp only [map_sum, coordinateChain, LinearEquiv.apply_symm_apply]
  exact sum_coordinateTerm _

/--
Local denominator for representative descent: every integral multiple of
every stored degree-three handle generator, in front of any existing cycle.
-/
def IntegralGeneratorBoundaryInvariant
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    {V : Type*}
    (evaluation : model.complex.cycles 2 → V) : Prop :=
  ∀ (cycle : model.complex.cycles 2) (index : Fin counts.h3)
    (coefficient : ℤ),
    evaluation
        (addBoundary model cycle
          (coordinateChain model index coefficient)) =
      evaluation cycle

/-- Invariance under a finite subset of the degree-three basis. -/
theorem sum_over_subset_invariant
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    {V : Type*}
    (evaluation : model.complex.cycles 2 → V)
    (generatorLaw : IntegralGeneratorBoundaryInvariant model evaluation)
    (chain : (model.complex.sc 2).X₁)
    (cycle : model.complex.cycles 2)
    (subset : Finset (Fin counts.h3)) :
    evaluation
        (addBoundary model cycle
          (∑ index ∈ subset,
            coordinateChain model index
              (model.degreeThreeBasis.toLinearEquiv
                ((degreeThreeScIso model).toLinearEquiv chain) index))) =
      evaluation cycle := by
  classical
  induction subset using Finset.induction_on generalizing cycle with
  | empty => simp
  | @insert index subset indexNotMem ih =>
      rw [Finset.sum_insert indexNotMem]
      rw [addBoundary_add]
      rw [ih]
      exact generatorLaw cycle index
        (model.degreeThreeBasis.toLinearEquiv
          ((degreeThreeScIso model).toLinearEquiv chain) index)

/-- Integral generator checks imply invariance under every incoming boundary. -/
theorem integral_generators_imply_all_boundaries
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    {V : Type*}
    (evaluation : model.complex.cycles 2 → V)
    (generatorLaw : IntegralGeneratorBoundaryInvariant model evaluation)
    (cycle : model.complex.cycles 2)
    (chain : (model.complex.sc 2).X₁) :
    evaluation (addBoundary model cycle chain) = evaluation cycle := by
  rw [← sum_coordinateChain model chain]
  simpa using
    sum_over_subset_invariant model evaluation generatorLaw chain cycle Finset.univ

/-- Mathlib's displayed boundary equation agrees with `addBoundary`. -/
theorem addBoundary_eq_of_boundaryEquation
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    (left right : model.complex.cycles 2)
    (chain : (model.complex.sc 2).X₁)
    (equation :
      (model.complex.sc 2).moduleCatToCycles chain =
        (model.complex.sc 2).moduleCatCyclesIso.hom left -
          (model.complex.sc 2).moduleCatCyclesIso.hom right) :
    addBoundary model right chain = left := by
  have equation' :
      (model.complex.sc 2).moduleCatLeftHomologyData.f' chain =
        (model.complex.sc 2).moduleCatCyclesIso.hom left -
          (model.complex.sc 2).moduleCatCyclesIso.hom right :=
    equation
  unfold addBoundary
  apply_fun (model.complex.sc 2).moduleCatCyclesIso.toLinearEquiv
    using (model.complex.sc 2).moduleCatCyclesIso.toLinearEquiv.injective
  simp only [LinearEquiv.apply_symm_apply]
  change
    (model.complex.sc 2).moduleCatCyclesIso.hom right +
        (model.complex.sc 2).moduleCatLeftHomologyData.f' chain =
      (model.complex.sc 2).moduleCatCyclesIso.hom left
  rw [equation']
  abel

/-- The finite local checks imply equality on every Mathlib `H₂` class. -/
theorem respects_homology_class
    {counts : HandleCounts}
    (model : HandleChainModel counts)
    {V : Type*}
    (evaluation : model.complex.cycles 2 → V)
    (generatorLaw : IntegralGeneratorBoundaryInvariant model evaluation)
    (left right : model.complex.cycles 2)
    (sameClass :
      model.complex.homologyπ 2 left = model.complex.homologyπ 2 right) :
    evaluation left = evaluation right := by
  obtain ⟨chain, equation⟩ :=
    (homologyπ_eq_iff_exists_boundary model.complex left right).mp sameClass
  rw [← addBoundary_eq_of_boundaryEquation model left right chain equation]
  exact integral_generators_imply_all_boundaries
    model evaluation generatorLaw right chain

/-- Machine-visible result: the global quotient step is now finite-local. -/
def currentStatus : String :=
  "PASS_HANDLE_CHAIN_INTEGRAL_GENERATORS_IMPLY_H2_DESCENT"

end TwistedYetter.Kirby.HandleChainGeneratorReduction
