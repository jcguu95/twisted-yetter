import TwistedYetter.Kirby.Final.Semantics.Independent.CutOpen

/-!
# Independent semantics: visible THAM-side marking coordinates

The public Kirby terminology is the ordinary one: dotted components are
primal one-handles, ordinary framed components are primal two-handles, and
`hThree` is only the number of unrecorded closing primal three-handles.

Tham, Definition 5.11 is applied to the handle decomposition turned upside
down.  The evaluator therefore attaches integral exponents to primal
two-handles.  It does not need the attaching spheres of the closing
three-handles, nor an arbitrary matrix pretending to encode them.

For a visible special Kirby diagram `D`, the only canonical identification
between coefficient vectors is addition of a transposed visible
one--two-handle boundary.  We therefore form the ambient quotient

  `C₂(D) / im(∂₂(D)ᵀ)`.

This quotient is deliberately not named `H²`: for a genuine closed handle
realization, actual second cohomology is the subgroup represented by cocycles.
The external topology relation in `EntranceAxioms` says which ambient marking
represents `PD(alpha)`.  This separation prevents an arbitrary, unrecorded
degree-three boundary from becoming part of the raw diagram semantics.

Reference: Ying Hong Tham, *On the Category of Boundary Values in the extended
Crane-Yetter TQFT* (2021), Definition 5.11 (PDF p. 58) and the dual-handle
application on PDF pp. 99--101.
-/

namespace TwistedYetter.Semantics.Independent

open scoped BigOperators

noncomputable section

abbrev dottedBoundaryCoefficient :=
  @dottedCutBoundaryCoefficient

/-!
There is deliberately no separate map `PunctureDirection → ℤ`.  The only
integer extracted from dotted-cut variance is the aggregate boundary
coefficient: output occurrences minus input occurrences.  In particular it
cannot be reused as a ribbon duality choice or as the evaluator's character
exponent.
-/

def twoOneIncidence
    (diagram : SpecialKirbyDiagram)
    (one : Fin diagram.handles.hOne)
    (two : Fin diagram.handles.hTwo) : ℤ :=
  diagram.handles.boundaryTwo
    (fun coordinate => if coordinate = two then 1 else 0) one

/-- The public incidence entry is exactly the aggregate boundary coefficient. -/
theorem twoOneIncidence_eq_dottedBoundaryCoefficient
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (one : Fin diagram.handles.hOne)
    (two : Fin diagram.handles.hTwo) :
    twoOneIncidence diagram one two =
      dottedBoundaryCoefficient
        (presentation.cut.punctureWord
          (diagram.handles.oneHandleIndex one).1
          (diagram.handles.oneHandleIndex one).2)
        (diagram.handles.twoHandleIndex two).1 :=
  presentation.incidence_agrees_with_handle_boundary one two

/-- The visible primal cellular boundary `C₂ → C₁`. -/
def primalBoundaryTwo
    (diagram : SpecialKirbyDiagram) :
    HandleChainGroup diagram.handles.hTwo →+
      HandleChainGroup diagram.handles.hOne :=
  diagram.handles.boundaryTwo

/-- Integral coordinate pairing in a fixed finite handle basis. -/
def coordinatePairing {count : ℕ}
    (left right : HandleChainGroup count) : ℤ :=
  ∑ index, left index * right index

/-- Integral unit vector in a fixed finite handle basis. -/
def coordinateUnit (count : ℕ) (index coordinate : Fin count) : ℤ :=
  if coordinate = index then 1 else 0

theorem coordinatePairing_unit_left
    (count : ℕ)
    (index : Fin count)
    (vector : HandleChainGroup count) :
    coordinatePairing (coordinateUnit count index) vector = vector index := by
  classical
  simp [coordinatePairing, coordinateUnit, eq_comm]

theorem coordinatePairing_unit_right
    (count : ℕ)
    (vector : HandleChainGroup count)
    (index : Fin count) :
    coordinatePairing vector (coordinateUnit count index) = vector index := by
  classical
  simp [coordinatePairing, coordinateUnit]

/--
The transpose of an integral map between finite coordinate groups.  This is
ordinary finite-basis algebra and does not encode a three-handle attachment.
-/
def transposeAddHom {sourceCount targetCount : ℕ}
    (map : HandleChainGroup sourceCount →+
      HandleChainGroup targetCount) :
    HandleChainGroup targetCount →+
      HandleChainGroup sourceCount where
  toFun target sourceIndex :=
    coordinatePairing
      (map (coordinateUnit sourceCount sourceIndex))
      target
  map_zero' := by
    funext sourceIndex
    simp [coordinatePairing]
  map_add' left right := by
    funext sourceIndex
    simp [coordinatePairing, mul_add, Finset.sum_add_distrib]

/-- Finite-basis adjointness for the computed transpose. -/
theorem transposeAddHom_adjoint
    {sourceCount targetCount : ℕ}
    (map : HandleChainGroup sourceCount →+
      HandleChainGroup targetCount)
    (source : HandleChainGroup sourceCount)
    (target : HandleChainGroup targetCount) :
    coordinatePairing (map source) target =
      coordinatePairing source (transposeAddHom map target) := by
  classical
  have source_decomposition :
      source =
        ∑ index, source index • coordinateUnit sourceCount index := by
    funext coordinate
    simp [coordinateUnit]
  have map_source_decomposition :
      map source =
        ∑ index,
          source index • map (coordinateUnit sourceCount index) := by
    calc
      map source =
          map (∑ index,
            source index • coordinateUnit sourceCount index) :=
        congrArg map source_decomposition
      _ = ∑ index,
          source index • map (coordinateUnit sourceCount index) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro index _
        exact map.map_zsmul
          (coordinateUnit sourceCount index) (source index)
  rw [map_source_decomposition]
  simp only [coordinatePairing, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, transposeAddHom]
  change
    (∑ targetIndex,
      (∑ sourceIndex,
        source sourceIndex *
          map (coordinateUnit sourceCount sourceIndex) targetIndex) *
        target targetIndex) =
      ∑ sourceIndex,
        source sourceIndex *
          (∑ targetIndex,
            map (coordinateUnit sourceCount sourceIndex) targetIndex *
              target targetIndex)
  calc
    _ = ∑ targetIndex, ∑ sourceIndex,
          (source sourceIndex *
            map (coordinateUnit sourceCount sourceIndex) targetIndex) *
              target targetIndex := by
        apply Finset.sum_congr rfl
        intro targetIndex _
        rw [Finset.sum_mul]
    _ = ∑ sourceIndex, ∑ targetIndex,
          (source sourceIndex *
            map (coordinateUnit sourceCount sourceIndex) targetIndex) *
              target targetIndex :=
        Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro targetIndex _
      ring

/-- The THAM-side visible coboundary `C¹ → C²`, namely `∂₂ᵀ`. -/
def thamVisibleCoboundary
    (diagram : SpecialKirbyDiagram) :
    HandleChainGroup diagram.handles.hOne →+
      HandleChainGroup diagram.handles.hTwo :=
  transposeAddHom (primalBoundaryTwo diagram)

/-- Integral coefficients attached by the evaluator to primal two-handles. -/
abbrev ThamTwoHandleCoefficients
    (diagram : SpecialKirbyDiagram) :=
  HandleChainGroup diagram.handles.hTwo

/--
The ambient marking quotient visible without three-handle attaching data.
Actual Poincare-dual classes are selected inside this quotient by an explicit
external topology relation.
-/
abbrev ThamMarkingClass
    (diagram : SpecialKirbyDiagram) :=
  ThamTwoHandleCoefficients diagram ⧸
    (thamVisibleCoboundary diagram).range

def thamMarkingClass
    {diagram : SpecialKirbyDiagram}
    (coefficients : ThamTwoHandleCoefficients diagram) :
    ThamMarkingClass diagram :=
  QuotientAddGroup.mk coefficients

/-- A cut-open diagram together with the ambient THAM marking it evaluates. -/
structure HomologicallyMarkedDiagram where
  diagram : SpecialKirbyDiagram
  cut : DottedCutPresentation diagram
  thamAlpha : ThamMarkingClass diagram

end

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 1530
