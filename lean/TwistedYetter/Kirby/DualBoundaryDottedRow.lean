import TwistedYetter.Kirby.DualBoundaryGeneratorReduction

/-!
# A dual degree-three generator is one primal dotted-handle row

The evaluator uses the transpose of the primal middle handle complex.  This
module extracts the coordinate statement needed by the dotted-disk graphical
compiler: adding an integral multiple of one dual degree-three basis vector
changes the coefficient of primal two-handle `j` by that multiple times the
`(j,i)` entry of the primal `d2` matrix.

This is proved from the adjointness field of `DualBoundaryCertificate`; no
linking number, diagram evaluation, or invariant equality is assumed.
-/

namespace TwistedYetter.Kirby.DualBoundaryDottedRow

open TwistedYetter.Kirby.BoundaryDerivedHandleChain
open TwistedYetter.Kirby.DualBoundaryGeneratorReduction
open TwistedYetter.Kirby.DualHandleConvention

/-- Pairing on the right with an integral coordinate reads that coordinate. -/
theorem coordinatePairing_integralCoordinate_right
    {count : Nat}
    (vector : FreeHandleGroup count)
    (index : Fin count)
    (coefficient : ℤ) :
    coordinatePairing vector
        (coordinateTerm (fun _ => coefficient) index) =
      vector index * coefficient := by
  classical
  simp [coordinatePairing, coordinateTerm]

/--
The transpose certificate identifies one dual `d3` coordinate with one
primal `d2` row entry.
-/
theorem dualD3_integralGenerator_coordinate
    {h1 h2 h3 : Nat}
    {primal : ClosedHandleBoundaryData h1 h2 h3}
    (certificate : DualBoundaryCertificate primal)
    (oneHandle : Fin h1)
    (coefficient : ℤ)
    (twoHandle : Fin h2) :
    certificate.dualD3
        (coordinateTerm (fun _ => coefficient) oneHandle) twoHandle =
      primal.d2 (coordinateUnit h2 twoHandle) oneHandle * coefficient := by
  calc
    certificate.dualD3
        (coordinateTerm (fun _ => coefficient) oneHandle) twoHandle =
        coordinatePairing (coordinateUnit h2 twoHandle)
          (certificate.dualD3
            (coordinateTerm (fun _ => coefficient) oneHandle)) :=
      (coordinatePairing_unit_left h2 twoHandle _).symm
    _ = coordinatePairing
          (primal.d2 (coordinateUnit h2 twoHandle))
          (coordinateTerm (fun _ => coefficient) oneHandle) :=
      (certificate.dualD3_adjoint
        (coordinateUnit h2 twoHandle)
        (coordinateTerm (fun _ => coefficient) oneHandle)).symm
    _ = primal.d2 (coordinateUnit h2 twoHandle) oneHandle * coefficient :=
      coordinatePairing_integralCoordinate_right _ _ _

/--
After adding one dual generator boundary, every two-handle coordinate changes
by the corresponding primal dotted-handle row entry.
-/
theorem addDualBoundary_integralGenerator_coordinate
    {h1 h2 h3 : Nat}
    {primal : ClosedHandleBoundaryData h1 h2 h3}
    (certificate : DualBoundaryCertificate primal)
    (cycle : certificate.dualBoundaryData.Cycles)
    (oneHandle : Fin h1)
    (coefficient : ℤ)
    (twoHandle : Fin h2) :
    ((addBoundary certificate.dualBoundaryData cycle
        (coordinateTerm (fun _ => coefficient) oneHandle) :
          certificate.dualBoundaryData.Cycles) :
        FreeHandleGroup h2) twoHandle =
      (cycle : FreeHandleGroup h2) twoHandle +
        primal.d2 (coordinateUnit h2 twoHandle) oneHandle * coefficient := by
  change
    (cycle : FreeHandleGroup h2) twoHandle +
        certificate.dualD3
          (coordinateTerm (fun _ => coefficient) oneHandle) twoHandle =
      _
  rw [dualD3_integralGenerator_coordinate]

/-- Machine-visible status of the transpose-to-dotted-row calculation. -/
def currentStatus : String :=
  "PASS_DUAL_D3_GENERATOR_EQUALS_PRIMAL_D2_DOTTED_ROW"

end TwistedYetter.Kirby.DualBoundaryDottedRow
