import TwistedYetter.Kirby.CertifiedH2RepresentativeTransport
import TwistedYetter.Kirby.CycleRepresentativeCounterexample
import TwistedYetter.Kirby.DualHandleConvention
import TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler
import TwistedYetter.Kirby.ThamThreeHandleVacuum

/-!
# Retraction of the primal/dual no-go misdiagnosis

Two superficially similar issues must not be merged.

1. The old raw graphical program was underspecified.  The replacement local
   compiler is total only on proof-carrying eight-case certificates.
2. The earlier proposed no-go test used the primal handle quotient even
   though the evaluator is dual/upside-down.

The numerical counterexample below is still correct for the wrong primal
adapter, but it does not refute the intended evaluator.  In the dual complex
a primal 2--3 pair has no nonzero degree-two cycle.  A primal 1--2 pair is the
case with a dual degree-three boundary, and its dotted component is exactly
where the Tham `k = 3` vacuum projector belongs.
-/

namespace TwistedYetter.Kirby.GeneralH2RawKirbyNoGo

open TwistedYetter.Kirby.CertifiedH2RepresentativeTransport
open TwistedYetter.Kirby.CycleRepresentativeCounterexample
open TwistedYetter.Kirby.DualHandleConvention
open TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler
open TwistedYetter.Kirby.ThamThreeHandleVacuum

/--
The exact descent object required only by the wrong primal-chain adapter.

It contains no topology language: `ZMod 1` is already the second homology of
the toy cancelling pair, and `agrees` requires the descended function to
recover every integer representative used by the raw formula.
-/
structure RawCancelingPairDescent where
  value : ZMod 1 → ℚ
  agrees :
    (exponent : ℤ) →
      value (exponent : ZMod 1) =
        twoSimpleTwistedUnknot exponent

/-- The wrong primal-chain descent is uninhabited. -/
theorem rawCancelingPairDescent_isEmpty :
    IsEmpty RawCancelingPairDescent := by
  constructor
  intro descent
  exact no_naive_representative_descent
    ⟨descent.value, descent.agrees⟩

/-- There is no function on the wrong primal quotient agreeing with the toy formula. -/
theorem no_rawCancelingPairDescent :
    ¬ Nonempty RawCancelingPairDescent := by
  exact not_nonempty_iff.mpr rawCancelingPairDescent_isEmpty

/--
The local blocker is terminally resolved by changing the admitted input to a
kernel-checked certificate.  This status does not claim raw auto-compilation.
-/
def localCompilerResolutionStatus : String :=
  "TERMINAL_REJECTED_UNDERSPECIFIED_RAW_COMPILER_"
    ++ "REPLACED_BY_PROOF_CARRYING_CHECKER"

/--
The old global no-go interpretation is retracted: it used the wrong chain.
-/
def rawGlobalLiftResolutionStatus : String :=
  "RETRACTED_WRONG_PRIMAL_DUAL_IDENTIFICATION_NOT_AN_INVARIANT_NOGO"

/-- The replacement route selected by the source audit. -/
def correctedRoute : String :=
  "Colour only cycles in the dual handle complex. Original 2-3 pairs are "
    ++ "controlled by the dual cycle kernel; original dotted 1-handles are "
    ++ "Tham k=3 vacuum projectors and control dual d3 boundaries."

/-- The two blocker statements that were inherited from the old status artifact. -/
inductive PriorBlocker where
  | underspecifiedLocalGraphicalProgram
  | arbitraryH2RawGlobalDescent
  deriving Repr, BEq, DecidableEq

/-- A terminal disposition is different from a successful invariant theorem. -/
inductive TerminalDisposition where
  | rejectedUnderspecifiedInput
  | retractedWrongConvention
  | unresolved
  deriving Repr, BEq, DecidableEq

/-- Exact disposition of each old blocker after the audit. -/
def resolution : PriorBlocker → TerminalDisposition
  | .underspecifiedLocalGraphicalProgram => .rejectedUnderspecifiedInput
  | .arbitraryH2RawGlobalDescent => .retractedWrongConvention

/-- No item in the old two-blocker list remains merely pending as stated. -/
theorem priorBlocker_resolution_terminal (blocker : PriorBlocker) :
    resolution blocker ≠ .unresolved := by
  cases blocker <;> decide

/--
The corrected dual route is not declared complete merely by retracting the
wrong no-go.  The dotted-vacuum realization must still be connected to the
serialized evaluator for all dual boundaries.
-/
def arbitraryH2RawKirbyInvariantEstablished : Bool := false

/-- The counterexample exponent `1` is rejected by the correct dual cycle gate. -/
theorem counterexample_coefficientOne_not_admitted_in_correct_dual_chain :
    singletonIdentity (fun _ => 1) ≠ 0 :=
  primalTwoThree_coefficientOne_not_dualCycle

/-- Machine-visible corrected diagnosis. -/
def currentStatus : String :=
  "PASS_RETRACTED_FALSE_NOGO_DUAL_HANDLE_ROUTE_RESTORED"

end TwistedYetter.Kirby.GeneralH2RawKirbyNoGo
