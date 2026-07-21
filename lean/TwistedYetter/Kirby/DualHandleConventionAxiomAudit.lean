import TwistedYetter.Kirby.DualHandleConvention

/-!
# Axiom audit: dual handle convention

The transpose-chain construction and both cancellation regression checks
must use only Lean's foundational quotient/classical axioms.  No project
axiom is permitted here.
-/

#print axioms TwistedYetter.Kirby.DualHandleConvention.dualCounts_involutive
#print axioms TwistedYetter.Kirby.DualHandleConvention.DualBoundaryCertificate.dualD2_dualD3_zero
#print axioms TwistedYetter.Kirby.DualHandleConvention.primalTwoThree_dualCycle_forced_zero
#print axioms TwistedYetter.Kirby.DualHandleConvention.primalTwoThree_coefficientOne_not_dualCycle
#print axioms TwistedYetter.Kirby.DualHandleConvention.primalOneTwo_unitCycle_is_dualBoundary
#print axioms TwistedYetter.Kirby.DualHandleConvention.primalOneTwo_zero_eq_one_in_dualH2
