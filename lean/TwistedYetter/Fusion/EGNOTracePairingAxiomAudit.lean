import TwistedYetter.Fusion.EGNOPairingCompatibility

/-!
# Axiom audit for trace-pairing compatibility

The commands below expose the kernel axioms used by the Step 7 constructions.
The two source-bound law structures are theorem parameters, not Lean axioms;
the audit therefore checks every conclusion derived after those parameters are
made explicit.
-/

#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.simpleComposition_right_separating
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.simpleComposition_left_separating
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.simpleComposition_finrank_eq
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.simpleCompositionPerfectPairing
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.unitCompositionPerfectPairing
#print axioms TwistedYetter.Fusion.EGNO.rightDualCupLinearEquiv
#print axioms TwistedYetter.Fusion.EGNO.pivotalCapLinearEquiv
#print axioms TwistedYetter.Fusion.EGNO.pivotalCup_comp_cap
#print axioms TwistedYetter.Fusion.EGNO.pivotalReverseExactPairing
#print axioms TwistedYetter.Fusion.EGNO.pivotalMateLinearEquiv
#print axioms TwistedYetter.Fusion.EGNO.pivotalDualMateLinearEquiv
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.pivotalTracePerfectPairing
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.pivotalTracePerfectPairing_pair
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.sphericalMatePairingTransport
#print axioms TwistedYetter.Fusion.PivotalMate.monoidalImagePrimal_comp_dual
#print axioms TwistedYetter.Fusion.EGNO.PivotalFunctorTraceLaw.localCompatibility
