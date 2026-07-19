import TwistedYetter.Fusion.PivotalMate
import TwistedYetter.Fusion.Insertion
import TwistedYetter.Fusion.EGNORibbon
import TwistedYetter.Fusion.EGNOCanonicalPivotal

/-!
# Kernel axiom audit for the finite-resolution bootstrap

This file is compiled by `scripts/lean_fusion_axiom_audit.sh`. The script fails
if Lean reports `sorryAx`.
-/

#print axioms TwistedYetter.Fusion.FiniteResolution.DualBasisData.pair_primal_dual
#print axioms TwistedYetter.Fusion.FiniteResolution.DualBasisData.coefficient_eq_repr
#print axioms TwistedYetter.Fusion.FiniteResolution.DualBasisData.reconstruct
#print axioms TwistedYetter.Fusion.FiniteResolution.DualBasisData.inverse_reconstruct
#print axioms TwistedYetter.Fusion.FiniteResolution.LinearResolution.reindex
#print axioms TwistedYetter.Fusion.FiniteResolution.LinearResolution.map
#print axioms TwistedYetter.Fusion.FiniteResolution.WeightedFamily.total_reindex
#print axioms TwistedYetter.Fusion.PairingTransport.pair_primal_dual
#print axioms TwistedYetter.Fusion.PairingTransport.dualVector_eq_canonical
#print axioms TwistedYetter.Fusion.PairingTransport.coefficient_eq
#print axioms TwistedYetter.Fusion.PairingTransport.channel_eq
#print axioms TwistedYetter.Fusion.PairingTransport.reconstruct
#print axioms TwistedYetter.Fusion.PairingTransport.mapped_resolution_term_eq
#print axioms TwistedYetter.Fusion.FrobeniusLinear.mateLinearEquiv_apply
#print axioms TwistedYetter.Fusion.FrobeniusLinear.mateLinearEquiv_symm_apply
#print axioms TwistedYetter.Fusion.FrobeniusLinear.dualMateLinearEquiv_apply
#print axioms TwistedYetter.Fusion.BiorthogonalFamily.ofDualBasisData
#print axioms TwistedYetter.Fusion.PairingMap.mapFamily_pair_eq
#print axioms TwistedYetter.Fusion.Insertion.IdentityResolution.inverse_sound
#print axioms TwistedYetter.Fusion.Insertion.IdentityResolution.map_sound
#print axioms TwistedYetter.Fusion.Insertion.IdentityResolution.map_inverse_sound
#print axioms TwistedYetter.Fusion.EGNO.rightDoubleDualFunctor
#print axioms TwistedYetter.Fusion.EGNO.leftCategoricalTrace
#print axioms TwistedYetter.Fusion.EGNO.pivotalTrace
#print axioms TwistedYetter.Fusion.EGNO.pivotalDimension
#print axioms TwistedYetter.Fusion.EGNO.drinfeldHom
#print axioms TwistedYetter.Fusion.EGNO.drinfeldIso
#print axioms TwistedYetter.Fusion.EGNO.drinfeldHom_naturality
#print axioms TwistedYetter.Fusion.EGNO.drinfeldNatIso
#print axioms TwistedYetter.Fusion.EGNO.canonicalPivotalHom
#print axioms TwistedYetter.Fusion.EGNO.canonicalPivotalHom_eq
#print axioms TwistedYetter.Fusion.EGNO.canonicalPivotalIso
#print axioms TwistedYetter.Fusion.PivotalMate.equation_3_1_11
#print axioms TwistedYetter.Fusion.PivotalMate.transformedDualFamily_pair
