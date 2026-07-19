import TwistedYetter.Kirby.EGNOKirbyColorExpansion

/-!
# Axiom audit for EGNO-bound Kirby-colour expansion

The commands expose the kernel axioms used by Step 8.  In particular, they
include the Schur-derived simple scalar, its nonvanishing proof, and both the
ordinary and integral-character finite expansions.
-/

#print axioms TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism.tensor_hom
#print axioms TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism.unit_hom
#print axioms TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism.identity
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.automorphismSimpleScalar
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.automorphism_app_eq_smul_identity
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.automorphismSimpleScalar_ne_zero
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.automorphismSimpleUnit
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.automorphismSimpleUnit_val
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.automorphismScalarPower
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.automorphismScalarPower_zero
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.automorphismScalarPower_add
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.identity_automorphism_simple_scalar
#print axioms TwistedYetter.Fusion.EGNO.FusionCategoryData.identity_automorphism_scalar_power
#print axioms TwistedYetter.Kirby.EGNOKirbyColorExpansion.ordinary
#print axioms TwistedYetter.Kirby.EGNOKirbyColorExpansion.integralCharacter
#print axioms TwistedYetter.Kirby.EGNOKirbyColorExpansion.integralCharacter_zero
#print axioms TwistedYetter.Kirby.EGNOKirbyColorExpansion.integralCharacter_identity
#print axioms TwistedYetter.Kirby.EGNOKirbyColorExpansion.diagramExpansion
#print axioms TwistedYetter.Kirby.EGNOKirbyColorExpansion.eval_diagramExpansion
#print axioms TwistedYetter.Kirby.EGNOKirbyColorExpansion.eval_ordinary_expansion
#print axioms TwistedYetter.Kirby.EGNOKirbyColorExpansion.eval_integralCharacter_expansion
