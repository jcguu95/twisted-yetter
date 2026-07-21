import TwistedYetter.Fusion.EGNOPremodularModular

/-!
# Axiom audit for the EGNO premodular/modular hierarchy

The three project axioms below are deliberately textbook-scoped:

* EGNO Proposition 8.10.12, spherical-to-ribbon reconstruction;
* EGNO Remark 8.19.3 and Theorem 8.20.7, nondegeneracy versus trivial
  Mueger center;
* EGNO Proposition 8.14.2 and Remark 8.14.3, nonzero global dimension.

The definitions of the S-matrix, premodular category, modular category, and
the final local-to-global descent contain no additional project axiom.
-/

#print axioms TwistedYetter.Fusion.EGNO.PremodularCategory.toBraidedSpherical
#print axioms TwistedYetter.Fusion.EGNO.sphericalRibbonReconstruction
#print axioms TwistedYetter.Fusion.EGNO.BraidedSphericalFusionCategory.toPremodular
#print axioms TwistedYetter.Fusion.EGNO.ModularCategory.transparent_iff_unit
#print axioms TwistedYetter.Fusion.EGNO.ModularCategory.globalDimension_ne_zero
