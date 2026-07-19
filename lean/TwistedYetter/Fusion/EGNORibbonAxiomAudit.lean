import TwistedYetter.Fusion.EGNORibbon
import TwistedYetter.Kirby.PresentationIsotopy

/-!
# Axiom audit for the EGNO category foundation

This file is compiled by `scripts/lean_egno_ribbon_axiom_audit.sh`. The script
fails if Lean reports `sorryAx`.
-/

#print axioms TwistedYetter.Fusion.EGNO.rightDoubleDualFunctor
#print axioms TwistedYetter.Fusion.EGNO.leftCategoricalTrace
#print axioms TwistedYetter.Fusion.EGNO.pivotalTrace
#print axioms TwistedYetter.Fusion.EGNO.pivotalDimension
#print axioms TwistedYetter.Kirby.FramingNaturality.NaturalTwist.ofBalanced
#print axioms TwistedYetter.Kirby.FramingNaturality.NaturalTwist.ofRibbon
#print axioms TwistedYetter.Kirby.PresentationIsotopy.FramedKinkCompatibility.twist
#print axioms TwistedYetter.Kirby.PresentationIsotopy.SphericalCutTrace.close
#print axioms TwistedYetter.Kirby.PresentationIsotopy.SphericalCutTrace.cyclic
