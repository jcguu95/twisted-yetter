import TwistedYetter.StableNoGo.Main
import TwistedYetter.StableNoGo.CategoryEvidence

/-!
# Trust audit for the initial stable no-go modules

These commands make the kernel dependency closure visible during compilation.
-/

#print axioms TwistedYetter.StableNoGo.twistedYetter_eq_of_stable_realization
#print axioms TwistedYetter.StableNoGo.PremodularMarkedIntersectionFormInvariance
#print axioms
  TwistedYetter.StableNoGo.premodularMarkedIntersectionFormInvariance_of_stable_inputs
#print axioms
  TwistedYetter.StableNoGo.markedStabilizationFormula_of_connectedSum
#print axioms
  TwistedYetter.StableNoGo.premodularMarkedIntersectionFormInvariance_of_core_obligations

-- Explicit new trust-boundary declarations.  These checks intentionally sit
-- beside the final theorem closure instead of being hidden in prose.
#check TwistedYetter.StableNoGo.wall_stableClassification
#check TwistedYetter.StableNoGo.rubermanStrle_oneStableRealization
#check TwistedYetter.StableNoGo.connectedSumOrientedDiffeomorphism
#check TwistedYetter.StableNoGo.premodularKirbyColourKilling
#check TwistedYetter.StableNoGo.standardPositiveHopfClosure_eq_monodromyTrace
