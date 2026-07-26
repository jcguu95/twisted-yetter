import TwistedYetter.Kirby.TwoOverTwoPositiveEndpointChannel

/-!
# Axiom audit for the positive 2/2 endpoint channel resolution

The two endpoint resolutions may depend on the narrow, category-neutral
shared-window topology input.  They must not depend on any evaluator-equality
axiom.
-/

open TwistedYetter.Kirby.TwoOverTwoPositiveEndpointChannel

#print axioms sourceLocalObject_positive
#print axioms targetLocalObject_positive
#print axioms sourceChannelResolution
#print axioms targetChannelResolution
#print axioms sourceUnequalExponentChannelResolution
#print axioms targetUnequalExponentChannelResolution
#print axioms targetMovingExponent_eq_sourceMovingExponent
#print axioms targetStationaryExponent_eq_sourceStationaryExponent
#print axioms sourceTerm_eval_eq_endpointIdentity
#print axioms targetTerm_eval_eq_endpointIdentity
#print axioms sourceGlobalPositiveEndpointResolution
#print axioms targetGlobalPositiveEndpointResolution
#print axioms sourceExactEndpointChannelResolution
#print axioms targetExactEndpointChannelResolution
