import TwistedYetter.Kirby.PresentationExecutionTrace

/-!
# Kernel axiom audit for typed presentation execution traces

These declarations must remain free of `sorryAx` and `native_decide.ax`.
The audit does not claim that a successful raw trace already has a correct
categorical interpretation.
-/

#print axioms TwistedYetter.Kirby.PresentationExecutionTrace.ExecutionTrace.stepCount_eq_event_length
#print axioms TwistedYetter.Kirby.PresentationExecutionTrace.ExecutionTrace.states_length_eq_event_length_add_one
#print axioms TwistedYetter.Kirby.PresentationExecutionTrace.ExecutionTrace.eventIds_eq
#print axioms TwistedYetter.Kirby.PresentationExecutionTrace.ClosedExecutionCertificate.slice_count
#print axioms TwistedYetter.Kirby.PresentationExecutionTrace.ClosedExecutionCertificate.event_count
#print axioms TwistedYetter.Kirby.PresentationExecutionTrace.ClosedExecutionCertificate.event_ids
