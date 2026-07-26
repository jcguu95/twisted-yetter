import TwistedYetter.Kirby.CancellationSafeH2Transport

/-!
# Axiom audit for arbitrary-H2 cancellation transport

The strict cycle retraction is explicit topology data supplied to the
theorems.  It is not a project axiom and cannot contain a scalar equality.
-/

#print axioms TwistedYetter.Kirby.CancellationSafeH2Transport.transportedRepresentative
#print axioms
  TwistedYetter.Kirby.CancellationSafeH2Transport.isCancellationSafe_of_automaticallySafe
#print axioms
  TwistedYetter.Kirby.CancellationSafeH2Transport.StrictCycleRetraction.liftRepresentative
#print axioms TwistedYetter.Kirby.CancellationSafeH2Transport.StrictCycleRetraction.liftedStep
#print axioms TwistedYetter.Kirby.CancellationSafeH2Transport.StrictCycleRetraction.eval_lift_eq
