import TwistedYetter.Kirby.Final.TwistedYetter

/-!
# Axiom audit for the intrinsic `TwistedYetter` interface

This file keeps the public trust boundary mechanically visible.  The topology
foundation and executable-backend correctness are admitted; presentation
independence and diffeomorphism invariance are theorems derived from the
Kirby-calculus development.
-/

#print axioms TwistedYetter.Kirby.Final.ClosedOrientedSmoothFourManifold
#print axioms TwistedYetter.Kirby.Final.H₂
#print axioms
  TwistedYetter.Kirby.Final.SpecialKirbyHandleTheory.Axioms.Realizes
#print axioms
  TwistedYetter.Kirby.Final.SpecialKirbyHandleTheory.Axioms.presentationExists
#print axioms
  TwistedYetter.Kirby.Final.SpecialKirbyHandleTheory.Axioms.kirbyCerfMovie
#print axioms
  TwistedYetter.Kirby.Final.SpecialKirbyHandleTheory.Axioms.kirbyCerfMovie_transports_marking

#print axioms TwistedYetter.Kirby.Final.TwistedYetter
#print axioms
  TwistedYetter.Kirby.Final.TwistedYetter_on_specialKirbyPresentation
#print axioms
  TwistedYetter.Kirby.Final.TwistedYetter_diffeomorphism_invariant
#print axioms
  TwistedYetter.Kirby.Final.TwistedYetterModular_diffeomorphism_invariant
#print axioms TwistedYetter.Kirby.Final.TwistedYetter.compute
#print axioms TwistedYetter.Kirby.Final.TwistedYetter.compute_correct
