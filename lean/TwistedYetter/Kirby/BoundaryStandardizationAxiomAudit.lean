import TwistedYetter.Kirby.BoundaryStandardization

/-!
# Axiom audit for boundary standardization

These declarations are constructors and recursors over explicit movie data.
They should use no project axiom.  Kirby's theorem belongs in a future
concrete `SurgerySemantics` instance, not in the movie recursion itself.
-/

#print axioms TwistedYetter.Kirby.BoundaryStandardization.SurgerySemantics.elementaryDiffeomorphism
#print axioms TwistedYetter.Kirby.BoundaryStandardization.SurgerySemantics.movieDiffeomorphism
#print axioms TwistedYetter.Kirby.BoundaryStandardization.BoundaryStandardizationCertificate.boundaryDiffeomorphism
#print axioms TwistedYetter.Kirby.BoundaryStandardization.CertifiedClosedPresentation.handleCounts
#print axioms TwistedYetter.Kirby.BoundaryStandardization.CertifiedClosedPresentation.h3_eq_boundary_genus
