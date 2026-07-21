import TwistedYetter.Kirby.BoundaryDerivedHandleChainModel

/-!
# Axiom audit for the derived Mathlib handle-chain model

The builder must not introduce project axioms.  Its only topology inputs are
the already-visible lower differential, transported sphere system, and
intersection theory.
-/

#print axioms
  TwistedYetter.Kirby.BoundaryDerivedHandleChainModel.chainDifferential_squared
#print axioms
  TwistedYetter.Kirby.BoundaryDerivedHandleChainModel.derivedComplex_d2
#print axioms
  TwistedYetter.Kirby.BoundaryDerivedHandleChainModel.derivedComplex_d3
#print axioms
  TwistedYetter.Kirby.BoundaryDerivedHandleChainModel.derivedHandleChainModel
#print axioms
  TwistedYetter.Kirby.BoundaryDerivedHandleChainModel.CertifiedClosedPresentation.derivedHandleChainModel
