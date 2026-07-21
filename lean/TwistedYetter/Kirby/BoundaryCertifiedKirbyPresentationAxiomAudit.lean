import TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation

/-!
# Axiom audit for the boundary-certified legacy adapter

The adapter should add no project axiom.  In particular, its handle-chain
equality is definitional rather than a supplied equivalence.
-/

#print axioms
  TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation.BoundaryCertifiedPresentation.handleChain
#print axioms
  TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation.BoundaryCertifiedPresentation.toSpecialKirbyPresentation
#print axioms
  TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation.BoundaryCertifiedPresentation.toSpecialKirbyPresentation_handleChain
#print axioms
  TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation.BoundaryCertifiedPresentation.toSpecialKirbyPresentation_counts
#print axioms
  TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation.BoundaryCertifiedPresentation.formal_boundary_diagram_sound
