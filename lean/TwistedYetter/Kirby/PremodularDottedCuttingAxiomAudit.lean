import TwistedYetter.Kirby.PremodularDottedCutting
import TwistedYetter.Kirby.ThamThreeHandleVacuum

/-!
# Axiom audit for premodular special-dotted cutting

This audit covers only the category-side operator and character neutrality.
It deliberately does not claim that the existing ordinary Kirby-colour
`CanonicalPresentation.cycleLinearDiagram` has special-dotted semantics.
-/

#print axioms
  TwistedYetter.Kirby.PremodularDottedCutting.specialDottedCutOperator
#print axioms
  TwistedYetter.Kirby.PremodularDottedCutting.automorphism_power_specialDottedCut_left
#print axioms
  TwistedYetter.Kirby.PremodularDottedCutting.automorphism_power_specialDottedCut_right
#print axioms
  TwistedYetter.Kirby.ThamThreeHandleVacuum.vacuumProjectedRegularWeight_eq_one
#print axioms
  TwistedYetter.Kirby.ThamThreeHandleVacuum.primalOneTwoBoundaryCoefficient_is_vacuum_neutral

#eval TwistedYetter.Kirby.PremodularDottedCutting.currentStatus
