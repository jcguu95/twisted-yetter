import TwistedYetter.Kirby.IntegralH2CycleBasis

/-!
# Axiom audit for integral cycle-basis construction

The existence and class theorems should use only Mathlib foundations and
classical choice.  In particular, no graphical or representative-descent
project axiom may enter here.
-/

open TwistedYetter.Kirby.IntegralH2

#print axioms CycleBasis.liftedBasisCycle_class
#print axioms CycleBasis.ofFreeCoordinates
#print axioms CycleBasis.markedCycle_class
#print axioms CycleBasis.cycleLinearMap_homology_coordinates
#print axioms CycleBasis.cycleLinearMap_homology_coordinates_eq
#print axioms CycleBasis.rebase_markedCycle
#print axioms CycleBasis.rebaseStrictComparison
#print axioms
  CycleBasis.ofHandleSupportedNormalForm_markedCycle
