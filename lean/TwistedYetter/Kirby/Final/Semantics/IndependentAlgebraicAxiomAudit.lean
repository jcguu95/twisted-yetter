import TwistedYetter.Kirby.Final.Semantics.IndependentAlgebraicBridge

/-!
# Kernel audit of the independent algebraic specification bridge

The independent structures themselves contain data and laws but introduce no
axioms. These commands expose the kernel dependencies of the one-way
conformance constructions.
-/

open TwistedYetter.Kirby.Final.IndependentAlgebraicBridge

#print axioms categoryConforms
#print axioms characterConforms
#print axioms twistedCategoryConforms
