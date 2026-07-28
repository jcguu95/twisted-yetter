import TwistedYetter.Kirby.Final.SemanticEightMoves

/-!
# Axiom audit for the independent eight-move semantics

The companion shell audit also checks the import boundary and the literal
custom-axiom denominator.  These commands expose the kernel dependencies of
the machine-checked move-kind denominator.
-/

open TwistedYetter.Kirby.Final.SemanticEightMoves

#print axioms move_kind_count
#check MoveGeometry.framedIsotopy
#check MoveGeometry.oneOverOne
#check MoveGeometry.twoOverOne
#check MoveGeometry.twoOverTwo
#check MoveGeometry.oneTwoBirth
#check MoveGeometry.oneTwoDeath
#check MoveGeometry.twoThreeBirth
#check MoveGeometry.twoThreeDeath
