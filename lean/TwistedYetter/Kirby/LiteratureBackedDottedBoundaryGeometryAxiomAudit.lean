import TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry

/-!
# Audit for the standard dotted-disk topology boundary

The certified presentation bundles exactly the three classes listed below.
There is deliberately no global axiom asserting geometry for malformed raw
syntax; all evaluator equalities are proved downstream.
-/

#eval TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry.requiredAssumptionClasses
#check TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry.required_assumption_class_count
#check TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry.required_assumption_classes_unique
#check TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry.exactImportedScope
#check TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry.sourceScopeCaveat
#print axioms TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry.StandardDottedCanonicalPresentation
