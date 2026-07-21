import TwistedYetter.Kirby.ComponentRibbonDiagram

/-!
# Kernel axiom audit for category-neutral component ribbon diagrams

The free syntax and its interpreter must not introduce a project axiom.
-/

#print axioms TwistedYetter.Kirby.ComponentRibbonDiagram.ComponentAtom.interpret
#print axioms TwistedYetter.Kirby.ComponentRibbonDiagram.ComponentBoundary.interpret
#print axioms TwistedYetter.Kirby.ComponentRibbonDiagram.ComponentDiagram.interpret
#print axioms TwistedYetter.Kirby.ComponentRibbonDiagram.ComponentDiagram.Context.interpret
#print axioms TwistedYetter.Kirby.ComponentRibbonDiagram.ComponentDiagram.Context.interpret_plug
#print axioms
  TwistedYetter.Kirby.ComponentRibbonDiagram.ComponentDiagram.Context.interpret_heq_of_eq_on_hole_and_componentIds
