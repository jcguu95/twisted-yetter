import TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

/-!
# Kernel axiom audit for source-bound local move recipes

The recipe mechanism is pure typed data.  Its coverage and shared-identity
theorems must use no project-specific axioms.
-/

#print axioms TwistedYetter.Kirby.SourceBoundLocalMoveRecipe.recipe_kind_count
#print axioms TwistedYetter.Kirby.SourceBoundLocalMoveRecipe.recipe_kinds_unique
#print axioms TwistedYetter.Kirby.SourceBoundLocalMoveRecipe.framed_isotopy_generator_count
#print axioms TwistedYetter.Kirby.SourceBoundLocalMoveRecipe.framed_isotopy_generators_unique
#print axioms TwistedYetter.Kirby.SourceBoundLocalMoveRecipe.SourceBoundRecipe.graphical_and_chain_recipe_ids_agree
