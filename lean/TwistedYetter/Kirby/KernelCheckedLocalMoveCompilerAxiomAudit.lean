import TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler

/-!
# Axiom audit: kernel-checked local-move compiler

The compiler itself is only projection from a proof-carrying certificate.
These commands expose every inherited axiom on its public theorem surface.
-/

#print axioms TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler.required_certificate_class_count
#print axioms TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler.required_certificate_classes_unique
#print axioms TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler.CertifiedMove.generated_core_is_exact_target
#print axioms TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler.CertifiedMove.topologyMoveClass_mem_required
#print axioms TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler.CertifiedMove.certificateClass_mem_required
