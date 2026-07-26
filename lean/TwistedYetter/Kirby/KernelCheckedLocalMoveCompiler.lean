import TwistedYetter.Kirby.CanonicalRawLocalMoveTarget

/-!
# Kernel-checked local-move certificates

The serialized `GraphicalEditProgram` records the name of a Kirby move and
its component IDs, but it does not contain enough typed ribbon-diagram data
to prove that an arbitrary replacement window realizes that move.  Treating
it as a total compiler input would therefore be unsound.

The formal route in this file is fail closed.  An admitted local move carries
an actual term of the eight-constructor `LocalCycleCalculation` grammar,
indexed by the exact source-backed topology move and its canonical
handle-chain enrichment.  Such a term contains typed diagram isotopies,
ordinary or generalized slide proof terms, or cancellation factorizations;
it cannot contain a bare equality of normalized scalar values.

`compile` is total on this proof-carrying input.  The older raw-window target
remains useful for checking endpoint bytes, but it is not an admission route
to the four-manifold theorem.
-/

namespace TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleLocalInvariance
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalRawLocalMoveTarget
open TwistedYetter.Kirby.CanonicalSourceBackedMove
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- The exact eight terminal certificate classes accepted by the compiler. -/
inductive CertificateClass where
  | framedIsotopy
  | oneOverOne
  | twoOverOne
  | twoOverTwo
  | oneTwoBirth
  | oneTwoDeath
  | twoThreeBirth
  | twoThreeDeath
  deriving Repr, BEq, DecidableEq

/-- Machine-visible denominator of admitted local graphical certificates. -/
def requiredCertificateClasses : List CertificateClass :=
  [
    .framedIsotopy,
    .oneOverOne,
    .twoOverOne,
    .twoOverTwo,
    .oneTwoBirth,
    .oneTwoDeath,
    .twoThreeBirth,
    .twoThreeDeath
  ]

theorem required_certificate_class_count :
    requiredCertificateClasses.length = 8 := by
  rfl

theorem required_certificate_classes_unique :
    requiredCertificateClasses.Nodup := by
  decide

/--
One exact topology move together with its kernel-checked graphical proof.

There is deliberately no certificate hash, evaluator function, output value,
or equality in `K` in this structure.  Hashes may bind serialized evidence to
a term externally, but only the term below has mathematical force.
-/
structure CertifiedMove
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2) where
  topologyMove :
    TopologicalTableTwoMove source.topology target.topology
  calculation :
    LocalCycleCalculation 𝒞 automorphism
      (CanonicalSourceBackedMove.enrichedMove topologyMove)

namespace CertifiedMove

/-- Total compilation is projection of the checked proof term. -/
def compile
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (certificate : CertifiedMove 𝒞 automorphism source target) :
    LocalCycleCalculation 𝒞 automorphism
      (CanonicalSourceBackedMove.enrichedMove certificate.topologyMove) :=
  certificate.calculation

/-- The raw endpoint core remains independently checked for every certificate. -/
theorem generated_core_is_exact_target
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (certificate : CertifiedMove 𝒞 automorphism source target) :
    canonicalEngine.apply
        (instructionOfMove certificate.topologyMove) =
      PresentationCore.ofFormal target.topology.formal :=
  canonicalEngine.generates_exact_target certificate.topologyMove

/-- Read the directed class of an exact source-backed topology move. -/
def topologyMoveClass
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (move : TopologicalTableTwoMove source.topology target.topology) :
    CertificateClass :=
  match move with
  | .framedIsotopy .. => .framedIsotopy
  | .oneOverOne .. => .oneOverOne
  | .twoOverOne .. => .twoOverOne
  | .twoOverTwo .. => .twoOverTwo
  | .oneTwoBirth .. => .oneTwoBirth
  | .oneTwoDeath .. => .oneTwoDeath
  | .twoThreeBirth .. => .twoThreeBirth
  | .twoThreeDeath .. => .twoThreeDeath

/-- Read the terminal class of a checked certificate. -/
def certificateClass
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (certificate : CertifiedMove 𝒞 automorphism source target) :
    CertificateClass :=
  topologyMoveClass certificate.topologyMove

/-- Every exact topology move belongs to the closed directed denominator. -/
theorem topologyMoveClass_mem_required
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (move : TopologicalTableTwoMove source.topology target.topology) :
    topologyMoveClass move ∈ requiredCertificateClasses := by
  cases move <;> simp [topologyMoveClass, requiredCertificateClasses]

/-- Every accepted certificate terminates in exactly one whitelisted case. -/
theorem certificateClass_mem_required
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (certificate : CertifiedMove 𝒞 automorphism source target) :
    certificate.certificateClass ∈ requiredCertificateClasses := by
  exact topologyMoveClass_mem_required certificate.topologyMove

end CertifiedMove

/-- The former raw auto-compilation target is not an admitted evidence type. -/
def rawWindowAdmissionStatus : String :=
  "REJECTED_UNDERSPECIFIED_RAW_GRAPHICAL_PROGRAM"

/-- The proof-carrying route is total and fail closed. -/
def certifiedCompilerStatus : String :=
  "PASS_KERNEL_CHECKED_EIGHT_CASE_CERTIFICATE_COMPILER"

end TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler
