import TwistedYetter.Kirby.HomologicallyTwistedInvariant

/-!
# Content-addressed computation artifact imports

R12 separates two claims which must never be confused.

* An `ExactInvariantValueCertificate` may expose a concrete invariant value,
  but only after clean provenance, exact arithmetic, complete coverage, a
  sealed evaluator profile, and an explicit R11 semantic binding are supplied.
* A `StructuralAggregateCertificate` proves only that a pinned distribution
  has complete denominator bookkeeping.  It has no constructor that produces
  an exact invariant value.

The existing Figure 21 pointed batch is represented by the second type.  Its
fifteen row denominators are checked, while dirty legacy provenance, a draft
diagram transcription, rounded output labels, an unsealed evaluator closure,
and a missing concrete R11 binding remain terminal blockers.
-/

namespace TwistedYetter.Kirby.ComputationArtifactImporter

open TwistedYetter.Kirby.Presentation

/--
A runtime-validated SHA-256 identifier.

Lean does not parse the digest bytes.  The Boolean records the external
validator's shape check, while the terminal artifact pins and rehashes the
actual bytes.
-/
structure Hash256 where
  value : String
  runtimeShapeChecked : Bool
  runtime_shape_checked : runtimeShapeChecked = true
  deriving Repr

namespace Hash256

/-- Reify one hash after the R12 runtime validator has checked its shape. -/
def ofRuntimeChecked (value : String) : Hash256 :=
  ⟨value, true, rfl⟩

/--
Convenience spelling for frozen literals.  The R12 runtime certificate must
rehash the referenced bytes before this Lean module is accepted.
-/
abbrev ofLiteral := ofRuntimeChecked

end Hash256

/-- Arithmetic policies understood by the exact importer. -/
inductive ArithmeticMode where
  | exactRational
  | exactCyclotomic
  | roundedComplex
  deriving Repr, DecidableEq

/-- Admission states are deliberately disjoint. -/
inductive ImportDisposition where
  | admittedExactValue
  | structuralOnly
  | terminalBlocked
  deriving Repr, DecidableEq

/-- Reasons which prevent a structural artifact from becoming an invariant. -/
inductive BlockerReason where
  | dirtyProvenance
  | draftDiagram
  | roundedOutput
  | missingR11Binding
  | unsealedEvaluatorClosure
  | missingMarkedH2Comparison
  deriving Repr, DecidableEq

/-- Immutable identity and provenance of one source artifact. -/
structure ArtifactEnvelope where
  schema : String
  fileHash : Hash256
  sourceCommit : String
  recordedDirty : Bool
  mutableAliasCount : Nat
  inconclusiveCount : Nat
  statusPass : Bool
  deriving Repr

/-- Exact category, diagram, and evaluator-independent input identity. -/
structure ComputationIdentity where
  realizationId : String
  rank : Nat
  categorySnapshotHash : Hash256
  categoryDataHash : Hash256
  diagramInputHash : Hash256
  projectedIrHash : Hash256
  couponGraphHash : Hash256
  deriving Repr

/--
Finite distribution bookkeeping.  Both observed sector count and both
distributions must independently account for the declared denominator.
-/
structure DistributionCertificate where
  expectedSectorCount : Nat
  observedSectorCount : Nat
  valueBucketCounts : List Nat
  projectorBucketCounts : List Nat
  observed_eq_expected :
    observedSectorCount = expectedSectorCount
  value_bucket_sum :
    valueBucketCounts.sum = observedSectorCount
  projector_bucket_sum :
    projectorBucketCounts.sum = observedSectorCount
  deriving Repr

namespace DistributionCertificate

/-- A distribution certificate really covers its declared denominator. -/
theorem coverage_complete (certificate : DistributionCertificate) :
    certificate.observedSectorCount = certificate.expectedSectorCount :=
  certificate.observed_eq_expected

/-- Every value bucket is included in the observed denominator. -/
theorem values_complete (certificate : DistributionCertificate) :
    certificate.valueBucketCounts.sum =
      certificate.expectedSectorCount := by
  rw [certificate.value_bucket_sum, certificate.observed_eq_expected]

/-- Every projector bucket is included in the observed denominator. -/
theorem projectors_complete (certificate : DistributionCertificate) :
    certificate.projectorBucketCounts.sum =
      certificate.expectedSectorCount := by
  rw [certificate.projector_bucket_sum, certificate.observed_eq_expected]

end DistributionCertificate

/--
An imported aggregate with complete structural bookkeeping.

There is intentionally no output value and no semantic evaluator witness in
this type.
-/
structure StructuralAggregateCertificate where
  artifact : ArtifactEnvelope
  identity : ComputationIdentity
  evaluatorEntryPointHash : Hash256
  arithmeticMode : ArithmeticMode
  distribution : DistributionCertificate
  claimBoundary : String
  deriving Repr

namespace StructuralAggregateCertificate

/-- Structural imports expose denominator completeness and nothing stronger. -/
theorem coverage_complete (certificate : StructuralAggregateCertificate) :
    certificate.distribution.observedSectorCount =
      certificate.distribution.expectedSectorCount :=
  certificate.distribution.coverage_complete

/-- Structural artifacts have the structural-only disposition. -/
def disposition (_ : StructuralAggregateCertificate) :
    ImportDisposition :=
  .structuralOnly

theorem disposition_not_exact
    (certificate : StructuralAggregateCertificate) :
    certificate.disposition ≠ .admittedExactValue := by
  simp [disposition]

end StructuralAggregateCertificate

/-- The exact target to which an external computation claims to be bound. -/
structure ExactInvariantTarget (K : Type) where
  identity : ComputationIdentity
  characterAssignmentHash : Hash256
  evaluatorProfileHash : Hash256
  evaluatorClosureHash : Hash256
  r11BindingCertificateHash : Hash256
  invariantValue : K
  r11BindingIsValid : Prop
  r11_binding_witness : r11BindingIsValid

/--
The only R12 certificate from which a concrete invariant value is exposed.

The equality to the R11 target is proof-relevant and cannot be replaced by a
status string or a matching rounded display value.
-/
structure ExactInvariantValueCertificate (K : Type) where
  artifact : ArtifactEnvelope
  target : ExactInvariantTarget K
  distribution : DistributionCertificate
  arithmeticMode : ArithmeticMode
  outputValue : K
  clean_source : artifact.recordedDirty = false
  alias_free : artifact.mutableAliasCount = 0
  pass_status : artifact.statusPass = true
  no_inconclusive : artifact.inconclusiveCount = 0
  exact_arithmetic :
    arithmeticMode = .exactRational ∨
      arithmeticMode = .exactCyclotomic
  output_sound : outputValue = target.invariantValue

namespace ExactInvariantValueCertificate

/-- Exact admission returns only the equality already bound to the R11 target. -/
theorem output_eq_invariant
    {K : Type}
    (certificate : ExactInvariantValueCertificate K) :
    certificate.outputValue = certificate.target.invariantValue :=
  certificate.output_sound

/-- Exact certificates, unlike structural aggregates, are admitted values. -/
def disposition
    {K : Type}
    (_ : ExactInvariantValueCertificate K) :
    ImportDisposition :=
  .admittedExactValue

end ExactInvariantValueCertificate

/-- A terminal blocker retains the structurally verified bytes and reasons. -/
structure TerminalBlockedImport where
  structural : StructuralAggregateCertificate
  blockers : List BlockerReason
  blockers_nonempty : blockers ≠ []
  exactAdmissionDisabled : Prop
  exact_admission_disabled_witness : exactAdmissionDisabled

namespace TerminalBlockedImport

/-- Terminal blockers have no exact-admission disposition. -/
def disposition (_ : TerminalBlockedImport) : ImportDisposition :=
  .terminalBlocked

theorem disposition_not_exact (blocked : TerminalBlockedImport) :
    blocked.disposition ≠ .admittedExactValue := by
  simp [disposition]

end TerminalBlockedImport

/-- One structurally imported batch and its global blockers. -/
structure StructuralImportBatch where
  batchArtifactHash : Hash256
  rows : List StructuralAggregateCertificate
  expectedRowCount : Nat
  row_count : rows.length = expectedRowCount
  blockers : List BlockerReason
  blockers_nonempty : blockers ≠ []
  exactAdmissionDisabled : Prop
  exact_admission_disabled_witness : exactAdmissionDisabled

namespace StructuralImportBatch

/-- Every row in a structural batch carries its own coverage proof. -/
theorem row_coverage_complete
    (batch : StructuralImportBatch)
    (row : StructuralAggregateCertificate)
    (_membership : row ∈ batch.rows) :
    row.distribution.observedSectorCount =
      row.distribution.expectedSectorCount :=
  row.coverage_complete

/-- A blocked structural batch cannot claim exact admission. -/
def disposition (_ : StructuralImportBatch) : ImportDisposition :=
  .terminalBlocked

theorem disposition_not_exact (batch : StructuralImportBatch) :
    batch.disposition ≠ .admittedExactValue := by
  simp [disposition]

end StructuralImportBatch

private def r11ControlEnvelope : ArtifactEnvelope where
  schema := "twisted-yetter.homologically-twisted-kirby-invariant.v1"
  fileHash := Hash256.ofLiteral
    "sha256:0b0cf045827fdfc6784771cfda58136099ee2e8cc5f547aedc81865b37f7724d"
  sourceCommit := "30f397f9e7e90bdb842751bffc52a9aec8fea480"
  recordedDirty := false
  mutableAliasCount := 0
  inconclusiveCount := 0
  statusPass := true

private def r11ControlIdentity : ComputationIdentity where
  realizationId := "r11-eight-move-all-alpha-exact-fixture"
  rank := 0
  categorySnapshotHash := Hash256.ofLiteral
    "sha256:b57342819b976cdfc071c2a13197bfe1de92f9727ce02fa534724d386add8f20"
  categoryDataHash := Hash256.ofLiteral
    "sha256:117bf045c8a99f753284f9ea0990cff4bfbc320b473925241b93053ec27384f2"
  diagramInputHash := Hash256.ofLiteral
    "sha256:43843db4f4b746b2811168d74f0979f4c73c28edd97bc84dd9bd154b89416edc"
  projectedIrHash := Hash256.ofLiteral
    "sha256:a08805a763e56bd5a469534c0f00b986eac0c99c5e84b7b7c6315e480a3b6036"
  couponGraphHash := Hash256.ofLiteral
    "sha256:9c0805c9f0152750c8ee5e3ddd78995ea56fdb61474606dcd5658c544b5fdb45"

/-- Exact toy/control packet used to prove the admission path is live. -/
def toyExactControl : ExactInvariantValueCertificate ℚ where
  artifact := r11ControlEnvelope
  target := {
    identity := r11ControlIdentity
    characterAssignmentHash := Hash256.ofLiteral
      "sha256:055ff74e68bdd1b07fd0898a635777aa98f639652a3b43e527e0af11c86cf946"
    evaluatorProfileHash := Hash256.ofLiteral
      "sha256:19575d5602f95b55011d4690c68d6333ed6ced74a94dbadcf0e111913f3b7da8"
    evaluatorClosureHash := Hash256.ofLiteral
      "sha256:0b0cf045827fdfc6784771cfda58136099ee2e8cc5f547aedc81865b37f7724d"
    r11BindingCertificateHash := Hash256.ofLiteral
      "sha256:19575d5602f95b55011d4690c68d6333ed6ced74a94dbadcf0e111913f3b7da8"
    invariantValue := (101 : ℚ) / 450
    r11BindingIsValid := True
    r11_binding_witness := True.intro
  }
  distribution := {
    expectedSectorCount := 4
    observedSectorCount := 4
    valueBucketCounts := [1, 1, 1, 1]
    projectorBucketCounts := [4]
    observed_eq_expected := rfl
    value_bucket_sum := by norm_num
    projector_bucket_sum := by norm_num
  }
  arithmeticMode := .exactRational
  outputValue := (101 : ℚ) / 450
  clean_source := rfl
  alias_free := rfl
  pass_status := rfl
  no_inconclusive := rfl
  exact_arithmetic := Or.inl rfl
  output_sound := rfl

theorem toy_exact_control_admitted :
    toyExactControl.outputValue =
      toyExactControl.target.invariantValue :=
  toyExactControl.output_eq_invariant

private def figure21DiagramInputHash : Hash256 :=
  Hash256.ofLiteral
    "sha256:b6f8459547a7cec415eb6c70acb89a40c37ab4cabd364330206685d8e579cbc5"

private def figure21ProjectedIrHash : Hash256 :=
  Hash256.ofLiteral
    "sha256:7b96de795e98bf8b521e33c9977c5eccbbde63e1d4296554ad388c609ff71695"

private def figure21CouponGraphHash : Hash256 :=
  Hash256.ofLiteral
    "sha256:f66f1ef64661c432c389b6c1db726de605055ea0cabe74005fa649ebbd32a26c"

private def rank2EvaluatorHash : Hash256 :=
  Hash256.ofLiteral
    "sha256:df32d4b30f2f7b4771c925e86cbee4d99027aef088b2ce2679aebdc7a904fa1d"

private def pointedChunkEvaluatorHash : Hash256 :=
  Hash256.ofLiteral
    "sha256:e8991359ec4e8712378b2138233abf133991700a93d3866edbaf6f7531f9ad06"

private def figure21Envelope
    (schema : String)
    (fileHash : Hash256)
    (sourceCommit : String) :
    ArtifactEnvelope where
  schema := schema
  fileHash := fileHash
  sourceCommit := sourceCommit
  recordedDirty := true
  mutableAliasCount := 0
  inconclusiveCount := 0
  statusPass := true

private def figure21Identity
    (realizationId : String)
    (rank : Nat)
    (categorySnapshotHash categoryDataHash : Hash256) :
    ComputationIdentity where
  realizationId := realizationId
  rank := rank
  categorySnapshotHash := categorySnapshotHash
  categoryDataHash := categoryDataHash
  diagramInputHash := figure21DiagramInputHash
  projectedIrHash := figure21ProjectedIrHash
  couponGraphHash := figure21CouponGraphHash

private def figure21Row
    (realizationId : String)
    (rank : Nat)
    (sourceSchema sourceCommit : String)
    (sourceHash categorySnapshotHash categoryDataHash evaluatorHash : Hash256)
    (expected : Nat)
    (valueBuckets projectorBuckets : List Nat)
    (valueSum : valueBuckets.sum = expected)
    (projectorSum : projectorBuckets.sum = expected) :
    StructuralAggregateCertificate where
  artifact := figure21Envelope sourceSchema sourceHash sourceCommit
  identity := figure21Identity
    realizationId rank categorySnapshotHash categoryDataHash
  evaluatorEntryPointHash := evaluatorHash
  arithmeticMode := .roundedComplex
  distribution := {
    expectedSectorCount := expected
    observedSectorCount := expected
    valueBucketCounts := valueBuckets
    projectorBucketCounts := projectorBuckets
    observed_eq_expected := rfl
    value_bucket_sum := valueSum
    projector_bucket_sum := projectorSum
  }
  claimBoundary :=
    "Complete fixed-label denominator bookkeeping only; no exact R11 value."

private def rank2SourceHash : Hash256 :=
  Hash256.ofLiteral
    "sha256:82bf43b163740e3e90fc22104f2ea6afff2333468646aa78faa8a255fd763853"

private def rank2ValueBuckets : List Nat :=
  [1024, 256, 256, 240, 272]

private def rank3ValueBuckets : List Nat :=
  [118098, 19845, 19602, 19602]

private def rank4EvenValueBuckets : List Nat :=
  [3145728, 524800, 523776]

private def rank4OddValueBuckets : List Nat :=
  [3145728, 262144, 262144, 262656, 261632]

private def rank4Z4ValueBuckets : List Nat :=
  [3145728, 122880, 122880, 131072, 131072, 139776, 131072,
    131072, 138752]

private def rank5ValueBuckets : List Nat :=
  [39062500, 1952500, 1952500, 1955625, 1952500, 1952500]

/-- The fifteen Figure 21 pointed rows, imported only structurally. -/
def figure21PointedRows : List StructuralAggregateCertificate :=
  [
    figure21Row
      "rank2-cyclic-z2-semion-minus" 2
      "twisted-yetter.figure21-rank2-semion-modular-evaluation.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      rank2SourceHash
      (Hash256.ofLiteral
        "sha256:e52647abd74604ca450085f9df7d063fb39d8eb43b43847278868c2b3de39ba1")
      (Hash256.ofLiteral
        "sha256:cb8423c8e0253a34069e41d94870a952cc5a552af5fec13f65a6f2833c760e3d")
      rank2EvaluatorHash 2048 rank2ValueBuckets [1024, 1024]
      (by norm_num [rank2ValueBuckets]) (by norm_num),
    figure21Row
      "rank2-cyclic-z2-semion-plus" 2
      "twisted-yetter.figure21-rank2-semion-modular-evaluation.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      rank2SourceHash
      (Hash256.ofLiteral
        "sha256:b6e1fcedc002a8bad19e62ce667a79bc4592557f4ad2667ee53b40db2f23c3cb")
      (Hash256.ofLiteral
        "sha256:6f6f8391b0c99c9c8e178541ec4262ef0188b51ad7add48e9a1b89eb450ed3a8")
      rank2EvaluatorHash 2048 rank2ValueBuckets [1024, 1024]
      (by norm_num [rank2ValueBuckets]) (by norm_num),
    figure21Row
      "rank3-cyclic-z3-minus" 3
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:65e1acbf34e471f8b0f101672ece89b95d5daea4f33fd6b9406f296306d2a977")
      (Hash256.ofLiteral
        "sha256:181d796654800e7bbe1561ebf74a8b1f7d4a2898fa624af3359b0a3b4a35b5af")
      (Hash256.ofLiteral
        "sha256:ef0fa273bd48c7ead003268c992d87f4520cfa80884412574a9fab1b05482628")
      pointedChunkEvaluatorHash 177147 rank3ValueBuckets [118098, 59049]
      (by norm_num [rank3ValueBuckets]) (by norm_num),
    figure21Row
      "rank3-cyclic-z3-plus" 3
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:681af404e7c6fe8e0899fc885e152837c67ac9a788427762f478dcf3aa2943f3")
      (Hash256.ofLiteral
        "sha256:acc30096ffcec2b6a2d4f974dafda8fc6c8e77af1eda6ca3e971432364b4f930")
      (Hash256.ofLiteral
        "sha256:37f67932b8fe4efb70fa3cb138845b80df2a2205085718de4ed429441fb543fb")
      pointedChunkEvaluatorHash 177147 rank3ValueBuckets [118098, 59049]
      (by norm_num [rank3ValueBuckets]) (by norm_num),
    figure21Row
      "rank4-pointed-z2xz2-q002" 4
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:ba52b45ca958daa304009c9fa54e4f3f74c9906bf2c40a3d1042341b3ff349d3")
      (Hash256.ofLiteral
        "sha256:328f84e089e496e9685f39bb0193f4c2dcc045acf0fdb8a738b3ebe312acdf2b")
      (Hash256.ofLiteral
        "sha256:938cf851cc4e80ef77acaa2b00459a61c897e9c34d7c5c1388d6040855449bae")
      pointedChunkEvaluatorHash 4194304 rank4EvenValueBuckets
      [3145728, 1048576]
      (by norm_num [rank4EvenValueBuckets]) (by norm_num),
    figure21Row
      "rank4-pointed-z2xz2-q013" 4
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:b4d1973344d4bfaccad18e726988be83b119befa5cc525fc6b7ba65463ecd060")
      (Hash256.ofLiteral
        "sha256:165ecb5fb3f451140cca13a149a952c29e6456015090b3745791ce771d8fd5d8")
      (Hash256.ofLiteral
        "sha256:7011c498e4292edda021b8f45201cefd066ae9d9b2bdded22ed7c856b943cb16")
      pointedChunkEvaluatorHash 4194304 rank4OddValueBuckets
      [3145728, 1048576]
      (by norm_num [rank4OddValueBuckets]) (by norm_num),
    figure21Row
      "rank4-pointed-z2xz2-q112" 4
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:7fbf7bfffc66d48ac2e71ef6ea7877298f69b2f0b771a8e5b71664e5aff6fb63")
      (Hash256.ofLiteral
        "sha256:6c30bf416c3717b8de3f9f863ec29744c05604e4d4bdd4193156433e23095b38")
      (Hash256.ofLiteral
        "sha256:f9e055fb5a06e6c4ea9bf77215191586deb3b1c42863df46a5b0a5b68663119e")
      pointedChunkEvaluatorHash 4194304 rank4OddValueBuckets
      [3145728, 1048576]
      (by norm_num [rank4OddValueBuckets]) (by norm_num),
    figure21Row
      "rank4-pointed-z2xz2-q222" 4
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:4c48f49d3c22c3152b2747886706fb9c2cbfa3191963918b3cdc508a225b398f")
      (Hash256.ofLiteral
        "sha256:4a395e0c9e5d5cc54b70873127cb16f91ccad476cb4ea99f165be0b5d8c3d3f9")
      (Hash256.ofLiteral
        "sha256:b422d65880e61a17c2ffb1f56631e016fe539616c7c69af4c40be8d75a5055aa")
      pointedChunkEvaluatorHash 4194304 rank4EvenValueBuckets
      [3145728, 1048576]
      (by norm_num [rank4EvenValueBuckets]) (by norm_num),
    figure21Row
      "rank4-pointed-z2xz2-q233" 4
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:d8a65eb7115d70d3f13c616ef932cd26cb1c594d9bff80782fa29bddc5b52117")
      (Hash256.ofLiteral
        "sha256:a2d43d9be5099cc056f1110f2b8f5dc747c6d942615de88ecc203aa2d8d4bb38")
      (Hash256.ofLiteral
        "sha256:9ef5f588ad0d396d268a463d652e90fb92e128404ba2dffda3aef195229535a9")
      pointedChunkEvaluatorHash 4194304 rank4OddValueBuckets
      [3145728, 1048576]
      (by norm_num [rank4OddValueBuckets]) (by norm_num),
    figure21Row
      "rank4-pointed-z4-k1" 4
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:98ee054afc4312bffb1d799025fd6a18cf469b3760ef116192ad7b1b06668dbd")
      (Hash256.ofLiteral
        "sha256:9130fd7100685e598ed4c09d96a07a71e23c81c4b7bc9066e20c32242573275c")
      (Hash256.ofLiteral
        "sha256:3690c9bd2acc18a423f1dea86fb5ba2a3ec18cf2b729b5211e8311723336a59d")
      pointedChunkEvaluatorHash 4194304 rank4Z4ValueBuckets
      [3145728, 1048576]
      (by norm_num [rank4Z4ValueBuckets]) (by norm_num),
    figure21Row
      "rank4-pointed-z4-k3" 4
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:4c8d32d347a81a6ad911c51db82963123fc0aefc0b84a816cc6ced794fb85834")
      (Hash256.ofLiteral
        "sha256:f8a53b75687a7fddfcdc6ece8df245ee4d53c6f067607c6e41d3847db37c735b")
      (Hash256.ofLiteral
        "sha256:03eb61f1e94897382538bd5c7cbd85a2ccddc847b37aa41e467bf76e6a281c59")
      pointedChunkEvaluatorHash 4194304 rank4Z4ValueBuckets
      [3145728, 1048576]
      (by norm_num [rank4Z4ValueBuckets]) (by norm_num),
    figure21Row
      "rank4-pointed-z4-k5" 4
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:abe629e2cd548f7570fd28fba9f1d74a8fbedb47495ad1bf9e0debd228ed3fcc")
      (Hash256.ofLiteral
        "sha256:467d41034048b43117d5353aac33927d62ae7970dc47d9096ae339c6b9d7db3e")
      (Hash256.ofLiteral
        "sha256:77ca1abbcd1caddaee38efce21a94869dd641e57f654529373a07e806d8968c3")
      pointedChunkEvaluatorHash 4194304 rank4Z4ValueBuckets
      [3145728, 1048576]
      (by norm_num [rank4Z4ValueBuckets]) (by norm_num),
    figure21Row
      "rank4-pointed-z4-k7" 4
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:1729a8d8f683e1af41c9c868b16eb15935797e7e2078b2358b82a3efe319760b")
      (Hash256.ofLiteral
        "sha256:fea42779d4411598fccb71013164a10ac567b738bf2824749cdced4190c96ba2")
      (Hash256.ofLiteral
        "sha256:0d011e1d787deb105e0db8a08e4da2661c112e373d0287c31c41c0662f80a125")
      pointedChunkEvaluatorHash 4194304 rank4Z4ValueBuckets
      [3145728, 1048576]
      (by norm_num [rank4Z4ValueBuckets]) (by norm_num),
    figure21Row
      "rank5-su5-1-s1" 5
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:afd134937b6ac957bb2c30e0e3b72a30398e2900e6585860f9384e075fdd230d")
      (Hash256.ofLiteral
        "sha256:e4dda8682349c012b78fa55e43d602aa76aba03c65abfb9d61594ab188e0d778")
      (Hash256.ofLiteral
        "sha256:51ad31b84da73d922f60cf449130c6a590c330828cb9e15557a3665c873e2ca8")
      pointedChunkEvaluatorHash 48828125 rank5ValueBuckets
      [39062500, 9765625]
      (by norm_num [rank5ValueBuckets]) (by norm_num),
    figure21Row
      "rank5-su5-1-s2" 5
      "twisted-yetter.figure21-pointed-category-aggregate.v1"
      "1f62269d14d13f4333be9783c7e6174bdfdfb9cf"
      (Hash256.ofLiteral
        "sha256:57bad2251e5fde1f4c07622a461557b8dd0f38c6b9afff96e75c24eadd3d3e36")
      (Hash256.ofLiteral
        "sha256:53764e4181911cc7e6e5bd8856785c3157dcfadde621ce894d22f30edf653d0a")
      (Hash256.ofLiteral
        "sha256:149fecbc7cef2295b751f5ae1bcacd19a71a3fc1bc85e6dc1fdbd410b15237bd")
      pointedChunkEvaluatorHash 48828125 rank5ValueBuckets
      [39062500, 9765625]
      (by norm_num [rank5ValueBuckets]) (by norm_num)
  ]

private def figure21Blockers : List BlockerReason :=
  [
    .dirtyProvenance,
    .draftDiagram,
    .roundedOutput,
    .missingR11Binding,
    .unsealedEvaluatorClosure,
    .missingMarkedH2Comparison
  ]

/-- Terminal R12 import state for the existing Figure 21 pointed batch. -/
def figure21PointedBatch : StructuralImportBatch where
  batchArtifactHash := Hash256.ofLiteral
    "sha256:b7d78b4f04ed013b763b5c853cfe570acb6e469bc829628a732e7bff2264763c"
  rows := figure21PointedRows
  expectedRowCount := 15
  row_count := rfl
  blockers := figure21Blockers
  blockers_nonempty := by
    simp [figure21Blockers]
  exactAdmissionDisabled :=
    figure21Blockers ≠ []
  exact_admission_disabled_witness := by
    simp [figure21Blockers]

theorem figure21_pointed_row_count :
    figure21PointedBatch.rows.length = 15 :=
  figure21PointedBatch.row_count

theorem figure21_structural_coverage_complete
    (row : StructuralAggregateCertificate)
    (membership : row ∈ figure21PointedBatch.rows) :
    row.distribution.observedSectorCount =
      row.distribution.expectedSectorCount :=
  figure21PointedBatch.row_coverage_complete row membership

theorem figure21_terminal_blocker_count :
    figure21PointedBatch.blockers.length = 6 := by
  rfl

theorem figure21_not_promoted_to_invariant_values :
    figure21PointedBatch.disposition ≠ .admittedExactValue :=
  figure21PointedBatch.disposition_not_exact

end TwistedYetter.Kirby.ComputationArtifactImporter
