import TwistedYetter.Kirby.Final.Semantics.Independent.Entry
import TwistedYetter.Kirby.Presentation

/-!
# Proof-bearing bridge for serialized dotted puncture words

The v3 JSON payload supplies the ordered signed words.  It does not prove
that chosen spanning disks exist or reglue correctly.  Those topology facts
remain explicit proof inputs below.
-/

namespace TwistedYetter.Kirby.Final.DottedCutImplementationBridge

open TwistedYetter.Kirby.Presentation
open TwistedYetter.Semantics.Independent

def componentRole :
    Presentation.ComponentRole →
      TwistedYetter.Semantics.Independent.ComponentRole
  | .ordinary => .ordinary
  | .dotted => .dotted
  | .speciallyDotted => .speciallyDotted

def strandOrientation :
    Presentation.Orientation →
      TwistedYetter.Semantics.Independent.StrandOrientation
  | .positive => .positive
  | .negative => .negative

def component (input : ComponentSpec) :
    TwistedYetter.Semantics.Independent.Component where
  role := componentRole input.role
  orientation := strandOrientation input.orientation
  integerFraming := input.integerFraming

def punctureDirection :
    Presentation.PunctureDirection →
      TwistedYetter.Semantics.Independent.PunctureDirection
  | .withDiskOrientation => .withDiskOrientation
  | .againstDiskOrientation => .againstDiskOrientation

/--
Names relate a partial semantic trace bridge back to the exact v3 IDs.
The soundness fields prevent a bridge from silently rebinding a component or
strand name to different role, orientation, or ownership data.
-/
structure TraceIndexing
    (formal : FormalPresentation)
    (trace : CombinatorialLinkTrace) where
  componentName : trace.ComponentId → String
  strandName : trace.StrandId → String
  componentName_injective : Function.Injective componentName
  strandName_injective : Function.Injective strandName
  component_sound :
    ∀ semanticId rawComponent,
      formal.raw.component? (componentName semanticId) =
        some rawComponent →
      trace.components semanticId =
        component rawComponent
  strand_component_sound :
    ∀ semanticStrand rawStrand,
      formal.raw.strandDefinition? (strandName semanticStrand) =
        some rawStrand →
      componentName (trace.strands semanticStrand).component =
        rawStrand.componentId
  strand_orientation_sound :
    ∀ semanticStrand rawStrand,
      formal.raw.strandDefinition? (strandName semanticStrand) =
        some rawStrand →
      (trace.strands semanticStrand).orientation =
        strandOrientation rawStrand.orientation

/-- Every semantic puncture field is copied from one exact raw occurrence. -/
def PunctureMatchesRaw
    {formal : FormalPresentation}
    {trace : CombinatorialLinkTrace}
    (indexing : TraceIndexing formal trace)
    (semantic : DottedPuncture trace)
    (raw : RawDottedPuncture) : Prop :=
  indexing.componentName semantic.twoHandleComponent =
      raw.twoHandleComponentId ∧
    indexing.strandName semantic.strand = raw.strandId ∧
    semantic.direction = punctureDirection raw.direction ∧
    semantic.characterExponentSign = raw.characterExponentSign ∧
    semantic.cutPosition = raw.cutPosition

/--
This is the topology trust boundary.  The raw/semantic correspondence is
fully visible, while the three genuinely topological propositions are proof
fields and cannot be manufactured from the provenance hash.
-/
structure DottedCutTopologyCertificate
    (formal : FormalPresentation)
    (trace : CombinatorialLinkTrace)
    (indexing : TraceIndexing formal trace) where
  punctureWord :
    (dotted : trace.ComponentId) →
      (trace.components dotted).role = .dotted →
      List (DottedPuncture trace)
  exact_raw_words :
    ∀ dotted dottedRole,
      ∃ cut ∈ formal.raw.dottedCuts,
        cut.dottedComponentId = indexing.componentName dotted ∧
        List.Forall₂
          (PunctureMatchesRaw indexing)
          (punctureWord dotted dottedRole)
          cut.punctures
  every_raw_cut_represented :
    ∀ cut ∈ formal.raw.dottedCuts,
      ∃ (dotted : trace.ComponentId)
          (dottedRole : (trace.components dotted).role = .dotted),
        indexing.componentName dotted = cut.dottedComponentId
  punctures_complete_without_duplicate_occurrences :
    PunctureWordsHaveNoRepeatedOccurrences trace punctureWord
  simultaneous_cuts_compatible :
    CutOpenWordsAreCompatible trace punctureWord
  regluing_returns_exact_trace :
    RegluingReturnsOriginalTrace trace punctureWord

/--
A formal v3 payload together with a partial trace indexing and the genuine
dotted-cut topology certificate.  No category or evaluator data occurs here.
-/
structure CertifiedDottedPresentation where
  formal : FormalPresentation
  trace : CombinatorialLinkTrace
  indexing : TraceIndexing formal trace
  dottedTopology :
    DottedCutTopologyCertificate formal trace indexing

/-- Construct the frozen semantic dotted-cut datum without guessing words. -/
def CertifiedDottedPresentation.toDottedCutData
    (certified : CertifiedDottedPresentation) :
    DottedCutData certified.trace where
  punctureWord := certified.dottedTopology.punctureWord
  puncturesHaveNoRepeatedOccurrences :=
    certified.dottedTopology.punctures_complete_without_duplicate_occurrences
  cutOpenWordsAreCompatible :=
    certified.dottedTopology.simultaneous_cuts_compatible
  reglueReturnsOriginalTrace :=
    certified.dottedTopology.regluing_returns_exact_trace

/-- Signed intersection multiplicity recorded by one raw puncture word. -/
def signedMultiplicity (punctures : List RawDottedPuncture) : Int :=
  punctures.foldl
    (fun total puncture => total + puncture.characterExponentSign)
    0

end TwistedYetter.Kirby.Final.DottedCutImplementationBridge
