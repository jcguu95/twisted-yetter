import TwistedYetter.Kirby.PresentationExecutionTrace
import Lean.Data.Json.Parser

/-!
# Runtime replay of the repository presentation fixture

The Python admission step recomputes the canonical SHA-256. This executable
independently asks Lean to parse the exact same JSON bytes, execute every
slice event, compare every declared slice and writhe, and pin the artifact
content hash rather than the provenance source hash.
-/

namespace TwistedYetter.Kirby.PresentationArtifactReplay

open Lean
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.PresentationExecutionTrace

def expectedFixtureContentHash : String :=
  "sha256:1362a4b9836f2eb127f91e8ce795ecc48825ef714494f341a55733c915458038"

def fail (message : String) : IO α :=
  throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let path ←
    match args with
    | [path] => pure path
    | _ => fail "usage: PresentationArtifactReplay <presentation.json>"
  let bytes ← IO.FS.readFile path
  let json ←
    match Json.parse bytes with
    | .ok parsed => pure parsed
    | .error message => fail ("JSON parse failed: " ++ message)
  let formal ←
    match FormalPresentation.fromJson json with
    | .ok accepted => pure accepted
    | .error message => fail ("Lean presentation admission failed: " ++ message)
  let execution ←
    match buildClosedExecutionCertificate formal with
    | .ok certificate => pure certificate
    | .error message =>
        fail ("typed closed-execution certificate failed: " ++ message)
  unless RawPresentation.toJson formal.raw == json do
    fail "Lean snake-case codec did not round-trip the repository JSON"
  unless formal.pinnedSourceHash == expectedFixtureContentHash do
    fail "Lean did not pin the expected presentation content hash"
  if formal.pinnedSourceHash == formal.provenanceSourceHash then
    fail "content hash was silently confused with provenance source hash"
  unless formal.raw.events.length == 12 do
    fail "unexpected fixture event count"
  unless formal.raw.declaredSlices.length == 13 do
    fail "unexpected fixture slice count"
  unless formal.raw.dottedCuts.length == 1 do
    fail "unexpected dotted cut count"
  let cut ←
    match formal.raw.dottedCuts with
    | [cut] => pure cut
    | _ => fail "fixture does not contain exactly one dotted cut"
  unless cut.punctures.length == 2 do
    fail "unexpected dotted puncture count"
  unless execution.trace.stepCount == 12 do
    fail "typed execution trace did not execute all 12 events"
  unless execution.trace.states.length == 13 do
    fail "typed execution trace did not expose all 13 slices"
  unless execution.trace.eventIds ==
      formal.raw.events.map SliceEvent.eventId do
    fail "typed execution trace silently reordered event IDs"
  unless formal.raw.declaredSlices ==
      RawPresentation.declareSlicesFrom 0 execution.trace.states do
    fail "typed execution trace silently diverged from declared slices"
  let staleSlices : RawPresentation :=
    { formal.raw with declaredSlices := [] }
  match staleSlices.validate with
  | .error "declared Morse slices do not match event execution" => pure ()
  | .error message =>
      fail ("stale-slice mutation failed for the wrong reason: " ++ message)
  | .ok () => fail "stale declared slices were silently admitted"
  let unknownField :=
    json.setObjVal! "alias" "current"
  match RawPresentation.fromJson unknownField with
  | .error "presentation keys mismatch" => pure ()
  | .error message =>
      fail ("unknown-field mutation failed for the wrong reason: " ++ message)
  | .ok _ => fail "unknown presentation field was silently admitted"
  let staleV2 :=
    (json.setObjVal! "schema" "twisted-yetter.kirby-presentation.v2")
  match FormalPresentation.fromJson staleV2 with
  | .error "unsupported presentation schema" => pure ()
  | .error message =>
      fail ("v2 mutation failed for the wrong reason: " ++ message)
  | .ok _ => fail "v2 payload was silently migrated"
  let puncture ←
    match cut.punctures with
    | puncture :: _ => pure puncture
    | [] => fail "fixture dotted cut has no puncture"
  let wrongSign : RawPresentation :=
    {
      formal.raw with
      dottedCuts := [
        {
          cut with
          punctures := [
            { puncture with characterExponentSign := -1 }
          ]
        }
      ]
    }
  match wrongSign.validateDottedCuts with
  | .error
      "dotted puncture direction/exponent sign convention mismatch" =>
      pure ()
  | .error message =>
      fail ("wrong-sign mutation failed for the wrong reason: " ++ message)
  | .ok () => fail "wrong dotted puncture sign was silently admitted"
  let wrongPosition : RawPresentation :=
    {
      formal.raw with
      dottedCuts := [
        {
          cut with
          punctures := [
            { puncture with cutPosition := 1 }
          ]
        }
      ]
    }
  match wrongPosition.validateDottedCuts with
  | .error "dotted puncture cut_position must equal its list index" =>
      pure ()
  | .error message =>
      fail ("wrong-position mutation failed for the wrong reason: " ++ message)
  | .ok () => fail "wrong dotted puncture position was silently admitted"
  IO.println
    ("PASS Lean replay + closed typed trace + 5 fail-closed mutations: " ++
      "events=12 slices=13 trace_steps=12 content_hash=" ++
      formal.pinnedSourceHash)

end TwistedYetter.Kirby.PresentationArtifactReplay

def main := TwistedYetter.Kirby.PresentationArtifactReplay.main
