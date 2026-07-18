import TwistedYetter.Kirby.Presentation
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

def expectedFixtureContentHash : String :=
  "sha256:42eef430c68ffdc02d687958e0e1d702c3cee7ba3638cc15b664985c8e6779aa"

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
  IO.println
    ("PASS Lean replay + 2 fail-closed mutations: " ++
      "events=12 slices=13 content_hash=" ++
      formal.pinnedSourceHash)

end TwistedYetter.Kirby.PresentationArtifactReplay

def main := TwistedYetter.Kirby.PresentationArtifactReplay.main
