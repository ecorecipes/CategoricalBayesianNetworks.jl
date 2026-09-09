import CategoricalBayesianNetworksProofs.RawCertificate
import CategoricalBayesianNetworksProofs.CertificateSyntax

/-!
# Decoding and checking the versioned JSON certificate

Every record has an exact required-key set. Counts, ranks and positions are
nonnegative integer tokens; variable pointers are checked before constructing
`Fin` values. The declared variable count must match the data-array length.
Arrays retain their source order and multiplicity.

Successful schema decoding does not imply graph validity. The final stage
calls the existing proved `Network.check`, unchanged. `read_sound` proves that
successful reading yields a valid network, while `read_preserves_decoded`
proves that validation does not substitute a different network. These are
statements about parsed data, not about a Julia exporter/compiler/runtime.
-/

namespace OpenNet.RawCertificate.JSON
open Lean

abbrev Result := Except String

@[simp] private theorem bind_ok {A B : Type} (a : A) (f : A → Result B) :
    (Except.ok a >>= f) = f a := rfl

@[simp] private theorem bind_error {A B : Type} (e : String) (f : A → Result B) :
    (Except.error e >>= f) = Except.error e := rfl

def keys (j : Json) (expected : List String) : Result Unit := do
  let obj ← j.getObj?
  if obj.all (fun k _ => expected.contains k) && expected.all obj.contains then
    return ()
  else
    throw s!"object must contain exactly these fields: {expected}"

def field {A : Type} (j : Json) (name : String) (read : Json → Result A) : Result A :=
  (j.getObjVal? name >>= read).mapError (fun message => s!"{name}: {message}")

def natural (j : Json) : Result Nat := j.getNat?

def index (bound : Nat) (j : Json) : Result (Fin bound) := do
  let n ← natural j
  if h : n < bound then return ⟨n, h⟩
  else throw s!"variable index {n} is not below bound {bound}"

def list {A : Type} (read : Json → Result A) (j : Json) : Result (List A) := do
  let values ← j.getArr?
  values.toList.mapM read

def reference (j : Json) : Result Reference := do
  let tag ← field j "tag" Json.getStr?
  match tag with
  | "noRef" =>
    keys j ["tag"]
    return .noRef
  | "named" =>
    keys j ["tag", "id"]
    return .named (← field j "id" Json.getStr?)
  | "pointMass" =>
    keys j ["tag", "state"]
    return .pointMass (← field j "state" Json.getStr?)
  | "policy" =>
    keys j ["tag", "decision"]
    return .policy (← field j "decision" Json.getStr?)
  | _ => throw s!"unknown reference tag: {tag}"

def stateRow (j : Json) : Result StateRow := do
  keys j ["name", "position"]
  return ⟨← field j "name" Json.getStr?, ← field j "position" natural⟩

def inputRow (bound : Nat) (j : Json) : Result (InputRow bound) := do
  keys j ["varId", "position"]
  return ⟨← field j "varId" (index bound), ← field j "position" natural⟩

def attrs (j : Json) : Result VariableAttrs := do
  keys j ["name", "spaceRef", "states"]
  return ⟨← field j "name" Json.getStr?, ← field j "spaceRef" reference,
    ← field j "states" (list Json.getStr?)⟩

def variableData (j : Json) : Result VariableData := do
  keys j ["name", "spaceRef", "stateRows", "rank"]
  return ⟨← field j "name" Json.getStr?, ← field j "spaceRef" reference,
    ← field j "stateRows" (list stateRow), ← field j "rank" natural⟩

def mechanism (bound : Nat) (j : Json) : Result (MechanismData bound) := do
  keys j ["name", "kernelRef", "target", "inputRows"]
  return ⟨← field j "name" Json.getStr?, ← field j "kernelRef" reference,
    ← field j "target" (index bound), ← field j "inputRows" (list (inputRow bound))⟩

def boundary (bound : Nat) (j : Json) : Result (BoundaryRow bound) := do
  keys j ["varId", "attrs"]
  return ⟨← field j "varId" (index bound), ← field j "attrs" attrs⟩

def network (j : Json) : Result Network := do
  keys j ["format", "variableCount", "variableData", "mechanisms", "inputs", "outputs"]
  let format ← field j "format" Json.getStr?
  if format != "OpenNet.RawCertificate/v1" then throw "unsupported certificate format"
  let n ← field j "variableCount" natural
  let vars ← field j "variableData" (list variableData)
  if h : vars.length = n then
    return {
      variableCount := n
      variableData := fun i => vars[i.val]'(h.symm ▸ i.isLt)
      mechanisms := ← field j "mechanisms" (list (mechanism n))
      inputs := ← field j "inputs" (list (boundary n))
      outputs := ← field j "outputs" (list (boundary n)) }
  else
    throw "variableCount does not match variableData length"

def validate (N : Network) : Result Network :=
  if N.check then .ok N else .error
    "certificate failed Network.check (positions, states, references, interfaces, generators or ranks)"

def read (text : String) : Result Network := do
  let j ← CertificateSyntax.parse text
  let N ← network j
  validate N

theorem natural_roundtrip (n : Nat) : natural (toJson n) = .ok n := rfl

theorem index_roundtrip (bound n : Nat) (h : n < bound) :
    index bound (toJson n) = .ok ⟨n, h⟩ := by
  simp only [index, natural_roundtrip, bind_ok, dif_pos h]
  rfl

theorem index_value {bound : Nat} {j : Json} {i : Fin bound}
    (h : index bound j = .ok i) : natural j = .ok i.val := by
  unfold index at h
  cases hn : natural j with
  | error message => simp [hn] at h
  | ok n =>
    simp only [hn, bind_ok] at h
    split at h
    · cases h
      rfl
    · cases h

theorem validate_preserves {N M : Network} (h : validate N = .ok M) :
    M = N ∧ N.Valid := by
  unfold validate at h
  split at h
  · rename_i hc
    cases h
    exact ⟨rfl, N.check_sound hc⟩
  · cases h

theorem read_preserves_decoded {text : String} {N : Network} (h : read text = .ok N) :
    ∃ j, CertificateSyntax.parse text = .ok j ∧ network j = .ok N ∧ N.Valid := by
  unfold read at h
  cases hj : CertificateSyntax.parse text with
  | error message => simp [hj] at h
  | ok j =>
    simp only [hj, bind_ok] at h
    cases hn : network j with
    | error message => simp [hn] at h
    | ok M =>
      simp only [hn, bind_ok] at h
      obtain ⟨rfl, hv⟩ := validate_preserves h
      exact ⟨j, rfl, hn, hv⟩

theorem read_sound {text : String} {N : Network} (h : read text = .ok N) : N.Valid :=
  (read_preserves_decoded h).choose_spec.2.2

/-- Successful parsed data feeds the existing proved categorical normalization. -/
noncomputable def checkedNet {text : String} {N : Network} (h : read text = .ok N) :
    Net N.dom N.cod :=
  N.normalize (N.check_iff.mpr (read_sound h))

def referenceJson : Reference → Json
  | .noRef => Json.mkObj [("tag", .str "noRef")]
  | .named id => Json.mkObj [("tag", .str "named"), ("id", .str id)]
  | .pointMass state => Json.mkObj [("tag", .str "pointMass"), ("state", .str state)]
  | .policy decision => Json.mkObj [("tag", .str "policy"), ("decision", .str decision)]

theorem reference_roundtrip (r : Reference) : reference (referenceJson r) = .ok r := by
  cases r <;> rfl

def stateRowJson (r : StateRow) : Json :=
  Json.mkObj [("name", .str r.name), ("position", toJson r.position)]

theorem stateRow_roundtrip (r : StateRow) : stateRow (stateRowJson r) = .ok r := by
  cases r
  rfl

end OpenNet.RawCertificate.JSON
