# Required Julia exporter: `OpenNet.RawCertificate/v1`

This is the precise remaining Julia-side interface requested by the Lean
category/semantics track. It is a **new exporter contract**, not a claim that
the Julia exporter is proved correct. The matching Lean JSON reader is now
available as `lake exe check_certificate PATH`.

Proposed API:

```julia
open_network_certificate(o::OpenBayesNetCospan; ranks = nothing)
```

Return a JSON-compatible `NamedTuple` or dictionary. Serialization may use the
ecosystem's existing JSON infrastructure; no new dependency is required.
The exact payload keys are:

```text
format        = "OpenNet.RawCertificate/v1"
variableCount = nonnegative integer
variableData  = variable-record array, length variableCount
mechanisms    = mechanism-record array
inputs        = input-boundary-row array
outputs       = output-boundary-row array
```

The machine-readable fixture
[`certificate-fixtures/mixed.json`](certificate-fixtures/mixed.json) encodes
the already kernel-checked `RawCertificate.certificate` example. Its `format`
is an envelope version; the remaining fields are the existing Lean record.

## Required extraction algorithm

1. Call `validate(o; unique_names=false)`. Do **not** require globally unique
   variable/mechanism names.
2. Enumerate **all** apex variable part IDs, including hidden variables, in
   their current part iteration order. Build an explicit bijective dictionary
   `oldVariablePartId => denseIndex - 1`. Never map by variable name.
3. Enumerate **all** mechanisms in current part order, including mechanisms
   with no path to an output. Keep their target and every input occurrence.
4. Group `State` rows by `state_variable` and `Input` rows by `input_mechanism`.
   Copy actual position attributes, rather than regenerating `1..n`. Row array
   order is immaterial: Lean sorts by the copied positions and checks the
   resulting profile. Do not deduplicate input variables.
5. Read boundary variable maps from the actual left/right legs in foot order.
   Preserve output order and multiplicity. Input/output overlap is allowed.
6. Read each boundary row's attributes from its **foot**, not by reconstructing
   them from the apex. The checker must be able to compare the supplied foot
   and apex attributes rather than receiving the same data twice by construction.
7. Supply a rank for every apex variable. With `ranks=nothing`, the 0-based
   position in `topological_order(apex(o))` is sufficient. If caller-supplied
   ranks are supported, use a dictionary keyed by source variable part ID,
   require total coverage, nonnegative integer values, and strict
   `rank[parent] < rank[target]` on every input occurrence.

No numerical values are needed for this minimal structural exporter.

## Exact record shapes

Variable record:

```json
{
  "name": "x",
  "spaceRef": {"tag": "named", "id": "bool:x"},
  "stateRows": [
    {"name": "true", "position": 2},
    {"name": "false", "position": 1}
  ],
  "rank": 0
}
```

Mechanism record:

```json
{
  "name": "parity",
  "kernelRef": {"tag": "named", "id": "kernel:parity"},
  "target": 1,
  "inputRows": [
    {"varId": 0, "position": 2},
    {"varId": 0, "position": 1}
  ]
}
```

Boundary row:

```json
{
  "varId": 0,
  "attrs": {
    "name": "x",
    "spaceRef": {"tag": "named", "id": "bool:x"},
    "states": ["false", "true"]
  }
}
```

`target` and `varId` are **0-based dense variable indices**, strictly below
`variableCount`. Positions remain the original **1-based** attributes.
Emit integer JSON tokens: the reader deliberately rejects fractional and
exponent spellings, even when a spelling such as `1.0` has an integral value.
`attrs.states` is the foot's state-name list in `state_position` order.
Names and reference payloads are exact `String` conversions of the source
strings/symbols: no case folding, sanitization or generated renaming.

Reference encodings are exactly:

```json
{"tag": "noRef"}
{"tag": "named", "id": "stable-id"}
{"tag": "pointMass", "state": "state-name"}
{"tag": "policy", "decision": "decision-name"}
```

Do not stringify the entire reference object or discard its tag.

## Required exporter regression cases

* The supplied fixture: unordered state/input rows, repeated parent variable,
  copied output, pass-through output, hidden generator, nontrivial references.
  Compare normalized row profiles when the exported row-array order differs.
* `compose_structural` of pieces with colliding names: use part IDs throughout,
  retain both unglued parts, and export successfully.
* Empty network; hidden scalar with both feet empty; repeated outputs with
  different foot part IDs pointing to one apex variable.
* All four reference constructors and distinct `space_ref` values.
* A variable/mechanism part renumbering: exported dense indices may change,
  but labels/references and ordered incidence must not.
* Bad supplied rank dictionaries should fail, not be silently replaced.

The existing Lean checker rejects duplicate/gapped/zero positions, bad ranks,
bad attributed feet, duplicate generators/inputs, and incomplete exogenous
coverage. JSON parsing, integer-bound checks constructing `Fin`, and the
exporter/runtime relation were separate outer translation obligations at the
contract's introduction. The first two now have an implemented strict reader
with acceptance/value-preservation lemmas and CLI regression coverage; full
lexical correctness and the Julia exporter/runtime relation are not thereby
proved.

## Optional numeric payload: keep it separate

If a model/table exporter is added, key each binding by **mechanism index**,
retain its full kernel reference/profile, and export:

* ordered parent state counts, including repeated occurrences;
* child state count;
* dimensions `(child, parent₁, ..., parentₖ)` and column-major flattened entries;
* a lossless numeric encoding.

Do not silently normalize the stored table. For `Float64`, a bit-preserving
binary64 encoding is preferable to pretending decimal JSON numbers are exact
normalized reals. Exact local Lean normalization is stronger than acceptance
within `atol`; an approximately normalized payload must remain explicitly
approximate unless a separately stated transformation/proof is supplied.
This numeric extension is **not required** for the minimal structural exporter.
