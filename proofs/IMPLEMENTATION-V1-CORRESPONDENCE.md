# Corrected runtime v1: category-semantics source correspondence

**Authority:** `backlog3/implementation-v1/SOURCE.json`  
**SHA256:** `070b9b202f6e703b077b7527d47c1d53cab047fd969608ee733bc1308ccfa5c7`

This is a source-correspondence supplement, not a new mathematical proof
milestone or another prover's result. All earlier frozen trees remain
unchanged. The existing 26-file Lean source closure and 45-page proof PDF
remain the mathematical evidence.

## Checked correspondence updates

| Corrected frozen Julia source | Correspondence to the existing Lean construction |
|---|---|
| `CategoricalBayesianNetworks.jl/src/composition.jl:126–136` | `compose_structural` validates both operands structurally, checks full positional interface agreement, performs the pushout, and validates with `unique_names=false`. This is the intended runtime counterpart of the existing total `Net.comp` / structural quotient operation. |
| `composition.jl:106–110` | `compose` delegates to `compose_structural` and then applies `_validate_composite`. The compatibility wrapper remains name-safe and may reject unglued name collisions; it is not the unrestricted category operation. |
| `wiring.jl:24–46` and `:181` | `VariablePort` includes `space_ref` in construction/equality/hash and restores it when rebuilding a variable. This agrees with preserving the full `VariableAttrs` type, rather than erasing references. |
| `wiring.jl:378–400` | The builder counts each ordered parent occurrence, makes that many extra copies, then moves copies into parent order. The Lean semantics already reads the complete ordered list; repeated occurrences are not deduplicated. This source change requires no change to those theorems. |
| `BayesianNetworkInference.jl/src/factors.jl:353–384` | Repeated named input slots are selected along the diagonal before constructing a unique-variable factor. This matches assigning one state per variable and reading it at every occurrence. The category proof does not certify this Julia conversion routine itself. |
| `BayesianNetworks.jl/src/evaluation.jl:50–62` and `:77–86` | The brute-force factors keep target/input axis positions, including repeats, and read each at the same complete assignment. This is the local-factor content of `apexWeight`. |
| `CategoricalBayesianNetworks.jl/src/evaluation.jl:126–149` | Open `interpret` forwards `atol`, enumerates every apex assignment, and accumulates at the output/input indices. `enumerated_table_correct` already proves the exact-arithmetic formula, including copied and passed-through outputs. |

These are inspected source-level correspondences. They are **not** a newly
proved Julia parser/compiler/runtime refinement. The unchanged mathematical
theorems still require exactly normalized local real kernels. Runtime
acceptance of rounded rows within `atol` and retention of their original
entries does not automatically discharge that stronger premise.

The neutral v1 changes concerning DVE, posterior feasibility, belief propagation
and influence-diagram copying are outside this category track's proof ownership.
No claim about those implementations is added here.

## Precise interface still required from Julia

The missing minimal interface is an exporter:

```julia
open_network_certificate(o::OpenBayesNetCospan; ranks = nothing)
```

The complete versioned payload, extraction algorithm, reference encodings,
index/position conventions, regression cases and optional numerical extension
are specified in [EXPORTER-CONTRACT.md](EXPORTER-CONTRACT.md). A concrete JSON
fixture is provided in `certificate-fixtures/mixed.json`, corresponding to the
already accepted Lean `RawCertificate.certificate`.

Essential points:

* dense **0-based variable IDs** derived from part IDs, never names;
* actual **1-based state/input positions**, keeping every repeated input row;
* exact names and all four reference tags/payloads;
* actual attributed feet and both explicit maps, preserving copied outputs;
* all hidden parts and a checked rank for every variable;
* no global name-freshness requirement and no numerical renormalization.

The exporter should return the structural records directly; it need not emit
Lean proof text. A JSON-to-Lean bounded-record reader and a theorem relating
the Julia exporter to its source ACSet remain outer translation work. The
existing finite checker and checked-record-to-category normalization already
provide the Lean mathematical consumer once those records are supplied.

## Validation and freeze linkage

No Lean source or proof conclusion was changed for this correspondence update.
The prior source closure is checked against `DEPENDENCIES.json`; the existing
fail-closed axiom audit is rerun. The JSON fixture is parsed and checked for
the required finite positions, references, legs, rank and hidden/copied cases
as a data-format validation, not as a parser-level proof.

A separate supplement under
`backlog3/project-lean-semantics-implementation-v1/` records this note, exporter
contract, fixture, source anchors, audit output, hashes and links to the
immutable mathematical snapshot. It does not modify
`backlog3/project-lean-semantics/` or any earlier freeze.
