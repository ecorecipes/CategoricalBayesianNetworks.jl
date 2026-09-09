# Complete raw cospan certificates

[`export_open_certificate`](@ref) and
[`export_open_operation_certificate`](@ref) capture the full structural
`ecorecipes.open-network-certificate` version `1.0.0` profile. This is
different from the smaller, zero-based `OpenNet.RawCertificate/v1` record
produced by [`open_network_certificate`](@ref).

The raw profile records all four apex sorts, both complete feet, and actual
Variable/State leg components. An operation certificate also records its
arguments A and B, the **actual result C**, and both actual cocone maps on
Variable, State, Mechanism and Input.

```julia
using CategoricalBayesianNetworks

A = Open(bayesnet(:X => [:low, :high]); outputs=[:X])
B = Open(bayesnet(:X => [:low, :high], :Y => [:off, :on];
                  mechanisms=[:Y => :X], closed=false);
         inputs=[:X], outputs=[:Y])

network = export_open_certificate(B)
operation = export_open_operation_certificate(:compose_structural, A, B)
operation.kind                     # "compose_structural"
operation.cocone.B.Variable         # source B part IDs index this array
tensor = export_open_operation_certificate(:otimes, A, B)
```

The result is JSON-compatible data. Use a JSON writer from the application's
environment to persist it; for example, with JSON3 available:

```julia
using JSON3
open("operation.json", "w") do io
    JSON3.write(io, operation)
end
```

No proof assistant or external Bayesian-network engine is loaded by these
Julia APIs.

## IDs, rows, feet and maps

All IDs and positions in this format are **one-based JSON integers**.
Each raw sort is emitted in original part-ID order and its row IDs are exactly
`1:length(rows)`. Sparse IDs are rejected, not silently compacted. State and
input rows are not sorted for export: their original `state_position` and
`input_position` attributes determine their semantic order.

| Record | Fields |
|---|---|
| Variable | `id`, `variable_name`, `space_ref` |
| State | `id`, `state_variable`, `state_name`, `state_position` |
| Mechanism | `id`, `target`, `mechanism_name`, `kernel_ref` |
| Input | `id`, `input_mechanism`, `input_variable`, `input_position` |

Each foot has its own Variable/State tables and its actual maps into the apex.
Duplicate variable/mechanism names, repeated input slots, copied outputs,
pass-through, empty feet and disconnected hidden material are retained.
This profile requires at least one state per variable, even though the general
mathematical category has a broader attribute universe.

The four reference constructors use the existing tagged serialization:
`NoRef`, `NamedRef` with `id`, `PointMassRef` with `state`, and `PolicyRef`
with `decision`, all under the `"type"` key. They are structural attributes
here: a generating `NoRef` is permitted, references are not resolved to
numerical tables, and no stochasticity is asserted.

For an operation, `cocone.A.S[i]` is the image in C of A's part `i` of sort S,
and likewise for B. These maps come from the same colimit computation as C;
the producer does not recompute a second result or infer maps from names.
Composition matches middle-foot states by foot-variable position and
`state_position`, not by raw State IDs. Its original outer feet remain intact.
If A repeats an output, B's distinct input variables and their states can
have the same image, so **B's Variable/State maps need not be injective**.
Mechanisms and ordered input slots remain distinct material.

## An explicit local signature relation

The default `signature=nothing` is serialized visibly as
`{"kind":"unrestricted"}`. This means unrestricted structural local typing,
not a hidden inference of an intended generator library.

Pass a vector of complete triples for a finite relation:

```julia
x = (variable_name=:X, space_ref=NoRef(), states=[:low, :high])
y = (variable_name=:Y, space_ref=NoRef(), states=[:off, :on])
allowed = [(label=(mechanism_name=:Y_mechanism, kernel_ref=NoRef()),
            inputs=[x], output=y)]
typed = export_open_certificate(B; signature=allowed)
```

Each entry admits exactly its label, ordered input attributes and output
attribute. Several entries may have the **same label with different signatures**;
identical entries may also repeat. This is not a label-keyed dictionary.
An empty relation permits generator-free networks only.

Records can be NamedTuples or dictionaries with exactly the documented fields.
Names may be strings or Symbols; references may be `KernelRef` values or their
exact tagged JSON objects. No arbitrary executable predicate is serialized.
Every mechanism in every exported network, including the result C, must match
an admitted complete triple.

## Resource and text profile

The [versioned JSON Schema](open-network-certificate-v1.schema.json) describes
the structural data shape. The producer enforces its finite resource limits:
256 parts per sort, 256 entries per map/input/state list, 512 signature entries,
and 1 MiB of compact JSON3 output. A writer that adds extra whitespace may exceed
the consumer's file-size limit even when the compact form fits.

Names and reference payloads contain 1-128 Unicode scalar values; descriptions
allow 1-2048. C0/C1 controls, DEL, unpaired surrogates and invalid UTF-8 are
rejected. There is no Unicode normalization, case folding, renaming or
renormalization. Strings that look similar but have different scalar sequences
remain different. The generated shape has bounded nesting and emits neither
nulls nor boolean/nonnumeric substitutes for IDs.

`OpenCertificateError` identifies a profile error and its record path.
It is defined in BayesianNetworks' shared exception hierarchy.
The ordinary structural exceptions are retained for invalid networks.
Inputs are copied for capture; do not mutate them or the signature during
capture. Returned arrays do not alias the source.

## Metadata and trust boundary

Metadata has `producer`, `producer_version`, `description`, and
`comparison_authority`. The default digest
`070b9b202f6e703b077b7527d47c1d53cab047fd969608ee733bc1308ccfa5c7`
identifies the frozen implementation-v1 **comparison packet**, not the
currently installed Julia source. The explicit role is `"comparison-only"`.
Producer/version text is descriptive, not attestation. A different
`comparison_manifest_sha256` can be supplied explicitly, but the reference
consumer's default comparison policy will reject a different digest.

The independent HOL4 contract workspace supplies `scripts/consume.py` and
`scripts/emit_hol.py`. Its reference consumer checks four-sort incidence,
attribute preservation, exact quotient fibres, material coverage and boundary
squares. Reference acceptance is not a HOL theorem.

In a writable copy of that workspace:

```sh
python3 -B scripts/consume.py operation.json
python3 -B scripts/emit_hol.py --theory E4Operation \
  --output theories/E4OperationScript.sml \
  --receipt logs/operation-emission.json operation.json
```

Emitting a proof attempt is not the same as proving it: build the new theory
and include it in the kernel/tag audit. Actual Julia network, composition and
tensor exports have been checked this way, including noninjective right maps
and deliberately corrupted maps/labels.

The current general bridge proves that finite raw checks imply a valid
decoded typed network. The general implication from every valid raw
four-sort cocone to equality with the quotient composition/tensor is still
an unproved adapter lemma; the checked examples prove their own concrete
operation equalities. Neither those instances nor the producer verifies
Python/Julia execution, arbitrary JSON transcription, or numerical semantics.
