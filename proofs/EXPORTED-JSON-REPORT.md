# Actual Julia-exported certificates: interoperability receipt

The final compiled Lean `check_certificate` executable was run against all
twelve files supplied by the parent under `backlog3/exported-certificates/`.
No Lean or Julia source was changed.

| Julia-produced file | Expected / actual exit |
|---|---|
| `mixed.json` | 0 / 0 |
| `automatic-ranks.json` | 0 / 0 |
| `empty.json` | 0 / 0 |
| `hidden-scalar.json` | 0 / 0 |
| `colliding-scalars.json` | 0 / 0 |
| `renumbered.json` | 0 / 0 |
| `invalid-negative-rank.json` | 1 / 1 |
| `invalid-variable-index.json` | 1 / 1 |
| `invalid-fractional-index.json` | 1 / 1 |
| `invalid-duplicate-position.json` | 1 / 1 |
| `invalid-foot-reference.json` | 1 / 1 |
| `invalid-version.json` | 1 / 1 |

The test checks the exact expected filename set, so missing cases cannot
silently reduce coverage. `evidence/exported-json/results.json` records each
input SHA256, expected/actual status, stdout/stderr, the executable SHA256,
and the SHA256 of the supplied `export-certificate-cases.jl` generator.

The parent reports 33 Julia fixture/contract assertions, including comparison
with the mixed fixture. This follow-up did not rerun those Julia assertions;
it independently exercised the Lean executable on the actual emitted files.

This is concrete exporter/reader interoperability evidence. The existing
`JSON.read_sound` theorem certifies validity of accepted parsed records; the
12-file experiment is not a proof of the Julia exporter, compiler/runtime or
all source translations.

A separate freeze at `backlog3/project-lean-semantics-json-exported/` contains
the emitted files, source generator, executable-result receipt, and a digest
link to the unchanged JSON-reader snapshot. Earlier frozen evidence and all
historical inspection receipts are untouched.
