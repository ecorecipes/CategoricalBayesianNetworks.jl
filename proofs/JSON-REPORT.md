# Checked JSON certificate reader: frozen follow-up

**Date:** 2026-09-08.  
**Status:** actual strict JSON reader and `lake exe check_certificate PATH`
implemented, built, audited, exercised, and reproduced from a fresh source
snapshot.

This is an outer-reader follow-up. The previously accepted syntax, stochastic
interpretation, normalization and finite-record checker are unchanged. The
24 mathematical module/dependency source files of the existing core were
checked against their frozen hashes. Only new outer modules/entry point and
the root imports, audit/build/CI, tests and proof-local documents were extended.

## Authority and preserved snapshots

Runtime correspondence continues to use the neutral implementation-v1 source:

```text
backlog3/implementation-v1/SOURCE.json
SHA256 070b9b202f6e703b077b7527d47c1d53cab047fd969608ee733bc1308ccfa5c7
```

The payload protocol is [EXPORTER-CONTRACT.md](EXPORTER-CONTRACT.md), format
`OpenNet.RawCertificate/v1`. No Julia source/tests or parent documentation were
edited. No other-prover results or source were read, and no nested agents were
used. The earlier `project-lean-semantics` and
`project-lean-semantics-implementation-v1` freezes, and older snapshots, remain
unchanged.

## 1. Actual executable and exit behavior

From this proof project:

```sh
lake exe check_certificate certificate-fixtures/mixed.json
```

Successful output:

```text
valid OpenNet.RawCertificate/v1: 3 variables, 2 mechanisms, 1 inputs, 3 outputs
```

`CertificateMain.lean` reads the actual file, invokes
`OpenNet.RawCertificate.JSON.read`, and reports:

* **0:** parsed and accepted by `Network.check`;
* **1:** malformed syntax, bad schema/index/tag, or failed network validation;
* **2:** wrong argument count or file-I/O failure, including invalid UTF-8.

The binary is a real Lake executable and a default build target, not a
description of a future tool or a Python substitute for the Lean checker.
`make check-certificates` invokes both the `lake exe` entry point and the
compiled binary regression matrix. CI runs it after building and auditing.

## 2. Strict syntax and schema

`CertificateSyntax.lean` implements recursive JSON object/array/value parsing
with a fuel parameter initialized from the input character count. It rejects:

* duplicate **decoded** object keys, including escaped spellings of the same key;
* trailing input, trailing commas, invalid tokens and non-JSON whitespace;
* invalid string escapes, unescaped control characters, and unpaired UTF-16
  surrogates.

Valid Unicode strings and surrogate pairs are retained. Standard Lean lexical
primitives handle integer digits and hexadecimal escapes. No project-specific
partial/native proof implementation was introduced.

**Intentional number contract:** numeric fields must use integer JSON tokens.
Fractions and exponent notation are rejected, including integral spellings
such as `1.0` and `3e0`; they are not rounded or coerced. Negative integer
values, booleans and numeric strings cannot become natural-number fields.
The Julia exporter should emit its actual integer values.

`CertificateJSON.lean` requires the exact envelope fields:

```text
format, variableCount, variableData, mechanisms, inputs, outputs
```

It also requires exact key sets on variable, state, mechanism, input, boundary,
attribute and reference records. Missing and unknown fields are rejected.
Reference tags and payloads are precisely `noRef`, `named(id)`,
`pointMass(state)` and `policy(decision)`.

Every pointer is decoded to a natural number, checked to be strictly below
`variableCount`, and only then wrapped as `Fin variableCount`. The declared
count must equal the actual variable-data-array length. Arrays retain order
and multiplicity: the reader does not deduplicate parent or output rows,
discard hidden parts, rename values, fill absent fields, or synthesize ranks.

## 3. The existing checker is called, not assumed

The pipeline is explicitly:

```text
input text
  → strict JSON syntax parser
  → exact record/schema decoder
  → validate N
```

The final function is:

```lean
def validate (N : Network) : Except String Network :=
  if N.check then .ok N else .error ...
```

`N.check` is the existing, unchanged finite decision procedure. It verifies
state/input positions, named states, attributed feet, the input/target
partition, target/input injectivity and supplied acyclic ranks. Zero positions
and other structurally invalid but well-typed records therefore fail at this
stage. The reader does not replace it with an assumed certificate or a second,
unproved success flag.

Successful reading certifies **structural records**. It does not check numeric
CPT entries or assert exact probability normalization of a floating-point
model.

## 4. Proved soundness and value-preservation statements

The principal new Lean statements are:

```text
validate_preserves :
  validate N = .ok M → M = N ∧ N.Valid

read_preserves_decoded :
  read text = .ok N →
  ∃ j, CertificateSyntax.parse text = .ok j ∧
       network j = .ok N ∧ N.Valid

read_sound :
  read text = .ok N → N.Valid
```

The first theorem follows by the actual branch on `Network.check` and its
already-proved `check_sound`. The second examines the actual `Except` pipeline:
syntax and schema failures cannot yield success; the final validator returns
the **same** decoded record. No premise assumes correctness of the entire
reader or checker.

`checkedNet` feeds a successful read to the existing categorical normalization:

```text
checkedNet (h : read text = .ok N) : Net N.dom N.cod
```

Additional round-trip/preservation results are:

* `natural_roundtrip`: decoding a JSON value encoding any natural number
  returns that exact natural number;
* `index_roundtrip`: a bounded natural-number JSON value returns the exact
  corresponding `Fin` index;
* `index_value`: successful bounded decoding has the same natural value as
  the input number decoder;
* `reference_roundtrip`: all four reference constructors, including arbitrary
  string payloads, round-trip through the provided JSON-value encoder/decoder;
* `stateRow_roundtrip`: arbitrary positioned state records preserve both name
  and position through their JSON-value encoder/decoder.

These round trips are at the **JSON-value / record** layer, not a theorem that
every text serializer/parser round-trips. In particular no RFC 8259
formalization, full lexical-parser completeness proof, Julia-exporter
refinement, or compiler/OS-runtime theorem is claimed.

## 5. Positive and negative cases

Persistent positive fixtures are:

* `certificate-fixtures/mixed.json`: copied/pass-through outputs, repeated
  input slots, unordered positions, full references and a hidden generator;
* `certificate-fixtures/empty.json`: zero variables/mechanisms and empty feet;
* `certificate-fixtures/hidden-scalar.json`: a hidden generator with both feet
  empty.

`scripts/test_certificates.py` creates its mutation cases only inside the
project and removes them afterward. The **64 compiled CLI cases** cover:

* valid Unicode/surrogate pairs and all reference tags;
* arbitrary-precision integral ranks;
* malformed/trailing JSON, duplicate/escaped-duplicate keys and invalid whitespace;
* wrong/missing/extra envelope and nested fields;
* incorrect tags, missing/extra payloads and incorrect payload types;
* mismatched counts, fractional/string/boolean/negative counts or indices;
* out-of-range targets, parents and feet, including very large indices;
* fractional/exponent spellings, including a huge exponent rejected before
  any exponent expansion;
* zero, duplicate or gapped input/state positions;
* duplicate state names, empty state lists, invalid/negative ranks;
* corrupted foot references/state order, duplicate inputs/targets and
  uncovered variables;
* missing files/arguments, excess arguments and invalid UTF-8.

Each case checks the actual process exit status and appropriate success/error
diagnostics. Native execution here is executable regression testing; it is
not used as a proof escape such as `native_decide`.

## 6. Builds, audits and fresh reproduction

The established pins remain Lean **4.30.0**, Mathlib **v4.30.0** and mdgen
**v4.30.0**, using the shared package directory and sibling proof dependencies.

All final commands succeeded:

```text
lake build --wfail
Build completed successfully (2215 jobs).

make audit
PASS: 143 declarations; only propext, Classical.choice, Quot.sound
PASS: 24 Lean source files scanned; no proof escape hatches

make check-certificates
PASS: 64 compiled CLI certificate cases (syntax/schema/graph/I/O)

make docs
PDF built with no missing-character warnings.
```

The source scanner now includes `CertificateMain.lean` and handles character
literals without mistaking embedded quotes for string delimiters; a scanner
regression check covers that case. The axiom audit
includes parser/decoder definitions and all new soundness/round-trip headlines,
with `assert_no_sorry` on critical results. The only proof axioms are the
standard `propext`, `Classical.choice`, and `Quot.sound`.

`DEPENDENCIES.json` records the **29-file same-prover source closure**.
A fresh sibling-layout snapshot, containing source/configurations and fixtures
but initially no own/path-dependency build products, rebuilt the executable,
passed the same 143/24 audit, and passed the same 64 CLI cases. Pinned external
Mathlib caches were reused. This verifies source completeness of the frozen
follow-up rather than relying solely on the live executable.

Full logs are under `evidence/json/`, including live and fresh-snapshot build,
audit and CLI tests, environment/binary hash, core-preservation checks, dependency
inventory, documentation and visual-inspection evidence.

## 7. Publication inspection

The regenerated **51-page A4 PDF** includes all **21 library modules** and the
complete CLI entry point. Markdown and standalone HTML are generated from the
same source; HTML has **43 Lean code blocks** with existing local assets.

Parser, decoder, preservation/round-trip, and CLI pages were visually inspected.
Inspection found a character-literal highlighting defect in the prior generic
Lean highlighter. `lean.xml` was corrected so quoted characters no longer put
subsequent parser declarations into string highlighting. The document was
regenerated and the corrected parser page inspected again.

No clipped code or footer overlap was observed on inspected pages. Fonts and
the existing diagrams retain the established embedded STIX / JuliaMono /
Helvetica setup. The final log has zero missing characters, zero overfull
horizontal boxes and zero unresolved LaTeX warnings. It retains ten small
overfull vertical boxes (maximum 3.07228pt) and 48 underfull vertical boxes at
long-code pagination. Not every page was visually inspected; HTML was checked
structurally, not browser-rendered.

## 8. Hashes and immutable follow-up

Selected SHA256 digests:

| Material | SHA256 |
|---|---|
| Full Markdown | `84ae4c8657df59124083c9bee5a554cb2087d637a759f6bf7b338ab8f755a833` |
| Full HTML | `04e13ec0fa04a0859dc810a0deea91414cf9c30e30f476dd9ab87129fef33a46` |
| Full PDF | `35ac1d6bd913a9d07ea1d1c7b308fbf16c4a65cc627d75ae4cad12b10e53774c` |
| Live build | `8d48ce21f342e3d1b271bc7a5a69fe61169b7629ac815338c60f701faeff1d3d` |
| Live/reproduced audit | `af22d74754905867f15db11301bd0a0e155288953bfc1eb0d4d8003446899b18` |
| Live/reproduced CLI tests | `5d6336031e3d139ab6b3f06783964d6f62da0316b473ef04d56e4050a06abdfd` |
| Fresh-snapshot build | `32382bf9cba55ab547669affd047a70772ce7262df752df0e976d7d3b801fd8f` |
| Documentation output | `11b5791e64094d65bcd85465c82afaa1ae267ffc8e3757eedccb35dbcdeff5dc` |
| Dependency inventory | `3cd70c81fc0b9bc6ccdde1a1eff572f98d0725782a8a3530f2d8c1b3e10301c8` |

All live source, configuration, fixture, document and receipt hashes are in
`SHA256SUMS`. The separate new source-complete freeze is:

```text
files/backlog3/project-lean-semantics-json/
```

It includes a root report, source closure in sibling layout, executable source,
fixtures, test driver, build/audit/test evidence, publications, fonts/licence
and material inventories. Build caches and generated binary/object files are
excluded after fresh reproduction. Earlier mathematical/correspondence
snapshots are not modified. No commits or pushes were made.
