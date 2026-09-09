# Ordered open-network certificate interface

`CategoricalBayesianNetworksProofs/RawCertificate.lean` defines the concrete
Lean-side data interface and an executable `Network.check : Bool`.

The record has a finite variable count, variable records, a finite list of
mechanism records, and finite input/output boundary-row lists.

* Variable record: exact name string; tagged `space_ref`; finite state rows
  `(name, position)`; nonnegative integer rank.
* Mechanism record: exact name string; tagged `kernel_ref`; target variable
  index; finite input rows `(variable index, position)`.
* Boundary row: variable index and complete copied attributes: variable name,
  tagged space reference, and ordered state-name list.
* References: `noRef`, `named(id)`, `pointMass(state)`, `policy(decision)`.
* Positions are **1-based**. Zero, duplicates, and gaps are rejected.
* Lean variable indices are `Fin variableCount`, and are therefore 0-based and
  in range. An exporter using Julia's 1-based indices must explicitly subtract
  one and check bounds. This index conversion/parser is not currently verified.

Rows are grouped by owner; the exporter may preserve any original row order.
Lean sorts the actual rows by position. The checker verifies that the result's
positions are exactly `1..rowCount`. State names must be distinct and each
variable must have at least one state. Repeated parent **variables** are allowed
at different input positions and their occurrences are retained.

The checker additionally verifies:

1. targets are injective;
2. inputs are injective and disjoint from generated targets;
3. inputs and targets cover the entire variable set;
4. both legs preserve full boundary attributes;
5. every parent rank is strictly below its target rank.

There is no global name-uniqueness test: this interface represents the total
structural category, not the compatibility name-safe Julia wrapper. Outputs
may repeat variables, pass inputs through, or be empty. Hidden mechanisms and
empty networks are retained.

`check_sound` proves that acceptance constructs a valid `Legged` network.
`normalize` uses the existing input/target-partition equivalence, and
`normalized_representation` proves full attributed ordered-incidence
isomorphism back to that checked legged record. Name/reference preservation,
position profiles, row-occurrence counts and acyclicity are separately stated.
The numerical interpretation then applies to this exact normalized syntax.

This checks supplied finite records. The implemented JSON and bounded-index
reader is described below. It does **not** prove that the Julia exporter,
Catlab's colimit code, or the Julia compiler/runtime produces the right records.
Grouping flat source ACSet rows by owner and translating Julia `Symbol`/`Int`
values remain explicit source-translation boundaries.

## Implemented Lean JSON reader

The outer reader is now implemented in `CertificateSyntax.lean` and
`CertificateJSON.lean`:

```sh
lake exe check_certificate PATH
make check-certificates
```

It requires the exact `OpenNet.RawCertificate/v1` envelope and record keys,
checks nonnegative integer tokens and every variable bound before constructing
`Fin`, validates the four tagged references, retains array order/multiplicity,
and invokes the existing `Network.check`. Duplicate decoded object keys,
trailing input, invalid string escapes and unpaired Unicode surrogates are
rejected. Decimal/exponent number spellings are not part of this v1 reader;
the Julia exporter should emit actual integer fields.

`JSON.read_sound` proves success implies `Network.Valid`.
`read_preserves_decoded` proves successful checking returns the same decoded
record, and `checkedNet` feeds it to categorical normalization.
Primitive integer/index, reference and positioned-state values have round-trip
or preservation lemmas. These do not assert full JSON lexical-parser correctness
or a theorem relating a Julia source ACSet to an exported file.

## Exact local numerical table interface

`LocalTables.lean` supplies a finite `StateTuple` with one coordinate for each
ordered parent occurrence, and an `entry` function taking this parent tuple
first and the child coordinate last. Nonnegativity and one-column-sum conditions
are local table hypotheses. `typed_entry` proves this table is exactly the
local kernel used by the stochastic interpretation, and
`checked_table_normalized` proves the resulting exact output-first
all-apex enumeration is normalized.

The universal attribute signature also contains malformed types with empty
state-name lists. Its canonical table state dimension is `max 1 stateCount`,
solely to give such unused malformed types a harmless total extension.
`dimension_checked` proves this is precisely `stateCount` for every variable
of every accepted certificate. A concrete point-mass family witnesses that
the table interface is inhabited.
