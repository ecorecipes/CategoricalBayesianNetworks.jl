# Non-vacuous recursive source-audit hardening

This small follow-up changes only the audit driver, its regression tests,
the audit target, ignore rules and proof-local documentation/evidence.
No Lean source, mathematical statement, JSON reader, executable logic or
previously frozen evidence is changed.

The source audit now:

* requires `Audit.lean`, the library root, and `CertificateMain.lean`;
* scans every root `*.lean` file, including any added root parser/helper;
* recursively scans `CategoricalBayesianNetworksProofs/**/*.lean`;
* rejects an empty expected `#print axioms` inventory before comparing it with
  the observed declarations.

`scripts/test_audit.py` adds eight **synthetic driver tests**: a valid control,
empty inventory, missing audit output, disallowed axiom, forbidden nested
module, forbidden extra root module, forbidden executable entry point, and
missing executable entry point. These test the audit guards, not mathematical
claims. Their files are created only in a project-local directory and removed.
`make audit`, already used by CI, runs these regressions automatically.

Validation:

```text
PASS: 143 declarations; only propext, Classical.choice, Quot.sound
PASS: 24 Lean source files scanned; no proof escape hatches
PASS: 8 synthetic audit-driver guard cases
```

The prior successful mathematical audits had explicit nonempty inventories;
this closes a future vacuous-acceptance possibility rather than changing any
previous proof result. The historical 24-page receipt at
`evidence/inspection.txt`, the 45-page receipt under `evidence/backlog3`, the
51-page JSON follow-up receipts, and their frozen snapshots are untouched.
The new log is `evidence/audit-hardening/audit.txt`.

This follow-up is frozen separately under
`backlog3/project-lean-semantics-json-audit-hardening/`, linked by digest to
the unchanged JSON-reader snapshot. No commits or pushes were made.
