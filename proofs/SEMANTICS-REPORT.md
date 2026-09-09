# General open-network stochastic semantics: frozen Lean report

**Milestone:** backlog3, 2026-09-08.  
**Status:** genuine general-boundary finite stochastic interpretation completed,
including an actual strong braided monoidal functor into the existing FinStoch
category, copy/discard preservation, and concrete checked-record/local-table bridges.

This report supersedes the numerical-semantics limitations of the historical
structural-only `REPORT.md`. The accepted syntax category, its structural
quotient, its copied/pass-through boundary maps, and its non-Markov hidden
generator distinctions are preserved.

## 1. Authority, independence, and ownership

New common authority:

```text
backlog3/source/SOURCE.json
SHA256 6c08638af13d1d9e4bca65be0ab6bb0e11d152e17c430fcd60a82148e7c8f2d6
```

The digest was independently rechecked. The packet contains the verbatim SPEC
body and current Julia source, without prior-prover revision-method summaries.
Relevant source anchors are:

* `SPEC-body.md`, §§5–6, 10, 13, 55.5, 61–62: finite stochastic kernels, general
  open-network interpretation, composition, tensor and copy/discard.
* `CategoricalBayesianNetworks.jl/src/evaluation.jl`, `interpret`: enumerate
  apex assignments, multiply mechanism factors, accumulate into
  `(outputs..., inputs...)` axes. Repeated output indices and pass-through
  input indices remain explicit.
* `open.jl`, `_leg_mismatches` and `_check_interface_rules!`: attributed feet,
  injective inputs, no generated inputs, complete exogenous coverage.
* `composition.jl`: structural pushout/tensor and the additional name-safe
  wrapper policies.
* `wiring.jl`: ordered input occurrences, copied/pass-through outputs and
  hidden mechanisms.
* `BayesianNetworks.jl/src/schemas.jl`, `validation.jl`, `refs.jl`: ordered
  `State`/`Input` records and the four tagged reference constructors.
* `FiniteKernels.jl/src/kernels.jl`, `composition.jl`, `copy_discard.jl`:
  output-first kernel storage and finite matrix/product operations.

Only the live CategoricalBayesianNetworks proof tree and its proof-only CI
workflow were changed. FiniteKernels proof source and all BayesianNetworks /
InfluenceDiagrams proof source were left unchanged. No Julia source/tests,
package README/CLAUDE/manual pages, workspace documents, schema JSON, old freeze,
or old source packet were modified. No commits or pushes were made.

No other-prover source or report was read. Same-prover reuse was limited to the
accepted syntax baseline and the five imported Lean source files pinned in
`DEPENDENCIES.json`. This is shared-host procedural isolation, not an OS sandbox.

## 2. Exact interpretation data and state spaces

For an arbitrary accepted `Signature S`, `Interpretation S` contains:

```text
states : S.Ty → Type
finite : ∀ t, Fintype (states t)
weight : S.Label → List (Sigma states) → Sigma states → ℝ
nonneg : ∀ l p s, 0 ≤ weight l p s
normalized :
  ∀ l p, p.map Sigma.fst = S.inputs l →
  ∑ s : states (S.result l), weight l p ⟨S.result l, s⟩ = 1.
```

These are ordinary **local** kernel assumptions, not normalization of an
entire network, a chosen functor, or correctness of a compiler/evaluator.
Ill-typed total rows are irrelevant to evaluation; the concrete local-table
adapter extends them by zero.

Signature-state types may be empty. There is **no** global `Nonempty` hypothesis.
An assignment on an interface with an empty state coordinate is simply
uninhabited, as appropriate for an empty FinStoch object.

`Assignment I σ` is a function assigning each finite index a tagged value,
with proof that its tag is `σ index`. `Assignment.piEquiv` proves equivalence
with the dependent finite tuple `∀ i, I.states (σ i)`. The sum-splitting and
renumbering equivalences are explicit; they preserve state values literally
and do not choose unrelated bijections between state spaces.

## 3. The actual numerical definition

For `f : Net X Y`, input assignment `x`, and generator assignment `z`, write
`v = join x z` for the complete valuation on `X.Port ⊕ f.Gen`. The definitions are:

```text
parents f x z a = map v (f.parents a)

joint f x z =
  ∏ a, weight (f.label a) (parents f x z a) (z a)

read f x z = v ∘ f.output

kernel f x y =
  ∑ z, if y = read f x z then joint f x z else 0.
```

Thus each ordered parent occurrence is read, including repetitions. Every
generator contributes a local factor, whether or not it reaches an output.
The arbitrary output map controls the final pushforward; no injectivity,
input/output disjointness, or output-reachability premise is added.

The morphism map is this expression itself, followed only by quotient descent
and its proved stochasticity. It is not defined as a map of a previously chosen
semantic functor, and is never quotiented by equality of numerical kernels.

## 4. Normalization, including empty signature-state types

`generated_nonempty f x a` proves inhabitance of the state space of each
instantiated generator for a **given input assignment** `x`.

The proof is induction on the existing acyclic generator rank. Input parents
obtain values from `x`; generated parents obtain values by induction. These
values form a correctly typed ordered parent row. If the current generator
state space were empty, that row's normalized finite sum would be zero and
one simultaneously. This derives the inhabitance needed by the existing
finite-DAG normalization theorem rather than importing it as an extra
signature assumption.

`internalBN` is then the closed internal-generator graph with target `id`.
`internalKernel` uses the actual ordered parent list and fixes `x`. Only the
dependency predicate is converted to a set, for locality/order reasoning;
the numerical kernel does **not** deduplicate the input slots.

`internalOrder` sorts generators by rank and proves completeness, noduplication,
parent-before-child and absence of self-dependence. `internal_local` and
`internal_normalized` prove the precise hypotheses of the imported
`FinBayesNet.sum_joint_eq_one`. Consequently:

```text
joint_normalized f x : ∑ z, joint f x z = 1
kernel_normalized f  : ∀ x, ∑ y, kernel f x y = 1
kernel_stochastic f  : Kernel.Nonneg (kernel f) ∧ Kernel.Normalised (kernel f).
```

Nonnegativity is proved directly from the finite products and sums.

## 5. General-boundary laws and the actual Mathlib functor

All following laws quantify over arbitrary signatures, interpretations, valid
finite syntax, and matching typed feet. Their only probabilistic premises are
the local interpretation data above.

| Declaration | Exact mathematical content / proof |
|---|---|
| `joint_iso`, `read_iso`, `kernel_iso` | Structural generator renumbering induces a bijection on assignments. Ordered lists, labels and output values are preserved; finite products and sums are reindexed. |
| `joint_comp` | On paired generator assignments, the composite joint equals `joint f x a * joint g (read f x a) b`. |
| `read_comp` | Reading the glued network equals reading `g` with `f`'s actual output assignment as its input. |
| `kernel_comp` | `kernel (f.comp g) = Kernel.comp (kernel f) (kernel g)`; finite Fubini and the intermediate-output equality indicator collapse the boundary sum. |
| `kernel_wire` | A generator-free arbitrary boundary map is precisely its deterministic assignment-reindexing kernel. |
| `joint_tensor`, `read_tensor`, `kernel_tensor` | Under canonical sum/pair assignment equivalences, tensor is exactly the independent product of the two numerical kernels. |
| `functor` | Actual `Interface S ⥤ FiniteKernelsProofs.FinStoch`, with object map the finite typed assignment space and morphism map the explicit kernel above. |
| `monoidalCore`, `monoidalFunctor` | Actual strong monoidal structure. Unit and tensor comparisons are deterministic assignment bijections. Naturality uses numerical tensor factorization; associativity and unit coherence are checked on actual functions. |
| `braidedFunctor` | Actual `Functor.Braided` instance, with preservation of the symmetry under those tensor comparisons. |
| `map_copy` | `F.map (copy X) = Δ[F X] ≫ μ[X,X]`. |
| `map_discard` | `F.map (discard X) = ε[F X] ≫ εIso.hom`. |
| `semantic_discard` | `F.map (f ≫ discard Y) = F.map (discard X)`, derived in FinStoch from normalized semantics. |

The target is the existing finite-kernel FinStoch category, whose real kernel
entry is `P(y | x)` and whose tensor is Cartesian product of finite state
types. It is not a new category containing assumed “semantic kernels.”

The raw syntax still has its meaningful generator-count invariant. In
particular the pre-existing `Examples.discard_not_natural` and
`hidden_scalar_not_identity` remain true and audited. No `MarkovCategory`
instance was added to raw syntax. Semantic erasure is a theorem about this
nonfaithful normalized interpretation, not a weakening of syntax equality.

## 6. Exact output-first reference-table bridge

`enumeratedTable f y x` is independently stated as:

```text
∑ complete apex valuation v,
  if apexInput v = x ∧ apexOutput v = y
  then ∏ generator a, weight label[a] (map v parents[a]) v[target[a]]
  else 0.
```

Its arguments are explicitly output first, input last. The theorem
`enumerated_table_correct` proves it equals `kernel f x y` by splitting the
complete assignment into input and generator assignments and eliminating the
input-equality indicator. `enumerated_table_normalized` proves its column sums.

`copied_output_zero` proves zero mass whenever two output positions select the
same apex variable but the requested output values differ.
`pass_through_zero` proves zero mass when an output selecting an input requests
a different value. These are general support theorems, not just examples.

This is a theorem about the exact finite Cartesian-index enumeration formula.
It does not verify Julia loops, memory layout, floating-point reductions,
compiler code generation, or a particular array object.

## 7. Concrete ordered-record and local-table bridge

The data interface is documented in [CERTIFICATE.md](CERTIFICATE.md).
`RawCertificate.Network` carries finite bounded variable IDs; finite mechanism,
input-foot and output-foot lists; grouped finite state/input rows; exact
names and tagged references; and a natural-number variable rank.

`orderRows` is an actual insertion sort on position, and `orderRows_perm`
proves that it retains all rows. `Network.check` is an executable finite
decision procedure checking:

1. sorted state positions are exactly `1..stateCount`, state names are distinct,
   and state lists are nonempty;
2. sorted input positions are exactly `1..inputRowCount`;
3. target and input injectivity, disjointness, and complete variable coverage;
4. both feet preserve full names, space references and ordered state profiles;
5. every parent has strictly smaller rank than its target.

There is no global unique-name policy, and no output-injectivity test. Repeated
parent variables remain separate positioned rows; `row_occurrences` proves
the original input-row count is retained.

`check_iff` and `check_sound` connect the Boolean result to the exact predicate.
`toLegged` constructs a valid general-legged network from acceptance.
`normalize` invokes the accepted input/target-partition normalization.
`normalized_representation` gives the full attributed ordered-incidence
isomorphism back to the checked legged record. State/input positions,
variable references, mechanism names/references and acyclicity have explicit
audited declarations.

`LocalTables` provides parent-first, child-last finite CPT functions. The
parent `StateTuple` has one finite coordinate per **ordered occurrence**.
`typed_entry` proves the table entry is exactly the local kernel evaluated by
the general interpretation. Local table nonnegativity and normalization are
the only numeric premises; `checked_table_normalized` proves the final exact
table's column sums.

**Explicit total extension:** the universal raw signature also includes
malformed attribute profiles with an empty state-name list. For those unused
profiles, canonical table dimension is `max 1 stateCount`. Accepted records
require nonempty states, and `dimension_checked` proves this is exactly the
declared count for every accepted variable. A concrete point-mass family
`LocalTables.point` / `tables_nonvacuous` shows the global table interface is
inhabited. This extension is separate from—and does not restrict—the general
interpretation's arbitrary finite, possibly empty, state types.

## 8. Genuine nonvacuous examples

`SemanticExamples.booleanModel` assigns two states to the signature type.
Nullary generators have probabilities **1/3 and 2/3**. Other generators compute
parity of their ordered parent-value occurrences.

On the existing mixed syntax, the visible mechanism reads the input twice,
so parity is false. There is also the independent hidden stochastic generator,
and three outputs: the input itself, the visible output, and its copy.
The exact theorem is:

```text
mixed_kernel x a b c :
  K_mixed(input x, output a b c) =
  if a = x ∧ b = false ∧ c = false then 1 else 0.
```

Additional audited results prove:

* inconsistent copies and an altered pass-through value have probability zero;
* the permitted visible output has probability one;
* the two hidden assignments contribute exactly 1/3 and 2/3;
* discarded mixed syntax has the same semantic arrow as input discard;
* the one-generator hidden scalar with both feet empty has kernel entry one.

The raw-record example has unordered two-state rows, unordered repeated input
rows, nontrivial space/kernel references, copied outputs, pass-through, and a
hidden mechanism. Lean's kernel-reduced `decide` accepts it and rejects
duplicate positions, invalid ranks, and corrupted output-foot references.
No native-decision escape was used.

## 9. Precise remaining boundaries

The mathematical numerical-semantics target is complete. Remaining
implementation-facing boundaries are explicit:

* A Julia/JSON parser/exporter is not verified. Raw Lean pointers are
  `Fin variableCount`; converting Julia's 1-based integer IDs and checking
  ranges is an outer translation step. Grouping flat ACSet rows by owner,
  translating `Symbol`/`Int`, and serializing the four reference tags also
  remain outside the theorem.
* The certificate checker verifies a **supplied** rank. It does not prove that
  Julia's cycle detector/topological-sort implementation produces that rank.
* No theorem identifies Julia's generated free expression with the checked
  record's syntax. The record normalization, exact enumeration formula, and
  finite local-table adapter are concrete mathematical algorithms instead.
* Floating-point approximation, `DEFAULT_ATOL`, array memory operations,
  maximum-state resource limits, errors/exceptions and compiler/runtime
  behavior are not covered by exact real arithmetic.
* The frozen source's compatibility name-safe wrapper is partial even when
  interfaces match. A total structural wrapper being implemented separately
  is compatible with this category's meaning, but its Julia implementation is
  not certified here.
* The five other imported same-prover proof files are trusted only through
  their kernel-checked proof terms and recorded hashes. No other backlog
  target—DVE, junction trees, evidence conditioning or d-separation—is claimed
  as work of this track.

## 10. Builds, axiom audit, and source-complete reproduction

Pins: Lean **4.30.0**; Mathlib **v4.30.0**
`c5ea00351c28e24afc9f0f84379aa41082b1188f`; mdgen **v4.30.0**
`8a448a570399ae674d0b0031d8c912c17665bea3`. The Lake manifest retains
`../../.lake-packages` and adds sibling path dependencies on the existing FK
and BN proof projects. The proof CI workflow now checks those siblings out.

Final live validation, all exit status zero:

```text
lake build --wfail
Build completed successfully (1117 jobs).

make audit
PASS: 131 declarations; only propext, Classical.choice, Quot.sound
PASS: 21 Lean source files scanned; no proof escape hatches

make docs
PDF built with no missing-character warnings.
```

`Audit.lean` contains the old syntax headlines and all new semantic/checker
headlines, including `assert_no_sorry` on the critical instances, normalization,
composition, enumeration and certificate results. The fail-closed audit checks
coverage and the standard axiom whitelist. Its lexical scan strips nested
comments/strings and rejects admissions, new axioms, native evaluation escapes,
`unsafe`, external implementations, and `#eval`.

`DEPENDENCIES.json` pins the exact transitive **26-file same-prover source
closure**: 21 files in this project, BN `Finite/BayesNet` and `Finite/Evaluation`,
and FK `Finite/Kernel`, `Finite/Laws`, `Theory/FinStoch`, plus external Git pins.
All 26 hashes were rechecked after validation.

A fresh sibling-layout snapshot containing just this exact source closure and
the package configurations was then built and audited successfully. This
reproduction used the pinned shared Mathlib cache, but no preexisting own-project
or path-dependency `.olean` files. It again reported **1117 build jobs** and the
same **131 / 21** audit results. Thus the snapshot is source-complete for this
library, not just a collection of binary build products.

Complete outputs are under [evidence/backlog3/](evidence/backlog3/), including
live build/audit/docs, independent snapshot build/audit, environment,
publication, dependency inventory and inspection records.

## 11. Publication and material inspection

mdgen generated Markdown containing all **19 modules' full source and prose**;
pandoc generated standalone HTML and a **45-page A4 PDF**. The original
structural diagram and a new exact-probability diagram are generated from
committed DOT into SVG and vector PDF.

Visual inspection covered PDF pages **1, 30, 31, 35, 42 and 45**, including
rank/normalization, braided monoidal and copy/discard proofs, the numerical
diagram, and final certificate checks; the standalone stochastic diagram was
also viewed. No clipped code or footer overlap was observed on these pages.
Not every PDF page was visually inspected.

All fonts in the PDF are embedded. Prose is STIX Two Text, code is JuliaMono,
and diagrams use Helvetica. `FONT-HASHES.json` records the four workspace
JuliaMono files and the STIX TeX font files. Diagram PDFs themselves pin the
embedded diagram-font result.

Final diagnostics: **zero missing characters**, **zero overfull horizontal
boxes**, **zero unresolved LaTeX warnings**. There remain **seven small
overfull vertical boxes**, at most **3.07228pt**, and **42 underfull vertical
boxes** at long-code page breaks. These are disclosed rather than suppressed.

HTML has **38 Lean code blocks** and existing local CSS/SVG references.
It was structurally checked, not browser-rendered. Full PDF text was checked
for the core normalization/functor/enumeration results and final checker
declarations.

## 12. Digests and new freeze

Selected final SHA256 values:

| Material | SHA256 |
|---|---|
| Full Markdown | `ab82249a9de4ff767a086161e22fdd6e4cd38f99e36eb6dda703a4339c4100f9` |
| Full HTML | `5270696ef5d00b632f05f3e342c2614d2c857dabd90250788897beb56c30aabf` |
| Full 45-page PDF | `cd5d96f3d8ffe6f3add52cccdf0018f82721c454bd5182add5519a74762b07d4` |
| Live build output | `a67ca4040222056b22ed6454ada9f02cacd9952bbd430322a10304b5918fdac1` |
| Live and reproduced audit output | `ec06f12504ce02363a15e847b31bdf3aeb1fef11fbd0495073317fa4007bb946` |
| Documentation output | `564d69e6a0e601c7b30e7a384f3cefe66995926f761bc82dcafc818874648cef` |
| Fresh source-snapshot build | `bae54980f2975710235e8f84e8698feff6317bd694f0a4dd4b080a3d0fc7fa2c` |
| Same-prover dependency inventory | `4da5b353f9bc9df3e67586757648d56e15d2ccc0cd4d553617ef86c624879c28` |
| Font inventory | `f0e7caf2714b8e03ad6d9da93361c2218e8f81b02a320987ec4514ae2b427270` |

The complete live material inventory is `SHA256SUMS`. The new frozen snapshot,
root `REPORT.md`, exact same-prover source closure, configurations, diagrams,
documents, receipts, font files/licence, `SHA256SUMS` and `FREEZE.json` live at:

```text
<authoring-session-state>/
  files/backlog3/project-lean-semantics/
```

Old `project-lean*` and `proof2/*` freezes remain immutable. The new snapshot
does not include dependency caches or generated `.olean` files; external
dependencies are pinned in the manifests and source inventory. There are no
admitted claims or undisclosed project axioms.
