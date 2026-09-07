# CategoricalBayesianNetworks.jl

Open Bayesian networks as structured cospans: composition, wiring diagrams, free Markov-category semantics, and interoperation with CatColab.

## Place in the ecosystem

Dependency order (arrows = depends on):
EcologicalBayesianNetworks → InfluenceDiagrams → BayesianNetworkInference → BayesianNetworks → FiniteKernels,
and BayesianNetworks → BayesianNetworkFormats (both Catlab-free).
This package sits beside `BayesianNetworks.jl` rather than under it: it depends on
BayesianNetworks, MarkovCategories, FiniteKernels and BayesianNetworkFormats, and nothing
depends on it. It is the only place in the model layer that uses Catlab (ADR 0009).
Sibling packages are expected at `../<Name>.jl` (see `[sources]` in Project.toml).

Every name of `BayesianNetworks` is re-exported (a loop over `names(BayesianNetworks)` in
the module), so `using CategoricalBayesianNetworks` is a superset of
`using BayesianNetworks`. Three names are exported by both Catlab and BayesianNetworks and
must stay explicitly imported from BayesianNetworks or the re-export becomes ambiguous:
`validate` and `to_graphviz` (methods are added to both here) and `is_isomorphic` (neither
defined nor extended, imported by name for this reason alone).

## Invariants that must not be broken

- Structural syntax (ACSets) and numerical semantics (kernels, utilities) stay separate; CPT arrays are never ACSet attributes.
- Parent / input order is explicit (`input_position`) and total. Never rely on part-id order.
- Axis conventions: user-facing CPTs are `(parents..., child)` normalised over the last axis; FinStoch kernels internally are outputs-first. Convert with the documented `permutedims`, never by hand.
- Observation (`observe`) and intervention (`do_intervention`) are different operations and stay different.
- Every optimised path is checked against a slower oracle (`joint_distribution`) on small models.
  In particular `categorical_joint` must stay an independent implementation -- the free
  expression built from the syntax and evaluated by MarkovCategories' `functor` -- and must
  never be short-cut to `BayesianNetworks.joint_distribution`. `to_free_expression` builds
  that expression by handing the closed model's wiring diagram to `wiring_expression`: one
  algorithm, two entry points, and neither may be short-cut either.
- The typed-interface rule is what makes every colimit here safe. Nothing may construct an
  `OpenBayesNet` that bypasses `validate` except deliberately, via `Open(...; validate = false)`,
  and `substitute` refuses such a network on entry.

## Commands

```sh
julia --project -e 'using Pkg; Pkg.instantiate(); Pkg.test()'   # the test suite
julia --project=docs docs/make.jl                                 # build docs locally
cd vignettes && quarto render                                     # render vignettes to html/gfm/pdf (julia engine; PDF needs lualatex + ../fonts/JuliaMono)
julia scripts/sync_vignettes.jl [--check]                         # copy vignettes into docs/src/tutorials
```

## Layout

- `src/CategoricalBayesianNetworks.jl`: the module; the Catlab imports, the re-export of
  every `BayesianNetworks` name, and the `using BayesianNetworks: ...` list of that
  package's internals this one builds on (`_factors`, `_product`, `_joint_atol`,
  `DEFAULT_MAX_STATES`, `_closed_semantics`, `_complete_spaces`, `_state_table`,
  `_in_range`, `_variable_id`, `_mechanism_id`, `_mechanism_spaces`, `_with`). Those are
  not `BayesianNetworks`' public interface; this package is their only consumer, and a
  change on either side has to be made on both.
- `src/open.jl`: `OpenBayesNet` / `OpenBayesNetOb` from `OpenACSetTypes(BayesNetUntyped,
  VariableSpaceUntyped)`, `Open(bn; inputs, outputs)`, accessors, the typed-interface rule
  (`validate(::OpenBayesNet)`, `InterfaceError`), and the `munit` override.
- `src/composition.jl`: `compose` (strict, `InterfaceMismatchError`), `glue(A, B; along)`,
  `otimes`, `oapply` (UWDs; `validate_composition` afterwards) and `substitute`. `compose`
  and `glue` validate the composite with `unique_names = true` when both pieces were
  uniquely named (`_validate_composite`), and `glue` refuses a rename whose target name is
  taken in `apex(B)` (`NameClashError`); `substitute` validates the replacement `N`,
  refuses hidden variables and mechanisms whose names are taken in `bn` (`NameClashError`),
  and relies on rule 3 of the typed-interface rule to keep the containing network's
  interface unchanged. `oapply` rejects an outer port on a junction no box touches
  (`InterfaceMismatchError(:missing_junction, ...)`) before Catlab's colimit runs.
- `src/rename.jl`: `rename_variable` for an open network (the feet follow the apex). The
  methods for a network and for a model are in `BayesianNetworks`' `src/semantics.jl`.
- `src/wiring.jl`: `VariablePort`, `MechanismBox`, `BayesWiringDiagram`
  (`WiringDiagram{ThMarkovCategory.Meta.T, VariablePort, Nothing, MechanismBox}`),
  `to_wiring_diagram`, `from_wiring_diagram` (round-trip subset, `WiringDiagramError`),
  `to_hom_expr(FreeMarkovCategory, d)` (Catlab's algorithm on a `Symbol`-valued copy) and
  `wiring_expression` (direct builder, also for boxes whose outputs are all discarded).
- `src/evaluation.jl`: `to_free_expression` / `free_generators` / `categorical_joint`
  (Proposition 1) and `interpret` (open-network semantics, Propositions 2-3). The factor
  machinery they share with the brute-force evaluators is `BayesianNetworks`'.
- `src/graphics.jl`: `box_label` / `wire_label` for Catlab's renderer, and the
  `to_graphviz` methods for an open network (delegating to `BayesianNetworks`' network
  method with the interface filled in) and for a wiring diagram (Catlab's renderer,
  reached by the fully qualified `Catlab.Graphics.to_graphviz` because this package's
  `to_graphviz` is `BayesianNetworks`').
- `test/runtests.jl`: one `@testset` per source file, plus the split-off halves of
  `BayesianNetworks`' `test_semantics.jl`, `test_causal.jl`, `test_properties.jl`,
  `test_formats_bridge.jl` and `test_dynamic.jl`. `test_open.jl` defines `abiotic_bn`,
  `biotic_bn`, `abiotic_open` and `biotic_open`, which the later files reuse;
  `test_properties.jl` defines `random_model`.
- `vignettes/01_wiring_diagrams_and_evaluation`, `vignettes/02_open_networks_and_composition`:
  the two vignettes, moved here from `BayesianNetworks.jl` (rendered outputs are committed).

## Files not to edit by hand

- `docs/src/tutorials/` is generated by `scripts/sync_vignettes.jl`.
- `vignettes/*/*.md`, `*.html`, `*.pdf` and `*_files/` are quarto output; edit the `.qmd`.
- `docs/adr/` is copied from the workspace `docs/adr/` by `scripts/sync_adrs.jl`; edit the workspace copy.
- `proofs/schemas/*.json` (where present) is emitted by the Lean project; edit the Lean source.

## Style

JuliaFormatter `yas`; docstrings on every exported name; typed exceptions with variable names in the message;
no emojis in code or docs.

Exceptions thrown here are `BayesianNetworks`' (`InterfaceError`, `InterfaceMismatchError`,
`NameClashError`, `WiringDiagramError`, ...). The whole `BayesNetError` hierarchy stays in
`BayesianNetworks/src/errors.jl` even where only this package throws a given type: they are
plain structs sharing one root, and splitting the hierarchy across two packages would be
worse than importing them.

## How Catlab is used

- Legs are built in R-form with `OpenACSetLeg(foot; Variable=..., State=...)`; Catlab converts
  them to L-form (domain `L(foot)`, a `BayesNet` without mechanisms), which its pushout-based
  `compose` needs. Never pass a `VariableSpace -> BayesNet` transformation as a leg.
- `compose` / `otimes` for our type are validating wrappers that reach Catlab's methods with
  `invoke(f, Tuple{StructuredCospan{L},StructuredCospan{L}} where {L}, A, B)`; `oapply` reaches
  Catlab's structured-multicospan method through its three-argument form.
- Own pushouts use `pushout[infer_acset_cat(bn)](f, g)` (explicit-category style) with
  `ACSetTransformation((Variable=..., State=...), L(S), bn)`; missing components are filled in.
- A pushout throws ("Not all equal") when merged parts disagree on an attribute, so interfaces are
  compared (names, states with positions, `space_ref`) before every colimit; `glue` renames B's
  glued variables to A's names first. Colimits renumber parts but never reorder states or inputs
  (orders are attributes); results are re-wrapped with freshly built feet and validated.
- `dom` / `codom` stay Catlab's (they return `OpenBayesNetOb`); `input_space` / `output_space`
  return the `VariableSpace`s. Do not override them or Catlab's `compose` breaks.
- Catlab's `copy(::WiringDiagram)` and its expression algorithms go through the untyped
  `WiringDiagram{Any,...}` constructor, so `to_hom_expr` is run on `_symbolic(d)` (an
  `Any`-valued diagram with `Symbol` labels) and `Base.copy` is defined for
  `BayesWiringDiagram`. Catlab's `substitute` keeps the concrete type, so it works directly.
- Catlab's `to_hom_expr` handles fan-out and copied or passed-through outputs, but asserts
  when a box has no path to an outer output (every output discarded); `to_hom_expr` checks
  this (`_all_boxes_reach_outputs`) and falls back to `wiring_expression`.
- Catlab's `CatlabGraphvizExt` runs the Graphviz_jll binaries by bare path, which loses the
  library search path on macOS. `BayesianNetworks.__init__` exports that path to the process,
  which is what makes the wiring-diagram renderer work here.
