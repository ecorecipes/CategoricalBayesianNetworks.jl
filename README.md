# CategoricalBayesianNetworks.jl

[![Build Status](https://github.com/ecorecipes/CategoricalBayesianNetworks.jl/actions/workflows/CI.yml/badge.svg)](https://github.com/ecorecipes/CategoricalBayesianNetworks.jl/actions/workflows/CI.yml)
[![Docs](https://img.shields.io/badge/docs-dev-blue.svg)](https://ecorecipes.github.io/CategoricalBayesianNetworks.jl/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Open Bayesian networks as structured cospans: composition, wiring diagrams, free Markov-category semantics, and interoperation with CatColab.

This is the Catlab half of the Bayesian-network model layer. `BayesianNetworks.jl` holds
everything ACSets and GATlab can express on their own -- the `SchBayesNet` schema,
construction, inspection, graphs, validation, serialisation, interventions, kernels, dynamic
networks and the brute-force evaluators -- and this package adds what genuinely needs a
category-theory library (ADR 0009). Every name of `BayesianNetworks.jl` is re-exported, so
`using CategoricalBayesianNetworks` is a superset of `using BayesianNetworks`.

Part of the ecorecipes compositional Bayesian-network ecosystem:
`FiniteKernels.jl` → `MarkovCategories.jl` → `CategoricalBayesianNetworks.jl` on the
categorical side and `FiniteKernels.jl` → `BayesianNetworks.jl` →
`BayesianNetworkInference.jl` → `InfluenceDiagrams.jl` on the numerical one, with
`BayesianNetworkFormats.jl` (file formats) and `EcologicalBayesianNetworks.jl` (model zoo).

## Features

- **Open networks** (`src/open.jl`): `OpenBayesNet` as a Catlab structured multicospan whose
  apex is a `BayesNet` and whose feet are `VariableSpace`s (variables with their ordered
  states), built with `Open(bn; inputs, outputs)`. `validate` enforces the **typed-interface
  rule**: input variables carry no mechanism in the apex, the input leg is injective, every
  mechanism-free apex variable is an input, the apex is acyclic, and the legs preserve names,
  states and positions (`InterfaceError`).
- **Composition** (`src/composition.jl`): strict `compose` (`⋅`), `glue(A, B; along)` by
  explicit pairs, `otimes` (`⊗`), `oapply` over `@relation` undirected wiring diagrams with
  `validate_composition`, mechanism `substitute`, and `rename_variable` on an open network.
  Every one is a pushout or coproduct of ACSets; under the typed-interface rule none of them
  can give a variable two mechanisms.
- **Wiring diagrams** (`src/wiring.jl`): `to_wiring_diagram` (one `MechanismBox` per
  mechanism, `VariablePort`-typed ports, fan-out as implicit copy and a dangling output as
  implicit discard), `from_wiring_diagram` on the round-trip subset,
  `to_hom_expr(FreeMarkovCategory, d)` through Catlab's junction normalisation, and
  `wiring_expression`, the direct builder that also handles a box whose every output is
  discarded.
- **Categorical semantics** (`src/evaluation.jl`): `to_free_expression` and
  `free_generators` compile a closed model into a `FreeMarkovCategory` term and its
  interpretation, `categorical_joint` evaluates it in **FinStoch** (Proposition 1: it equals
  `BayesianNetworks.joint_distribution`), and `interpret` gives the kernel
  `⊗ inputs → ⊗ outputs` of an open network with
  `interpret(compose(A, B)) ≈ compose(interpret(A), interpret(B))` and likewise for `otimes`
  (Propositions 2 and 3). Combine the kernel dictionaries of separately built operands with
  `merge_kernels`, not `merge`: `bind_kernel` derives a mechanism's default reference from
  its *name*, so two independently built networks that name a mechanism alike share a
  `KernelRef`, and a plain `merge` silently drops one of the two kernels. `merge_kernels`
  raises `ConflictingKernelError` instead. `interpret` cannot catch this itself -- once it
  holds a single dictionary the losing kernel is gone, and a genuine duplicate such as
  `A ⊗ A` is indistinguishable from the collision.
- **Drawings** (`src/graphics.jl`): `to_graphviz` on an open network (interface variables
  drawn with a dashed or bold border) and on a wiring diagram (Catlab's renderer, with the
  mechanism and variable names as labels).

## Formal category

The Lean project in [`proofs/`](proofs/) constructs the category of finite typed
acyclic network syntax with **general boundary maps**. Outputs may copy a variable
or pass an input through; parent lists retain repeated slots; empty feet and hidden
components are allowed. Equality is structural isomorphism, not numerical
equivalence. Concrete gluing, its pushout property, derived acyclicity, identities,
associativity, tensor, symmetry and coherent copy/discard are proved, with actual
Mathlib `Category`, `MonoidalCategory`, `SymmetricCategory` and
`CopyDiscardCategory` instances.

An independently defined general-legged presentation is proved equivalent to the
canonical inputs-plus-generators representation. Types and mechanism labels may
carry attributes, which the isomorphisms preserve. This is not a verified parser
or refinement of the Julia runtime, and it does not make the name-sensitive
`compose` wrapper total. `compose_structural` is the corresponding structural
runtime operation.

The project now also proves the actual finite sum-product interpretation,
normalization from local kernels and acyclic ranks, and a **strong braided
monoidal functor into the existing FinStoch category**, preserving composition,
tensor, copy and discard. General finite signature state types may even be empty.
Ordered CPT and output-first enumeration bridges retain repeated slots and
copied/pass-through outputs. Raw syntax remains non-Markov: discarded mechanisms
disappear under normalized semantics, not under structural equality.

`open_network_certificate(o; ranks=nothing)` exports
`OpenNet.RawCertificate/v1` records with dense part-ID indices, original
positions, full reference tags, attributed feet and a rank witness. The Lean
record checker constructs a valid general-legged network from acceptance.
`lake exe check_certificate PATH` in `proofs/` now reads the actual versioned
JSON, checks bounds/tags/fields and invokes that checker. It rejects malformed
JSON or invalid records with a nonzero exit status.
This structural certificate does not contain numerical tables or certify
Julia's compiler, floating-point arithmetic or the exporter implementation itself.
See [`proofs/SEMANTICS-REPORT.md`](proofs/SEMANTICS-REPORT.md) and
[`proofs/EXPORTER-CONTRACT.md`](proofs/EXPORTER-CONTRACT.md).
The JSON-reader soundness and exact translation boundary are documented in
[`proofs/JSON-REPORT.md`](proofs/JSON-REPORT.md).

`export_open_certificate` and `export_open_operation_certificate` additionally
capture the **complete one-based raw cospan** profile, including both full
feet and the actual four-sort cocone maps from composition/tensor. They
preserve shuffled raw positions, repeated names/slots/outputs and hidden
material; optional signatures are finite relations, not label-keyed functions.
This is a separate data format for reference checking and concrete HOL4
proof attempts, not a Julia/compiler theorem. See the
[raw cospan guide](docs/src/cospan_certificates.md).

`lake build --wfail`, `make audit` and `make docs` in `proofs/` build the development,
enforce the permitted axiom/source policy and generate the full readable proof
documents. See [ADR 0010](docs/adr/0010-general-open-network-proof-layer.md).

## Installation

The ecosystem packages are not registered. Install this package and its ecosystem
dependencies by URL, in dependency order:

```julia
using Pkg
Pkg.add(url="https://github.com/ecorecipes/FiniteKernels.jl")
Pkg.add(url="https://github.com/ecorecipes/MarkovCategories.jl")
Pkg.add(url="https://github.com/ecorecipes/BayesianNetworkFormats.jl")
Pkg.add(url="https://github.com/ecorecipes/BayesianNetworks.jl")
Pkg.add(url="https://github.com/ecorecipes/CategoricalBayesianNetworks.jl")
```

Requires Julia ≥ 1.12.

## Quick Start

`compose_structural(A, B)` provides sequential structural gluing on matching
valid interfaces, retaining duplicate names on distinct hidden parts. `compose`
keeps its existing name-safe policy. Use part ids or explicit renaming before
passing a structurally composed network with duplicate names to name-based APIs.
Repeated input slots and non-default space references survive the wiring bridge.

```julia
using CategoricalBayesianNetworks

# Split the SPEC section 45 reference network in two and glue it back together.
abiotic = bayesnet(:Climate => [:dry, :normal, :wet], :Irrigation => [:low, :high],
                   :SoilMoisture => [:low, :medium, :high];
                   mechanisms = [:SoilMoisture => (:Climate, :Irrigation)])
biotic = bayesnet(:SoilMoisture => [:low, :medium, :high], :GrazingPressure => [:low, :high],
                  :Vegetation => [:sparse, :moderate, :dense], :HabitatQuality => [:poor, :good],
                  :Occupancy => [:absent, :present];
                  mechanisms = [:GrazingPressure => (), :Vegetation => (:SoilMoisture, :GrazingPressure),
                                :HabitatQuality => :Vegetation, :Occupancy => :HabitatQuality],
                  closed = false)
A = Open(abiotic; outputs = [:SoilMoisture])
B = Open(biotic; inputs = [:SoilMoisture], outputs = [:Occupancy])
C = glue(A, B; along = [:SoilMoisture => :SoilMoisture])   # or compose(A, B), or oapply(uwd, [A, B])
canonicalize(apex(C)) == canonicalize(reference_habitat_bn())   # true

# The categorical evaluator agrees with the brute-force joint (Proposition 1).
m = reference_habitat_model()
J = joint_distribution(m)
categorical_joint(m) ≈ J                    # true

# The wiring-diagram view and its free expression.
d = to_wiring_diagram(reference_habitat_bn())
nboxes(d), nwires(d)                        # (7, 13)
evaluate(to_hom_expr(FreeMarkovCategory, d), free_generators(m)) ≈ J   # true

# The semantics of an open network, and its compositionality (Propositions 2 and 3).
by_name = Dict(x => kernel(m, x) for x in variable_names(syntax(m)))
kA, kB = interpret(A, by_name), interpret(B, by_name)
interpret(compose(A, B), by_name) ≈ compose(kA, kB)   # true
to_graphviz(d)                                  # the wiring diagram, as SVG
```

## Vignettes

| # | Vignette | Description |
|---|---|---|
| 1 | [Wiring diagrams and evaluation](https://github.com/ecorecipes/CategoricalBayesianNetworks.jl/blob/main/vignettes/01_wiring_diagrams_and_evaluation/01_wiring_diagrams_and_evaluation.md) | Networks as wiring diagrams, from diagrams to expressions, and two evaluation routes to the same joint |
| 2 | [Open networks and composition](https://github.com/ecorecipes/CategoricalBayesianNetworks.jl/blob/main/vignettes/02_open_networks_and_composition/02_open_networks_and_composition.md) | Splitting a network, the typed-interface rule, sequential composition, gluing, tensor, substitution and compositional semantics |

Each vignette is also published as a tutorial in the [documentation](https://ecorecipes.github.io/CategoricalBayesianNetworks.jl/);
the sources are the `.qmd` files in [`vignettes/`](vignettes/).
