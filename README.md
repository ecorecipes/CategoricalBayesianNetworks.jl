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
  (Propositions 2 and 3).
- **Drawings** (`src/graphics.jl`): `to_graphviz` on an open network (interface variables
  drawn with a dashed or bold border) and on a wiring diagram (Catlab's renderer, with the
  mechanism and variable names as labels).

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
kA, kB = interpret(A, m), interpret(B, m)
interpret(compose(A, B), m) ≈ compose(kA, kB)   # true
to_graphviz(d)                                  # the wiring diagram, as SVG
```

## Vignettes

Rendered vignettes live in [`vignettes/`](vignettes/) and are published in the
[documentation](https://ecorecipes.github.io/CategoricalBayesianNetworks.jl/).
