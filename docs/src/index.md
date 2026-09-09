# CategoricalBayesianNetworks.jl

Open Bayesian networks as structured cospans: composition, wiring diagrams, free Markov-category semantics, and interoperation with CatColab.

This is the Catlab half of the Bayesian-network model layer. [`BayesianNetworks.jl`](https://ecorecipes.github.io/BayesianNetworks.jl/) holds everything that ACSets and GATlab can express on their own -- the `SchBayesNet` schema and the `BayesNet` type, construction, inspection, derived graphs, validation, canonical forms, JSON serialisation, interventions, kernels, dynamic networks and the brute-force evaluators -- and this package adds what genuinely needs a category-theory library (ADR 0009). Every name of `BayesianNetworks.jl` is re-exported, so `using CategoricalBayesianNetworks` is a superset of `using BayesianNetworks`.

## Open networks

An open network is a Catlab structured cospan: a `BayesNet` apex with an input and an output interface, each a `VariableSpace` (variables with their states) embedded into the apex by a leg. [`Open`](@ref) builds one from named variables; the legs, not the names, say which apex variable each interface variable is.

```julia
using CategoricalBayesianNetworks

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

C = compose(A, B)                                          # strict: outputs(A) must equal inputs(B)
G = glue(A, B; along = [:SoilMoisture => :SoilMoisture])   # by explicit pairs
canonicalize(apex(G)) == canonicalize(reference_habitat_bn())   # true

uwd = @relation (occ,) begin
    abiotic(soil)
    biotic(soil, occ)
end
oapply(uwd, Dict(:abiotic => A, :biotic => B)) == G  # true
```

Every open network satisfies the **typed-interface rule** (checked by [`validate`](@ref) on construction): input variables have no mechanism in the apex, the input leg is injective, every mechanism-free apex variable is an input, the apex is acyclic, and the legs preserve names, states and positions. Under this rule the pushouts behind [`compose`](@ref), [`glue`](@ref) and [`substitute`](@ref) never give a variable two mechanisms. [`otimes`](@ref) places networks side by side (names may then repeat), and [`oapply`](@ref) composes along an undirected wiring diagram with the rule checked afterwards by [`validate_composition`](@ref).

[`substitute`](@ref) replaces one mechanism by an open network whose interface matches its parents and target, so a mechanism can be refined into a sub-network without touching the containing network's interface; [`rename_variable`](@ref) renames a variable in the apex and both feet, which is how interfaces that differ only by name are lined up.

## Wiring diagrams

[`compose_structural`](@ref) is the sequential operation without a name-freshness
restriction; it preserves distinct hidden parts even when their names coincide.
The existing [`compose`](@ref) remains the name-safe compatibility wrapper.
Repeated input occurrences are preserved by diagonal factor evaluation and
per-occurrence copying. Ports carry their space references as well as names and
ordered states; incompatible references are rejected instead of erased.

[`to_wiring_diagram`](@ref) draws a network as a Catlab `WiringDiagram`: one box per mechanism with input ports in `input_position` order and one output port, a wire from the port producing each variable to every port consuming it (fan-out is an implicit copy, a dangling output an implicit discard), typed by [`VariablePort`](@ref)s and [`MechanismBox`](@ref)es. [`from_wiring_diagram`](@ref) inverts it on the round-trip subset (flat diagrams of single-output boxes), so `canonicalize(first(from_wiring_diagram(to_wiring_diagram(bn)))) == canonicalize(bn)`. `to_hom_expr(FreeMarkovCategory, d)` turns the diagram into a free expression through Catlab's junction normalisation (or [`wiring_expression`](@ref) when a box is entirely discarded). Catlab's `substitute` on the diagram agrees with [`substitute`](@ref) on the network.

## Categorical evaluation

[`to_free_expression`](@ref) compiles a closed model into a `FreeMarkovCategory` term `I → X_1 ⊗ ... ⊗ X_n` with explicit `mcopy` and `braid`, [`free_generators`](@ref) maps its generators to the model's spaces and kernels, and [`categorical_joint`](@ref) evaluates the term in **FinStoch** through MarkovCategories' functor. Proposition 1 is that this equals `BayesianNetworks.joint_distribution`, which enumerates every assignment instead; the test suite checks it on every example and on random networks. The two must stay independent implementations: `categorical_joint` never calls the brute-force evaluator.

[`interpret`](@ref) gives the kernel `⊗ inputs → ⊗ outputs` of an open network, and `interpret(compose(A, B)) ≈ compose(interpret(A), interpret(B))`, likewise for `otimes` (Propositions 2 and 3). Both are checked by the test suite here and proved in `BayesianNetworks.jl`'s Lean project for the abstract finite model (`Finite/Tensor.lean`, `Finite/Open.lean`), which also proves the closure theorem: composition along a matched interface preserves the typed-interface rule, acyclicity included.

Every evaluator takes `atol`, the normalisation tolerance used for the validation, the per-mechanism kernel check and the kernel returned; a model read from a file at `atol = 1e-6` must be evaluated at `1e-6` as well.

## The general syntax category in Lean

The separate `proofs/` project proves a category of finite typed acyclic networks
with arbitrary output legs, including copied outputs and pass-through variables.
Its ordered parent lists allow repeated input occurrences. Inputs identify exactly
the exogenous variables, and each internal generator produces one variable.
Hidden components and empty interfaces are retained.

Arrow equality is structural isomorphism. Total gluing and tensor preserve validity;
the category and symmetric monoidal laws follow from concrete internal
renumberings. The project supplies Mathlib `Category`, `MonoidalCategory`,
`SymmetricCategory` and `CopyDiscardCategory` instances, plus both round trips to a
general-legged presentation and a typed-apex pushout universal property.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted by its fail-closed
audit.

The explicit finite sum-product interpretation now gives a strong braided
monoidal functor into the existing FinStoch category. It derives normalization
from local normalized kernels and acyclic ranks and preserves composition,
tensor, copy and discard. The exact output-first enumeration formula and
ordered local CPT adapter are proved as well.

This is not a quotient by numerical equality. Naturality of discard would be false
for retained syntax; hidden mechanisms disappear under normalized interpretation
instead. A full Julia runtime/array refinement remains separate work.
In particular, the name-freshness condition of the Julia `compose` wrapper is
stricter than mathematical composability. The earlier finite semantics and schema
emitter remain in `BayesianNetworks.jl`, as recorded in ADR 0010.

## Structural certificates

[`open_network_certificate`](@ref) exports a JSON-compatible
`OpenNet.RawCertificate/v1` record using dense 0-based variable indices and the
actual 1-based state/input positions. It retains reference tags, boundary
attributes, repeated slots/outputs, hidden components and a topological rank
witness, without requiring globally unique names.

The Lean-side finite record checker proves that acceptance constructs valid
typed acyclic syntax. The executable `lake exe check_certificate PATH` in
`proofs/` parses the versioned JSON and runs that checker, returning a nonzero
status for malformed or invalid input. Integer fields require integer JSON
tokens; fractional/exponent spellings are not coerced.

Exporting a record is not a proof of the Julia exporter,
the JSON implementation or floating-point evaluation. Numerical tables are
deliberately outside this minimal structural payload.

For complete raw part identities and operation witnesses,
[`export_open_certificate`](@ref) and
[`export_open_operation_certificate`](@ref) provide the distinct one-based
`ecorecipes.open-network-certificate` 1.0.0 profile. It contains complete
apex/foot rows, actual leg maps, and actual four-sort colimit cocones for
composition/tensor, with an optional finite relational local signature.
See [Raw cospan certificates](cospan_certificates.md) for resource limits and
the difference between reference acceptance, kernel-checked instances and
unproved general runtime refinement.

## Drawings

[`to_graphviz`](@ref) is `BayesianNetworks.jl`'s function, extended here with a method for an open network (the apex, with the input variables dashed and the output variables bold) and one for a wiring diagram (Catlab's renderer, with the mechanism and variable names as labels). Both `show` as SVG in notebooks and quarto.

## Module

```@docs
CategoricalBayesianNetworks
```
