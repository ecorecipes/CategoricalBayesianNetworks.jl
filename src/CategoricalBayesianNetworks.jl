"""
    CategoricalBayesianNetworks

Open Bayesian networks as structured cospans: composition, wiring diagrams, free
Markov-category semantics, and interoperation with CatColab.

This is the Catlab half of the Bayesian-network model layer. `BayesianNetworks.jl`
holds everything that ACSets and GATlab can express on their own -- the
`SchBayesNet` schema, construction, inspection,
graphs, validation, serialisation, interventions, kernels and the brute-force
evaluators -- and this package adds what genuinely needs a category-theory library:

  - **Open networks** (`src/open.jl`): [`OpenBayesNet`](@ref) as a Catlab structured
    multicospan on the `Variable` / `State` interface, built with [`Open`](@ref), and
    the typed-interface rule its validation enforces.
  - **Composition** (`src/composition.jl`): [`compose`](@ref), [`glue`](@ref),
    [`otimes`](@ref), [`oapply`](@ref) over undirected wiring diagrams, and
    [`substitute`](@ref), every one of them a pushout or coproduct of ACSets.
  - **Wiring diagrams** (`src/wiring.jl`): the directed-wiring-diagram view
    ([`to_wiring_diagram`](@ref), [`from_wiring_diagram`](@ref),
    [`wiring_expression`](@ref), `to_hom_expr`).
  - **Categorical semantics** (`src/evaluation.jl`): [`to_free_expression`](@ref) and
    [`categorical_joint`](@ref), which evaluate a model through MarkovCategories'
    functor into FinStoch, and [`interpret`](@ref), the semantics of an open network.

Every name of `BayesianNetworks.jl` is re-exported, so `using
CategoricalBayesianNetworks` is a superset of `using BayesianNetworks`.

Part of the ecorecipes compositional Bayesian-network ecosystem.
"""
module CategoricalBayesianNetworks

using Catlab, Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra: StructuredCospan, StructuredMulticospan,
                                 StructuredCospanOb,
                                 OpenACSetTypes, OpenACSetLeg, apex, legs, feet, left,
                                 right,
                                 force, components, is_natural, infer_acset_cat, pushout
using Catlab.WiringDiagrams: UndirectedWiringDiagram, nboxes, boxes, ports, junction,
                             WiringDiagram, Box, Port, Wire, InputPort, OutputPort,
                             add_box!, add_wire!, input_id, output_id, box_ids, box,
                             input_ports, output_ports, in_wires, out_wires, wires,
                             nwires
using Catlab.Graphics: LayoutOrientation, LeftToRight, TopToBottom
using Catlab.Programs: @relation
using ACSets
using FiniteKernels
using MarkovCategories
using BayesianNetworks
# Imported by name: the internals of `BayesianNetworks.jl` that the categorical layer
# builds on. They are the brute-force evaluator's factor machinery, the model-record
# helpers and the structural predicates; none of them is part of that package's public
# interface, and this package is the only consumer.
using BayesianNetworks: BayesianNetworks, AbstractVariableSpace, AbstractBayesNet,
                        BayesNetUntyped, VariableSpace, VariableSpaceUntyped,
                        DEFAULT_MAX_STATES, _closed_semantics, _complete_spaces,
                        _factors, _in_range, _joint_atol, _mechanism_id, _state_table,
                        _mechanism_spaces, _product, _variable_id, _with

import Catlab.Theories: compose, otimes, munit, dom, codom, id, ⋅, ⊗
import Catlab.WiringDiagrams: oapply, substitute, to_wiring_diagram, to_hom_expr
import Catlab.Graphics.WiringDiagramLayouts: box_label, wire_label
import BayesianNetworks: validate, validation_errors, inputs, rename_variable,
                         to_graphviz
# `is_isomorphic` is exported by both Catlab and `BayesianNetworks` and this package
# neither defines nor extends it; the explicit import decides which one the re-export
# below carries. (`validate` and `to_graphviz`, the other two such names, are imported
# above because this package does add methods to them.)
using BayesianNetworks: is_isomorphic

# Re-exported names of the packages below this one, so that
# `using CategoricalBayesianNetworks` is a superset of `using BayesianNetworks`.
for name in setdiff(names(BayesianNetworks), [:BayesianNetworks])
    @eval export $name
end
# Re-exported Catlab names for open networks: structured-cospan accessors, the
# symmetric monoidal operations and undirected wiring diagrams.
export apex, legs, feet, dom, codom, compose, otimes, munit, id, ⋅, ⊗, oapply,
       UndirectedWiringDiagram, @relation
# Re-exported Catlab names for directed wiring diagrams and their expressions.
export WiringDiagram, Box, Port, Wire, InputPort, OutputPort, add_box!, add_wire!,
       input_id, output_id, box_ids, box, boxes, nboxes, wires, nwires, input_ports,
       output_ports, in_wires, out_wires, to_wiring_diagram, to_hom_expr,
       LeftToRight, TopToBottom
# Re-exported MarkovCategories names for the free expressions of `src/evaluation.jl`.
export evaluate, FreeMarkovCategory, ThMarkovCategory, mcopy, delete, braid, Δ, ◊, σ,
       Ob, Hom

# open.jl
export OpenBayesNetObUntyped, OpenBayesNetUntyped, OpenBayesNetOb, OpenBayesNet, Open,
       outputs, input_space, output_space, input_variables, output_variables, left_leg,
       right_leg
# composition.jl
export interface_matches, glue, validate_composition, substitute
# wiring.jl
export VariablePort, MechanismBox, BayesWiringDiagram, from_wiring_diagram,
       wiring_expression
# evaluation.jl
export to_free_expression, free_generators, categorical_joint, interpret

include("open.jl")
include("composition.jl")
include("rename.jl")
include("wiring.jl")
include("evaluation.jl")
include("graphics.jl")

end # module
