"""
The directed wiring-diagram view (SPEC §7, §12). A network is drawn as a Catlab
`WiringDiagram` with one box per mechanism: the box's input ports are the mechanism's
inputs in `input_position` order and its single output port is the target. A wire runs
from the port that produces a variable (the box of its mechanism, or an outer input
port for an exogenous variable) to every port that consumes it. Copying is implicit in
the fan-out of a wire and discarding is implicit in an output port that no wire leaves,
which is how Catlab draws `ThMarkovCategory` (see MarkovCategories.jl's
`mcopy(::Ports{ThMarkovCategory.Meta.T}, n)`). Reading a Bayesian network as a string
diagram in a Markov category, with copy and discard carrying the structure that a
directed graph leaves implicit, is [Fritz2020](@cite)'s synthetic presentation.

The diagram is typed: ports carry [`VariablePort`](@ref)s (name, states and space reference), boxes
carry [`MechanismBox`](@ref)es (name and `KernelRef`). `from_wiring_diagram`
inverts the view on the round-trip subset (flat diagrams of single-output boxes with
typed ports), and `to_hom_expr(FreeMarkovCategory, wd)` turns the diagram into a free
Markov-category expression that MarkovCategories' `evaluate` interprets in FinStoch.
"""

# Port and box values
#####################

"""
    VariablePort(name::Symbol, states::Vector{Symbol}, space_ref::KernelRef=NoRef())

The value carried by a port of a network's wiring diagram: its name, states in
`state_position` order and `space_ref`. Equality includes all three attributes.
"""
struct VariablePort
    name::Symbol
    states::Vector{Symbol}
    space_ref::KernelRef
end

VariablePort(name::Symbol, states::Vector{Symbol}) = VariablePort(name, states, NoRef())

# The port of variable `v` of a network. A port needs the variable's `space_ref`, so an
# unset one, which is structurally valid, is a `MissingAttributeError`.
function VariablePort(bn::AbstractVariableSpace, v)
    id = _variable_id(bn, v)
    ref = subpart(bn, id, :space_ref)
    _has_value(ref) || throw(MissingAttributeError(:Variable, id, :space_ref))
    return VariablePort(variable_name(bn, id), states(bn, v), ref)
end

function Base.:(==)(a::VariablePort, b::VariablePort)
    return a.name == b.name && a.states == b.states && a.space_ref == b.space_ref
end
function Base.hash(p::VariablePort, h::UInt)
    return hash(p.space_ref, hash(p.states, hash(p.name, hash(:VariablePort, h))))
end

"""
    MechanismBox(name::Symbol, kernel_ref::KernelRef)

The value carried by a box of a network's wiring diagram: the mechanism's name and its
kernel reference. The box's ports say which variables the mechanism reads and writes.
"""
struct MechanismBox
    name::Symbol
    kernel_ref::KernelRef
end

function Base.:(==)(a::MechanismBox, b::MechanismBox)
    return a.name == b.name && a.kernel_ref == b.kernel_ref
end
function Base.hash(b::MechanismBox, h::UInt)
    return hash(b.kernel_ref, hash(b.name, hash(:MechanismBox, h)))
end

Base.show(io::IO, p::VariablePort) = print(io, p.name, "{", join(p.states, ","), "}")
Base.show(io::IO, b::MechanismBox) = print(io, b.name)

"""
    BayesWiringDiagram

The type of the diagrams built by [`to_wiring_diagram`](@ref):
`WiringDiagram{ThMarkovCategory.Meta.T, VariablePort, Nothing, MechanismBox}` (the
theory parameter is the Catlab tag of `ThMarkovCategory`). Wires carry no value.
"""
const BayesWiringDiagram = WiringDiagram{ThMarkovCategory.Meta.T,VariablePort,Nothing,
                                         MechanismBox}

# Catlab's `copy` for wiring diagrams goes through the untyped constructor and drops the
# type parameters, which then breaks every non-mutating operation on a typed diagram.
Base.copy(d::BayesWiringDiagram) = BayesWiringDiagram(copy(d.diagram), d.value)

# ACSet -> wiring diagram
#########################

# The typed-interface rule on the chosen interface, without building an open network:
# rules 1 to 3 of `_check_interface_rules!` (rules 4 and 5 are about the apex and the
# legs, which a diagram does not have), with repeated inputs reported by their apex id.
function _check_wiring_interface(bn::AbstractBayesNet, in_ids::AbstractVector{Int})
    errs = _check_interface_rules!(Exception[], bn, in_ids,
                                   dup -> (variable_name.(Ref(bn), in_ids[dup]),
                                           in_ids[dup]))
    isempty(errs) || throw(first(errs))
    return nothing
end

function _wiring_diagram(bn::AbstractBayesNet, in_ids::AbstractVector{Int},
                         out_ids::AbstractVector{Int})
    _check_wiring_interface(bn, in_ids)
    # Every variable has a port, which carries its `space_ref`, and every mechanism a box,
    # which carries its `kernel_ref`: an unset one is reported before anything is built.
    _require_attributes(bn; types=(:Ref,))
    d = BayesWiringDiagram([VariablePort(bn, v) for v in in_ids],
                           [VariablePort(bn, v) for v in out_ids])
    source = Dict{Int,Port}()
    for (i, v) in enumerate(in_ids)
        source[v] = Port(input_id(d), OutputPort, i)
    end
    for v in topological_order(bn)
        mech = mechanism_of(bn, v)
        mech === nothing && continue
        ps = inputs(bn, mech)
        b = add_box!(d,
                     Box(MechanismBox(mechanism_name(bn, mech), kernel_ref(bn, mech)),
                         [VariablePort(bn, p) for p in ps], [VariablePort(bn, v)]))
        source[v] = Port(b, OutputPort, 1)
        for (i, p) in enumerate(ps)
            add_wire!(d, source[p] => Port(b, InputPort, i))
        end
    end
    for (j, v) in enumerate(out_ids)
        add_wire!(d, source[v] => Port(output_id(d), InputPort, j))
    end
    return d
end

"""
    to_wiring_diagram(bn; inputs = exogenous variables, outputs = the others) -> BayesWiringDiagram
    to_wiring_diagram(m::BayesModel; kwargs...)
    to_wiring_diagram(o::OpenBayesNet)

The directed wiring diagram of a network (SPEC §7, §12): one box per mechanism, added
in topological order of the target, with input ports for the mechanism's inputs (in
`input_position` order) and one output port for its target; a wire from the port that
produces each variable (the box of its mechanism, or the outer input port of an
exogenous variable) to every port that consumes it. Fan-out is an implicit copy and an
unused output port an implicit discard. Ports carry [`VariablePort`](@ref)s and boxes
[`MechanismBox`](@ref)es.

`inputs` default to the exogenous variables and `outputs` to every other variable in
topological order; both are lists of names, and `outputs` may repeat a variable or
name an input (a pass-through wire). The interface must satisfy the typed-interface
rule (`InterfaceError`): inputs are distinct and have no mechanism, and every
mechanism-free variable is an input. For an open network the interface is its feet. The
network must be valid with unique names. Every port carries its variable's `space_ref`
and every box its mechanism's `kernel_ref`, so an unset one, which is structurally
valid, raises `MissingAttributeError` before any port or box is built.

# Example

```jldoctest
julia> d = to_wiring_diagram(reference_habitat_bn());

julia> nboxes(d), nwires(d)
(7, 13)

julia> box(d, 5)
Box(Vegetation_mechanism, [SoilMoisture{low,medium,high},GrazingPressure{low,high}], [Vegetation{sparse,moderate,dense}])
```
"""
function to_wiring_diagram(bn::AbstractBayesNet;
                           inputs::Union{Nothing,AbstractVector{Symbol}}=nothing,
                           outputs::Union{Nothing,AbstractVector{Symbol}}=nothing)
    validate(bn; unique_names=true)
    in_ids = inputs === nothing ? exogenous(bn) : Int[variable_id(bn, x) for x in inputs]
    out_ids = outputs === nothing ? filter(v -> !(v in in_ids), topological_order(bn)) :
              Int[variable_id(bn, x) for x in outputs]
    return _wiring_diagram(bn, in_ids, out_ids)
end

to_wiring_diagram(m::BayesModel; kw...) = to_wiring_diagram(syntax(m); kw...)

function to_wiring_diagram(o::OpenBayesNetCospan)
    validate(o; unique_names=true)
    return _wiring_diagram(apex(o), input_variables(o), output_variables(o))
end

# Wiring diagram -> ACSet
#########################

function _port_variable(bn::BayesNet, p, where_::Int, port::Int)
    p isa VariablePort ||
        throw(WiringDiagramError(:port_value, where_, port,
                                 "port carries $(repr(p)); a VariablePort is required"))
    return add_variable!(bn, p.name; states=p.states, space_ref=p.space_ref)
end

"""
    from_wiring_diagram(d::WiringDiagram) -> (BayesNet, inputs::Vector{Symbol}, outputs::Vector{Symbol})

Read a network back from a wiring diagram of the round-trip subset: a flat diagram
(no nested diagrams or junctions) whose boxes carry [`MechanismBox`](@ref)es and have
exactly one output port, whose ports carry [`VariablePort`](@ref)s, and in which every
box input port and every outer output port receives exactly one wire. Every outer input
port and every box output port defines a variable (with the port's states), every box a
mechanism whose inputs are the variables wired into its input ports, in port order; a
wire must connect ports with the same name, states and space reference. The result is validated with
unique names, and returned together with the names of the interface variables, so that
`canonicalize(first(from_wiring_diagram(to_wiring_diagram(bn)))) == canonicalize(bn)`
(SPEC §12). Violations are `WiringDiagramError`s.
"""
function from_wiring_diagram(d::WiringDiagram)
    bn = BayesNet()
    source = Dict{Port,Int}()
    for (i, p) in enumerate(input_ports(d))
        source[Port(input_id(d), OutputPort, i)] = _port_variable(bn, p, input_id(d), i)
    end
    for b in box_ids(d)
        bx = box(d, b)
        bx isa Box ||
            throw(WiringDiagramError(:box, b, 0,
                                     "box is a $(nameof(typeof(bx))); only atomic boxes are supported"))
        bx.value isa MechanismBox ||
            throw(WiringDiagramError(:box_value, b, 0,
                                     "box carries $(repr(bx.value)); a MechanismBox is required"))
        outs = output_ports(bx)
        length(outs) == 1 ||
            throw(WiringDiagramError(:outputs, b, length(outs),
                                     "box $(bx.value.name) has $(length(outs)) output ports; exactly one is required"))
        source[Port(b, OutputPort, 1)] = _port_variable(bn, only(outs), b, 1)
    end
    for b in box_ids(d)
        bx = box(d, b)
        ps = Int[]
        for (i, p) in enumerate(input_ports(bx))
            v = _wired_source(d, bn, source, Port(b, InputPort, i), p)
            push!(ps, v)
        end
        add_mechanism!(bn, source[Port(b, OutputPort, 1)]; inputs=ps, name=bx.value.name,
                       kernel_ref=bx.value.kernel_ref)
    end
    ins = Symbol[variable_name(bn, source[Port(input_id(d), OutputPort, i)])
                 for i in eachindex(input_ports(d))]
    outs = Symbol[variable_name(bn,
                                _wired_source(d, bn, source,
                                              Port(output_id(d), InputPort, j),
                                              p))
                  for (j, p) in enumerate(output_ports(d))]
    validate(bn; unique_names=true)
    return bn, ins, outs
end

# The variable wired into `target`, checked against the port value `p`.
function _wired_source(d::WiringDiagram, bn::BayesNet, source::Dict{Port,Int}, target::Port,
                       p)
    ws = in_wires(d, target)
    length(ws) == 1 ||
        throw(WiringDiagramError(:wires, target.box, target.port,
                                 "port receives $(length(ws)) wires; exactly one is required"))
    v = source[only(ws).source]
    (p isa VariablePort && p == VariablePort(bn, v)) ||
        throw(WiringDiagramError(:port_mismatch, target.box, target.port,
                                 "port name, states or space reference disagree with variable $(variable_name(bn, v))"))
    return v
end

# Wiring diagram -> free expression
###################################

# The same diagram with `Symbol` port and box values in an untyped (`Any`) diagram,
# which is what Catlab's expression algorithms can copy and rewrite.
function _symbolic(d::BayesWiringDiagram)
    u = WiringDiagram{ThMarkovCategory.Meta.T}(Any[p.name for p in input_ports(d)],
                                               Any[p.name for p in output_ports(d)])
    for b in box_ids(d)
        bx = box(d, b)
        add_box!(u,
                 Box(bx.value.name, Symbol[p.name for p in input_ports(bx)],
                     Symbol[p.name for p in output_ports(bx)]))
    end
    for w in wires(d)
        add_wire!(u, w.source => w.target)
    end
    return u
end

# Box ids in an order where every wire runs forward.
function _box_order(d::WiringDiagram)
    ids = box_ids(d)
    indeg = Dict{Int,Int}(b => 0 for b in ids)
    succ = Dict{Int,Vector{Int}}(b => Int[] for b in ids)
    for w in wires(d)
        s, t = w.source.box, w.target.box
        (haskey(indeg, s) && haskey(indeg, t)) || continue
        indeg[t] += 1
        push!(succ[s], t)
    end
    ready = sort!([b for b in ids if indeg[b] == 0]; rev=true)
    order = Int[]
    while !isempty(ready)
        b = pop!(ready)
        push!(order, b)
        for t in succ[b]
            indeg[t] -= 1
            indeg[t] == 0 && (push!(ready, t); sort!(ready; rev=true))
        end
    end
    length(order) == length(ids) ||
        throw(WiringDiagramError(:cycle, 0, 0, "the wiring diagram has a cycle"))
    return order
end

# Whether every box has a directed path to an outer output port; Catlab's `to_hom_expr`
# cannot reduce boxes whose every output is discarded.
function _all_boxes_reach_outputs(d::WiringDiagram)
    reach = Set{Int}(output_id(d))
    for b in reverse(_box_order(d))
        any(w.target.box in reach for w in out_wires(d, b)) && push!(reach, b)
    end
    return all(b in reach for b in box_ids(d))
end

# One layer of the expression: `otimes` of the parts.
_layer(parts) = foldl(otimes, parts)

# Adjacent braids moving the wire at `pos` to position `to > pos`; `wires` is updated.
function _bubble!(steps, wires::Vector{Symbol}, obj, pos::Int, to::Int)
    while pos < to
        parts = Any[]
        pre, suf = wires[1:(pos - 1)], wires[(pos + 2):end]
        isempty(pre) || push!(parts, id(_free_tensor([obj[w] for w in pre])))
        push!(parts, braid(obj[wires[pos]], obj[wires[pos + 1]]))
        isempty(suf) || push!(parts, id(_free_tensor([obj[w] for w in suf])))
        push!(steps, _layer(parts))
        wires[pos], wires[pos + 1] = wires[pos + 1], wires[pos]
        pos += 1
    end
    return pos
end

"""
    wiring_expression(d::BayesWiringDiagram; syntax = FreeMarkovCategory) -> FreeMarkovCategory.Hom

A free Markov-category expression `⊗ inputs → ⊗ outputs` for a network's wiring
diagram, built directly from the diagram (an independent alternative to Catlab's
`to_hom_expr`): object generators are named by variables and morphism generators by
mechanisms (`⊗ inputs → target`, as in [`to_free_expression`](@ref)). Boxes are applied
in topological order while every wire is kept (parents are copied before a box reads
them), and a final layer copies, discards and permutes the wires into the order of the
outer output ports. Works for every diagram of the round-trip subset, including boxes
whose outputs are all discarded. Evaluate with `evaluate(expr, free_generators(m))`.
"""
function wiring_expression(d::BayesWiringDiagram; syntax::Module=FreeMarkovCategory)
    from_wiring_diagram(d)
    obj = Dict{Symbol,Any}()
    for p in input_ports(d)
        obj[p.name] = Ob(syntax, p.name)
    end
    for b in box_ids(d)
        for p in vcat(input_ports(box(d, b)), output_ports(box(d, b)))
            haskey(obj, p.name) || (obj[p.name] = Ob(syntax, p.name))
        end
    end
    wires_ = Symbol[p.name for p in input_ports(d)]
    length(unique(wires_)) == length(wires_) ||
        throw(WiringDiagramError(:inputs, input_id(d), 0, "input ports repeat a variable"))
    # The variable each producing port carries.
    produced = Dict{Port,Symbol}(Port(input_id(d), OutputPort, i) => p.name
                                 for (i, p) in enumerate(input_ports(d)))
    for b in box_ids(d)
        produced[Port(b, OutputPort, 1)] = only(output_ports(box(d, b))).name
    end
    steps = Any[]
    expr = isempty(wires_) ? nothing : id(_free_tensor([obj[w] for w in wires_]))
    for b in _box_order(d)
        bx = box(d, b)
        ps = Symbol[]
        for i in eachindex(input_ports(bx))
            ws = in_wires(d, Port(b, InputPort, i))
            length(ws) == 1 ||
                throw(WiringDiagramError(:wires, b, i,
                                         "port receives $(length(ws)) wires; exactly one is required"))
            push!(ps, produced[only(ws).source])
        end
        t = produced[Port(b, OutputPort, 1)]
        κ = Hom(bx.value.name, _free_tensor([obj[p] for p in ps]), obj[t])
        if isempty(wires_)
            expr = expr === nothing ? κ : compose(expr, κ)
            push!(wires_, t)
            continue
        end
        # Keep one wire and supply one additional copy for each ordered input occurrence.
        layer = Any[]
        newwires = Symbol[]
        for w in wires_
            n = count(==(w), ps)
            if n > 0
                push!(layer, _mcopy_chain(obj[w], n + 1))
                append!(newwires, fill(w, n + 1))
            else
                push!(layer, id(obj[w]))
                push!(newwires, w)
            end
        end
        push!(steps, _layer(layer))
        wires_ = newwires
        # 2. move the copies to the right end, in parent order
        for p in ps
            _bubble!(steps, wires_, obj, findall(==(p), wires_)[2], length(wires_))
        end
        # 3. apply the mechanism to the last |ps| wires
        keep = wires_[1:(end - length(ps))]
        push!(steps,
              isempty(keep) ? κ : otimes(id(_free_tensor([obj[w] for w in keep])), κ))
        wires_ = vcat(keep, [t])
    end
    # 4. copy, discard and permute into output order
    outs = Symbol[produced[only(in_wires(d, Port(output_id(d), InputPort, j))).source]
                  for j in eachindex(output_ports(d))]
    if !isempty(wires_)
        layer = Any[]
        newwires = Symbol[]
        for w in wires_
            k = count(==(w), outs)
            if k == 0
                push!(layer, delete(obj[w]))
            elseif k == 1
                push!(layer, id(obj[w]))
                push!(newwires, w)
            else
                push!(layer, _mcopy_chain(obj[w], k))
                append!(newwires, fill(w, k))
            end
        end
        # A layer of identities changes nothing; leaving it out keeps the expression of
        # a network whose outputs are already the wires as short as it can be.
        newwires == wires_ || push!(steps, _layer(layer))
        wires_ = newwires
        # bubble sort into the order of `outs`
        for j in eachindex(outs)
            pos = findfirst(==(outs[j]), view(wires_, j:length(wires_))) + j - 1
            while pos > j
                _bubble!(steps, wires_, obj, pos - 1, pos)
                pos -= 1
            end
        end
    end
    isempty(steps) && return expr === nothing ? id(munit(syntax.Ob)) : expr
    tail = foldl(compose, steps)
    return expr === nothing ? tail : compose(expr, tail)
end

# `n` copies of `A` as a chain of binary copies.
function _mcopy_chain(A, n::Int)
    return n == 2 ? mcopy(A) : compose(mcopy(A), otimes(id(A), _mcopy_chain(A, n - 1)))
end

"""
    to_hom_expr(FreeMarkovCategory, d::BayesWiringDiagram) -> FreeMarkovCategory.Hom

The free Markov-category expression of a network's wiring diagram: Catlab's
`to_hom_expr` applied to the diagram with `Symbol` port and box values (object
generators named by variables, morphism generators by mechanisms), whose fan-out and
dangling ports become `mcopy` and `delete` through Catlab's junction normalisation.
Catlab's reduction cannot handle a box whose every output is discarded (it asserts
that a wire reaches an outer port), so such diagrams are handed to
[`wiring_expression`](@ref), which builds the same kind of expression directly. Both
evaluate, with [`free_generators`](@ref), to the kernel of the network:
`joint_distribution` for a closed network with every variable as output, and
`interpret` for an open network.
"""
function to_hom_expr(syntax::Module, d::BayesWiringDiagram)
    _all_boxes_reach_outputs(d) || return wiring_expression(d; syntax=syntax)
    return to_hom_expr(syntax, _symbolic(d))
end
