"""
Open Bayesian networks as structured cospans (SPEC §13, revision note). An open network
is a `BayesNet` apex with two feet that are `VariableSpace`s (variables with
their states) and legs that embed the feet into the apex. The feet are built by copying
the named variables and their states, so gluing is never by name: it is the legs that
say which apex variable each interface variable is.

Catlab's `OpenACSetTypes` supports this multi-object interface because no hom leaves
`{Variable, State}` in `SchBayesNet`. The legs are stored in Catlab's "L-form", with
domain the discrete network `L(foot)` (a `BayesNet` without mechanisms), which is what
the pushouts of `compose` need.

Structured cospans as a way of making a category of "open" objects out of a category of
closed ones are due to [BaezCourser2020](@cite); a network whose interface variables
carry no mechanism is the ACSet rendering of a causal theory with inputs in the sense of
[Fong2012](@cite). The `Open`/`compose`/`oapply`/`substitute` layout follows the
AlgebraicJulia open-systems pattern of [Libkind2022](@cite).
"""

const OpenBayesNetObUntyped, OpenBayesNetUntyped = OpenACSetTypes(BayesNetUntyped,
                                                                  VariableSpaceUntyped)

@doc """
    OpenBayesNetObUntyped{Label, Position, Ref}

Object type of open networks with attribute types left open (a `StructuredCospanOb`
wrapping a `VariableSpaceUntyped`). See [`OpenBayesNetOb`](@ref).
""" OpenBayesNetObUntyped

@doc """
    OpenBayesNetUntyped{Label, Position, Ref}

Morphism type of open networks with attribute types left open (a
`StructuredMulticospan` with a `BayesNetUntyped` apex). See [`OpenBayesNet`](@ref).
""" OpenBayesNetUntyped

"""
    OpenBayesNetOb

An object of the category of open Bayesian networks: a `VariableSpace`
interface, wrapped as a Catlab `StructuredCospanOb`. `dom(o)` and `codom(o)` of an
[`OpenBayesNet`](@ref) return one; its `.ob` field is the `VariableSpace`, which
[`input_space`](@ref) and [`output_space`](@ref) return directly.
"""
const OpenBayesNetOb = OpenBayesNetObUntyped{Symbol,Int,KernelRef}

"""
    OpenBayesNet

An open Bayesian network: a Catlab structured (multi)cospan whose apex is a
`BayesNet` and whose feet are `VariableSpace`s. Build one with
[`Open`](@ref); combine with [`compose`](@ref), [`glue`](@ref), [`otimes`](@ref) and
[`oapply`](@ref); inspect with `apex`, [`inputs`](@ref), [`outputs`](@ref),
[`input_space`](@ref), [`output_space`](@ref), [`left_leg`](@ref) and
[`right_leg`](@ref).

Two-footed values (the results of `Open` and of the binary operations) are Catlab
`StructuredCospan`s; `oapply` handles multicospans with one leg per port internally.
"""
const OpenBayesNet = OpenBayesNetUntyped{Symbol,Int,KernelRef}

_discrete_functor(::Type{StructuredMulticospan{L}}) where {L} = L

# The functor L: VariableSpace -> BayesNet behind `OpenBayesNet`, and the two-footed
# subtype on which `compose` and `otimes` are specialised.
const _OpenL = _discrete_functor(OpenBayesNet)
const OpenBayesNetCospan = StructuredCospan{_OpenL}

# Catlab's default `munit` is `FinSet(0)`, which only works for single-object
# interfaces; the unit of our interface is the empty variable space.
munit(::Type{OpenBayesNetOb}) = OpenBayesNetOb(VariableSpace())

# Feet and legs
###############

# The variable space on the apex variables `ids` (in that order, with their states in
# position order) together with the apex part ids of each foot variable and state.
function _foot(bn::AbstractBayesNet, ids::AbstractVector{<:Integer})
    vs = VariableSpace()
    vmap, smap = Int[], Int[]
    for v in ids
        nv = add_part!(vs, :Variable; variable_name=variable_name(bn, v),
                       space_ref=subpart(bn, v, :space_ref))
        push!(vmap, Int(v))
        for s in state_ids(bn, v)
            add_part!(vs, :State; state_variable=nv, state_name=subpart(bn, s, :state_name),
                      state_position=subpart(bn, s, :state_position))
            push!(smap, s)
        end
    end
    return vs, vmap, smap
end

function _leg(bn::AbstractBayesNet, ids::AbstractVector{<:Integer})
    vs, vmap, smap = _foot(bn, ids)
    return OpenACSetLeg(vs; Variable=vmap, State=smap)
end

# An open network with feet on the given apex variable ids, in R-form.
function _open(bn::BayesNet, in_ids::AbstractVector{<:Integer},
               out_ids::AbstractVector{<:Integer})
    return OpenBayesNet(bn, _leg(bn, in_ids), _leg(bn, out_ids))
end

"""
    Open(bn::BayesNet; inputs = Symbol[], outputs = Symbol[], validate = true) -> OpenBayesNet
    Open(bn::BayesNet, inputs, outputs; validate = true)

Make `bn` an open network with the named variables as input and output interfaces, in
the given order. Each foot is a `VariableSpace` copying the variables' names,
references and states (with positions); the legs map foot variables and states to the
apex parts they were copied from. Variable names may repeat in `outputs` (an implicit
copy) but not in `inputs`.

The result is a structured cospan in the sense of [BaezCourser2020](@cite): the apex is
the network and the feet are its interfaces. An input variable carries no mechanism, so
an open network is a causal theory with free inputs [Fong2012](@cite).

With `validate = true` the typed-interface rule is checked (see
[`validate`](@ref validate(::CategoricalBayesianNetworks.OpenBayesNetCospan))) and the first violation thrown.

# Example

```jldoctest
julia> A = Open(bayesnet(:Climate => [:dry, :wet], :Irrigation => [:none, :high],
                         :SoilMoisture => [:low, :medium, :high];
                         mechanisms = [:SoilMoisture => (:Climate, :Irrigation)],
                         closed = false);
                inputs = [:Climate, :Irrigation], outputs = [:SoilMoisture]);

julia> inputs(A), outputs(A)
([:Climate, :Irrigation], [:SoilMoisture])
```
"""
function Open(bn::BayesNet; inputs::AbstractVector{Symbol}=Symbol[],
              outputs::AbstractVector{Symbol}=Symbol[], validate::Bool=true)
    in_ids = [variable_id(bn, n) for n in inputs]
    out_ids = [variable_id(bn, n) for n in outputs]
    o = _open(bn, in_ids, out_ids)
    validate && _validate_open(o)
    return o
end

function Open(bn::BayesNet, inputs::AbstractVector{Symbol}, outputs::AbstractVector{Symbol};
              validate::Bool=true)
    return Open(bn; inputs=inputs, outputs=outputs, validate=validate)
end

# Accessors
###########

function _two_feet(o::StructuredMulticospan{_OpenL})
    return length(feet(o)) == 2 ||
           throw(ArgumentError("expected an open network with two feet (inputs and outputs), got $(length(feet(o))) legs"))
end

"""
    input_space(o::OpenBayesNet) -> VariableSpace

The input interface (left foot) of `o`.
"""
input_space(o::OpenBayesNetCospan) = first(feet(o))

"""
    output_space(o::OpenBayesNet) -> VariableSpace

The output interface (right foot) of `o`.
"""
output_space(o::OpenBayesNetCospan) = last(feet(o))

"""
    inputs(o::OpenBayesNet) -> Vector{Symbol}

Names of the input variables of `o`, in interface order.
"""
inputs(o::OpenBayesNetCospan) = variable_names(input_space(o))

"""
    outputs(o::OpenBayesNet) -> Vector{Symbol}

Names of the output variables of `o`, in interface order.
"""
outputs(o::OpenBayesNetCospan) = variable_names(output_space(o))

"""
    left_leg(o::OpenBayesNet) -> ACSetTransformation

The leg embedding the input interface into the apex (Catlab's `left`). Its `Variable`
and `State` components map foot parts to apex parts.
"""
left_leg(o::OpenBayesNetCospan) = left(o)

"""
    right_leg(o::OpenBayesNet) -> ACSetTransformation

The leg embedding the output interface into the apex (Catlab's `right`).
"""
right_leg(o::OpenBayesNetCospan) = right(o)

_variable_component(leg) = Vector{Int}(collect(components(leg)[:Variable]))
_state_component(leg) = Vector{Int}(collect(components(leg)[:State]))

"""
    input_variables(o::OpenBayesNet) -> Vector{Int}

Apex part ids of the input variables, in interface order.
"""
input_variables(o::OpenBayesNetCospan) = _variable_component(left(o))

"""
    output_variables(o::OpenBayesNet) -> Vector{Int}

Apex part ids of the output variables, in interface order.
"""
output_variables(o::OpenBayesNetCospan) = _variable_component(right(o))

function Base.show(io::IO, o::StructuredMulticospan{_OpenL})
    bn = apex(o)
    print(io, "OpenBayesNet(", nparts(bn, :Variable), " variables, ",
          nparts(bn, :Mechanism), " mechanisms; ")
    if length(feet(o)) == 2
        print(io, inputs(o), " -> ", outputs(o))
    else
        print(io, length(feet(o)), " legs")
    end
    return print(io, ")")
end

# Typed-interface rule
######################

# Foot variables whose image under `leg` does not carry the same name, reference and
# states (with positions), plus their ids.
function _leg_mismatches(leg, foot::VariableSpace, bn::AbstractBayesNet)
    V, S = _variable_component(leg), _state_component(leg)
    bad = Int[]
    for v in parts(foot, :Variable)
        w = V[v]
        ok = _in_range(bn, :Variable, w) &&
             variable_name(foot, v) == variable_name(bn, w) &&
             subpart(foot, v, :space_ref) == subpart(bn, w, :space_ref)
        if ok
            fs = state_ids(foot, v)
            images = [S[s] for s in fs]
            ok = allunique(images) && length(images) == nstates(bn, w) &&
                 all(_in_range(bn, :State, t) && subpart(bn, t, :state_variable) == w &&
                     subpart(bn, t, :state_name) == subpart(foot, s, :state_name) &&
                     subpart(bn, t, :state_position) == subpart(foot, s, :state_position)
                     for (s, t) in zip(fs, images))
        end
        ok || push!(bad, v)
    end
    return bad
end

# Rules 1 to 3 of the typed-interface rule for the variables `in_ids` of `bn` taken as
# the input interface, appending one `InterfaceError` per violation to `errs`: rule 2
# (the interface is injective, that is `in_ids` has no repetition), rule 1 (no input
# carries a mechanism) and rule 3 (every mechanism-free variable is an input), in that
# order. `label(positions)` turns the positions in `in_ids` that repeat into the
# `(names, ids)` pair rule 2 reports, which is what lets an open network report its foot
# and a wiring diagram its apex. Shared by `validation_errors(::OpenBayesNet)` and by
# `to_wiring_diagram`, so both read the rules from one place.
function _check_interface_rules!(errs, bn::AbstractBayesNet,
                                 in_ids::AbstractVector{<:Integer}, label)
    seen = Dict{Int,Int}()
    dup = Int[]
    for (i, w) in enumerate(in_ids)
        haskey(seen, w) ? push!(dup, i) : (seen[w] = i)
    end
    if !isempty(dup)
        names, ids = label(dup)
        push!(errs, InterfaceError(2, names, ids))
    end
    with_mech = filter(w -> has_mechanism(bn, w), unique(in_ids))
    isempty(with_mech) ||
        push!(errs, InterfaceError(1, variable_name.(Ref(bn), with_mech), with_mech))
    not_input = filter(v -> !(v in keys(seen)), exogenous(bn))
    isempty(not_input) ||
        push!(errs, InterfaceError(3, variable_name.(Ref(bn), not_input), not_input))
    return errs
end

function _check_interface!(errs, o::OpenBayesNetCospan)
    bn = apex(o)
    fin, fout = input_space(o), output_space(o)
    # Rule 5: legs natural and attribute-preserving.
    natural = true
    for (leg, foot) in ((left(o), fin), (right(o), fout))
        bad = _leg_mismatches(leg, foot, bn)
        if !isempty(bad) || !is_natural(leg)
            isempty(bad) && (bad = collect(parts(foot, :Variable)))
            push!(errs, InterfaceError(5, variable_name.(Ref(foot), bad), bad))
            natural = false
        end
    end
    natural || return
    # Rules 1 to 3, with repeated inputs reported by their position in the foot.
    _check_interface_rules!(errs, bn, _variable_component(left(o)),
                            dup -> (variable_name.(Ref(fin), dup), dup))
    return
end

"""
    validation_errors(o::OpenBayesNet; unique_names = false) -> Vector{Exception}

All problems of the open network `o`: the structural errors of its apex (see
`BayesianNetworks.validation_errors`, always with `closed = false`; a cycle
is rule 4 of the typed-interface rule) followed by the violations of the remaining
typed-interface rules as `InterfaceError`s: rule 5 (legs natural and
attribute-preserving), rule 2 (input leg injective), rule 1 (inputs have no mechanism)
and rule 3 (every exogenous apex variable is an input). Rules 1 to 3 are only checked
when rule 5 holds.
"""
function validation_errors(o::OpenBayesNetCospan; unique_names::Bool=false)
    errs = validation_errors(apex(o); closed=false, unique_names=unique_names)
    any(e -> e isa DanglingReferenceError, errs) && return errs
    _check_interface!(errs, o)
    return errs
end

"""
    validate(o::OpenBayesNet; unique_names = false) -> Nothing

Throw the first entry of [`validation_errors`](@ref validation_errors(::CategoricalBayesianNetworks.OpenBayesNetCospan)), if any. Under the
typed-interface rule, pushout composition preserves "at most one mechanism per
variable": the closure theorem `OpenFinBayesNet.Composable.composeNet_target_injective`
in `proofs/BayesianNetworksProofs/Finite/Open.lean`, machine-checked for the abstract
finite model of open networks (`compose_input_exogenous`, `compose_exogenous_input` and
`composeTopo` give the other clauses, acyclicity derived rather than assumed). The
correspondence between that model and these ACSets is documentation, not a theorem,
which is why every composite is validated again here.
"""
function validate(o::OpenBayesNetCospan; kw...)
    errs = validation_errors(o; kw...)
    isempty(errs) || throw(first(errs))
    return nothing
end

_validate_open(o::OpenBayesNetCospan) = validate(o)

"""
    isvalid(o::OpenBayesNet; unique_names = false) -> Bool

Whether [`validation_errors`](@ref validation_errors(::CategoricalBayesianNetworks.OpenBayesNetCospan)) is empty.
"""
Base.isvalid(o::OpenBayesNetCospan; kw...) = isempty(validation_errors(o; kw...))
