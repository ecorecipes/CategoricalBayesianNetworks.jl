"""
Composition of open networks (SPEC §13): strict sequential `compose`, the convenient
`glue`, the tensor `otimes`, `oapply` over undirected wiring diagrams, and mechanism
`substitute`. Every operation is a pushout (or coproduct) of ACSets computed by Catlab;
the results are re-wrapped with freshly built feet and validated. Colimits may renumber
parts, but never reorder states or inputs, because the orders live in `state_position`
and `input_position` attributes.
"""

# Interface comparison
######################

# The first difference between variable `i` of `a` and variable `j` of `b`, as a
# `(what, left, right)` triple, or `nothing`.
function _variable_difference(a::AbstractVariableSpace, i::Integer,
                              b::AbstractVariableSpace, j::Integer; names::Bool=true)
    na, nb = variable_name(a, i), variable_name(b, j)
    names && na != nb && return (:variable_name, na, nb)
    sa, sb = _state_table(a, i), _state_table(b, j)
    sa == sb || return (:states, sa, sb)
    ra, rb = subpart(a, i, :space_ref), subpart(b, j, :space_ref)
    ra == rb || return (:space_ref, ra, rb)
    return nothing
end

# The first difference between two interfaces, as `(what, position, left, right)`.
function _interface_difference(a::AbstractVariableSpace, b::AbstractVariableSpace)
    na, nb = nparts(a, :Variable), nparts(b, :Variable)
    na == nb || return (:length, 0, variable_names(a), variable_names(b))
    for i in 1:na
        d = _variable_difference(a, i, b, i)
        d === nothing || return (d[1], i, d[2], d[3])
    end
    return nothing
end

"""
    interface_matches(a::VariableSpace, b::VariableSpace) -> Bool

Whether two interfaces agree exactly: the same number of variables, and at each
position the same variable name, the same states with the same positions, and the same
`space_ref`. This is the condition under which [`compose`](@ref) glues `codom(A)` to
`dom(B)`.
"""
function interface_matches(a::AbstractVariableSpace, b::AbstractVariableSpace)
    return _interface_difference(a, b) === nothing
end

# Pushouts
##########

# Pushout of two embeddings of the variable space on `ids_a` of `a` (with `ids_b` the
# matching variables of `b`, whose states must agree position by position).
function _pushout_along_maps(a::BayesNet, ids_a::AbstractVector{<:Integer}, b::BayesNet,
                             ids_b::AbstractVector{<:Integer})
    S, va, sa = _foot(a, ids_a)
    _, vb, sb = _foot(b, ids_b)
    length(sa) == length(sb) ||
        throw(InterfaceMismatchError(:states, 0, sa, sb, "pushout: state counts differ"))
    LS = BayesNet()
    copy_parts!(LS, S)
    fa = ACSetTransformation((Variable=va, State=sa), LS, a)
    fb = ACSetTransformation((Variable=vb, State=sb), LS, b)
    po = pushout[infer_acset_cat(a)](fa, fb)
    ia, ib = legs(po)
    return apex(po), ia, ib
end

function _pushout_along(a::BayesNet, ids_a::AbstractVector{<:Integer}, b::BayesNet,
                        ids_b::AbstractVector{<:Integer})
    P, ia, ib = _pushout_along_maps(a, ids_a, b, ids_b)
    return P, _variable_component(ia), _variable_component(ib)
end

# Name freshness is a convenience-wrapper policy, not a composability condition.
function _unique_named(bn::AbstractBayesNet)
    return allunique(variable_names(bn)) &&
           allunique(mechanism_names(bn))
end

# Validate a composite of `A` and `B`, demanding unique names when both pieces had them
# (SPEC section 11 item 12): silently returning a network with two variables of one name
# would only surface much later, in a name-based lookup.
function _validate_composite(o::OpenBayesNetCospan, pieces::AbstractBayesNet...)
    return validate(o; unique_names=all(_unique_named, pieces))
end

# Sequential composition
########################

"""
    compose(A::OpenBayesNet, B::OpenBayesNet) -> OpenBayesNet
    A ⋅ B

Strict sequential composition: the output interface of `A` must equal the input
interface of `B` position by position ([`interface_matches`](@ref)); otherwise an
`InterfaceMismatchError` names the first difference. The result is a Catlab
pushout of the two middle legs after aligning their position-equivalent feet, with
`inputs(A)` as inputs and `outputs(B)` as outputs [BaezCourser2020](@cite); it is
validated before being returned (with unique names when both pieces had them).
This name-safe compatibility wrapper can reject structurally composable pieces
whose unglued names collide. Use [`compose_structural`](@ref) for the total
structural operation on matching valid interfaces; it deliberately retains duplicate names.
Composing two causal theories by identifying the outputs of one with the free inputs of
the other is the operation of [Fong2012](@cite). Under the typed-interface rule
the pushout never produces two mechanisms for one variable; this is the machine-checked
theorem `OpenFinBayesNet.Composable.composeNet_target_injective` in
`proofs/BayesianNetworksProofs/Finite/Open.lean`, proved for the abstract finite model
of open networks rather than for the ACSet objects themselves.
"""
function compose(A::OpenBayesNetCospan, B::OpenBayesNetCospan)
    C = compose_structural(A, B)
    _validate_composite(C, apex(A), apex(B))
    return C
end

"""
    compose_structural(A::OpenBayesNet, B::OpenBayesNet) -> OpenBayesNet

Sequential pushout composition without a name-freshness restriction. Both
networks must satisfy the typed-interface rule and their interfaces must match
positionally, including names, ordered states and references. Unglued variables
and mechanisms remain distinct even when their names agree. The result is
validated structurally with `unique_names=false`.

Raw state-row numbering in the shared feet need not agree: the common interface
is aligned by variable position and `state_position`. The original outer feet
are retained, including their raw state-row numbering.

This is the composition underlying the structural-isomorphism category.
[`compose`](@ref) remains the name-safe compatibility wrapper. A result with
duplicate names must be accessed by part ids or suitably renamed before using
APIs requiring unique names; kernel references survive the pushout unchanged.
"""
function compose_structural(A::OpenBayesNetCospan, B::OpenBayesNetCospan)
    return first(_compose_structural_with_maps(A, B))
end

function _compose_structural_with_maps(A::OpenBayesNetCospan, B::OpenBayesNetCospan)
    validate(A; unique_names=false)
    validate(B; unique_names=false)
    d = _interface_difference(output_space(A), input_space(B))
    d === nothing ||
        throw(InterfaceMismatchError(d..., "compose: outputs(A) vs inputs(B)"))
    # A single position-ordered middle foot avoids imposing raw State-ID equality.
    P, ia, ib = _pushout_along_maps(apex(A), output_variables(A),
                                    apex(B), input_variables(B))
    cat = infer_acset_cat(P)
    cospan = Cospan(P, compose[cat](left_leg(A), ia), compose[cat](right_leg(B), ib))
    C = force(OpenBayesNetCospan(cospan, dom(A), codom(B)))
    validate(C; unique_names=false)
    return C, ia, ib
end

"""
    glue(A::OpenBayesNet, B::OpenBayesNet; along::Vector{Pair{Symbol,Symbol}}) -> OpenBayesNet

Glue selected outputs of `A` to selected inputs of `B`: each `a => b` in `along` names
an output variable of `A` and an input variable of `B`, which must carry the same states
(positions included) and `space_ref` but may differ in name (the glued variable keeps
the name it has in `A`); an `InterfaceMismatchError` reports the first pair
that does not agree, or a name that is not in the relevant interface. The two networks
are pushed out along the shared variable space, so the glued variables become one
variable each and everything else stays disjoint (variables are never merged because
their names coincide).

The result has inputs `inputs(A)` followed by the inputs of `B` that were not glued,
and outputs the outputs of `A` that were not glued followed by `outputs(B)`. It is
validated before being returned, with unique names when both pieces had them, so a
composite never silently carries two variables of one name. A pair `a => b` with
`a != b` whose name `a` is already used by another variable of `apex(B)` is refused
with a `NameClashError`: the rename would produce a duplicate rather than the
intended merge.

# Example

```jldoctest
julia> A = Open(bayesnet(:Climate => [:dry, :wet], :SoilMoisture => [:low, :high];
                         mechanisms = [:SoilMoisture => :Climate]);
                outputs = [:SoilMoisture]);

julia> B = Open(bayesnet(:SoilMoisture => [:low, :high], :Vegetation => [:sparse, :dense];
                         mechanisms = [:Vegetation => :SoilMoisture], closed = false);
                inputs = [:SoilMoisture], outputs = [:Vegetation]);

julia> C = glue(A, B; along = [:SoilMoisture => :SoilMoisture]);

julia> inputs(C), outputs(C), sort(variable_names(apex(C)))
(Symbol[], [:Vegetation], [:Climate, :SoilMoisture, :Vegetation])
```
"""
function glue(A::OpenBayesNetCospan, B::OpenBayesNetCospan;
              along::AbstractVector{<:Pair{Symbol,Symbol}})
    outA, inB = outputs(A), inputs(B)
    ia, ib = Int[], Int[]
    for (k, (a, b)) in enumerate(along)
        i = findall(==(a), outA)
        isempty(i) &&
            throw(InterfaceMismatchError(:missing_output, k, a, nothing,
                                         "glue: $a is not an output of A"))
        length(i) > 1 && throw(DuplicateNameError(:Variable, a, i))
        j = findall(==(b), inB)
        isempty(j) &&
            throw(InterfaceMismatchError(:missing_input, k, nothing, b,
                                         "glue: $b is not an input of B"))
        length(j) > 1 && throw(DuplicateNameError(:Variable, b, j))
        only(i) in ia &&
            throw(InterfaceMismatchError(:duplicate, k, a, b,
                                         "glue: output $a of A is glued more than once"))
        only(j) in ib &&
            throw(InterfaceMismatchError(:duplicate, k, a, b,
                                         "glue: input $b of B is glued more than once"))
        d = _variable_difference(output_space(A), only(i), input_space(B), only(j);
                                 names=false)
        d === nothing ||
            throw(InterfaceMismatchError(d[1], k, d[2], d[3], "glue: along[$k] = $a => $b"))
        push!(ia, only(i))
        push!(ib, only(j))
    end
    VA_out, VB_in = output_variables(A), input_variables(B)
    # A pushout cannot merge variables whose names differ, so the glued variables of B
    # take the names of their partners in A before gluing.
    apB = apex(B)
    if any(a != b for (a, b) in along)
        renamed = copy(variable_names(apB))
        for ((a, _), j) in zip(along, ib)
            renamed[VB_in[j]] = a
        end
        # Renaming must not collide with a variable of B that is not glued (or with
        # another renamed input): the pushout would merge nothing and the composite
        # would carry two variables of one name.
        for ((a, b), j) in zip(along, ib)
            a == b && continue
            count(==(a), renamed) == 1 ||
                throw(NameClashError(:Variable, a, b,
                                     "glue: along $a => $b"))
        end
        apB = deepcopy(apB)
        for (v, name) in zip(parts(apB, :Variable), renamed)
            set_subpart!(apB, v, :variable_name, name)
        end
    end
    P, mapA, mapB = _pushout_along(apex(A), VA_out[ia], apB, VB_in[ib])
    keep_a = setdiff(eachindex(outA), ia)
    keep_b = setdiff(eachindex(inB), ib)
    in_ids = vcat(mapA[input_variables(A)], mapB[VB_in[keep_b]])
    out_ids = vcat(mapA[VA_out[keep_a]], mapB[output_variables(B)])
    o = _open(P, in_ids, out_ids)
    _validate_composite(o, apex(A), apex(B))
    return o
end

# Tensor
########

"""
    otimes(A::OpenBayesNet, B::OpenBayesNet) -> OpenBayesNet
    A ⊗ B

Place two open networks side by side: the apex is the coproduct (disjoint union) of the
apexes and the interfaces are concatenated, `inputs(A)` then `inputs(B)` and likewise
for outputs. Variable and mechanism names are kept, so tensoring a network with itself
yields repeated names; the result is validated with `unique_names = false`.
"""
function otimes(A::OpenBayesNetCospan, B::OpenBayesNetCospan)
    return first(_otimes_with_maps(A, B))
end

function _otimes_with_maps(A::OpenBayesNetCospan, B::OpenBayesNetCospan)
    validate(A; unique_names=false)
    validate(B; unique_names=false)
    cat = infer_acset_cat(apex(A))
    cp = coproduct[cat](apex(A), apex(B))
    ia, ib = legs(cp)
    input_sum = coproduct[cat](dom(left_leg(A)), dom(left_leg(B)))
    output_sum = coproduct[cat](dom(right_leg(A)), dom(right_leg(B)))
    input_leg = copair[cat](input_sum,
                            compose[cat](left_leg(A), ia), compose[cat](left_leg(B), ib))
    output_leg = copair[cat](output_sum,
                             compose[cat](right_leg(A), ia), compose[cat](right_leg(B), ib))
    C = force(OpenBayesNetCospan(Cospan(apex(cp), input_leg, output_leg),
                                 otimes(dom(A), dom(B)), otimes(codom(A), codom(B))))
    validate(C; unique_names=false)
    return C, ia, ib
end

# Undirected wiring diagrams
############################

# The name a `@relation` diagram gives a junction, or `nothing` for a bare
# `UndirectedWiringDiagram`.
function _junction_name(uwd::UndirectedWiringDiagram, j::Integer)
    return has_subpart(uwd, :variable) ? Symbol(subpart(uwd, j, :variable)) : nothing
end

function _junction_suffix(uwd::UndirectedWiringDiagram, j::Integer)
    n = _junction_name(uwd, j)
    return n === nothing ? "" : " (:$n)"
end

# One leg per interface variable, inputs first, so that the network can sit in a box
# of an undirected wiring diagram.
function _unbundle(o::StructuredMulticospan{_OpenL})
    bn = apex(o)
    ids = Int[]
    for leg in legs(o)
        append!(ids, _variable_component(leg))
    end
    return OpenBayesNet(bn, (_leg(bn, [v]) for v in ids)...)
end

"""
    oapply(uwd::UndirectedWiringDiagram, nets::Vector{OpenBayesNet}; validate = true) -> OpenBayesNet
    oapply(uwd::UndirectedWiringDiagram, nets::Dict{Symbol,OpenBayesNet}; validate = true)

Compose open networks along an undirected wiring diagram (for example one written with
`@relation`). Box `i` receives `nets[i]` (or, for the dictionary form, the network
named like the box); its ports are the interface variables of the network, inputs
first, then outputs, and every port is connected to a junction. Networks whose ports
meet at a junction must agree there ([`interface_matches`](@ref) on the single
variable; an `InterfaceMismatchError` names the junction otherwise). The
result's apex is the colimit computed by Catlab's `oapply` for structured
multicospans; its inputs are the outer-port variables without a mechanism and its
outputs the remaining outer-port variables, in outer-port order.

An outer port on a junction that no box touches has no variable to stand for and is
refused with an `InterfaceMismatchError``(:missing_junction, ...)` naming the
junction.

Undirected diagrams cannot express the typed-interface rule, so it is checked
afterwards by [`validate_composition`](@ref) (skipped with `validate = false`): a
junction that receives two mechanism-bearing variables gives a
`DuplicateGeneratorError`, and cycles a `CyclicBayesNetError`.

# Example

```jldoctest
julia> A = Open(bayesnet(:Climate => [:dry, :wet], :SoilMoisture => [:low, :high];
                         mechanisms = [:SoilMoisture => :Climate]);
                outputs = [:SoilMoisture]);

julia> B = Open(bayesnet(:SoilMoisture => [:low, :high], :Vegetation => [:sparse, :dense];
                         mechanisms = [:Vegetation => :SoilMoisture], closed = false);
                inputs = [:SoilMoisture], outputs = [:Vegetation]);

julia> uwd = @relation (veg,) begin
           abiotic(soil)
           biotic(soil, veg)
       end;

julia> C = oapply(uwd, [A, B]);

julia> outputs(C), sort(variable_names(apex(C)))
([:Vegetation], [:Climate, :SoilMoisture, :Vegetation])
```
"""
function oapply(uwd::UndirectedWiringDiagram, nets::AbstractVector{<:OpenBayesNet};
                validate::Bool=true)
    nboxes(uwd) == length(nets) ||
        throw(ArgumentError("oapply: the diagram has $(nboxes(uwd)) boxes but $(length(nets)) networks were given"))
    unbundled = map(_unbundle, nets)
    junction_feet = Dict{Int,VariableSpace}()
    for (b, m) in zip(boxes(uwd), unbundled)
        ps = ports(uwd, b)
        length(ps) == length(feet(m)) ||
            throw(InterfaceMismatchError(:length, b, length(feet(m)), length(ps),
                                         "oapply: interface variables of network $b vs ports of box $b"))
        for (p, f) in zip(ps, feet(m))
            j = junction(uwd, p)
            if haskey(junction_feet, j)
                d = _interface_difference(junction_feet[j], f)
                d === nothing ||
                    throw(InterfaceMismatchError(d[1], j, d[3], d[4],
                                                 "oapply: junction $j (box $b, port $p)"))
            else
                junction_feet[j] = f
            end
        end
    end
    for p in parts(uwd, :OuterPort)
        j = junction(uwd, p; outer=true)
        haskey(junction_feet, j) ||
            throw(InterfaceMismatchError(:missing_junction, j, _junction_name(uwd, j),
                                         nothing,
                                         "oapply: outer port $p is wired to junction $j$(_junction_suffix(uwd, j)), which no box touches"))
    end
    R = oapply(uwd, unbundled, nothing)
    P = apex(R)
    outer = Int[only(_variable_component(leg)) for leg in legs(R)]
    in_ids = filter(v -> !has_mechanism(P, v), outer)
    out_ids = filter(v -> has_mechanism(P, v), outer)
    o = _open(P, in_ids, out_ids)
    validate && validate_composition(o)
    return o
end

function oapply(uwd::UndirectedWiringDiagram, nets::AbstractDict{Symbol,<:OpenBayesNet};
                kw...)
    names = Symbol.(subpart(uwd, :name))
    ordered = OpenBayesNet[haskey(nets, n) ? nets[n] :
                           throw(ArgumentError("oapply: no network for box :$n"))
                           for n in names]
    return oapply(uwd, ordered; kw...)
end

"""
    validate_composition(o::OpenBayesNet) -> Nothing

Post-hoc validation of a composite built without the typed-interface rule (the result
of [`oapply`](@ref)): the same checks as [`validate`](@ref validate(::CategoricalBayesianNetworks.OpenBayesNetCospan)), so a
junction that received two mechanism-bearing variables is reported as a
`DuplicateGeneratorError` and a cycle created by the wiring as a
`CyclicBayesNetError`, before the interface rules.
"""
validate_composition(o::OpenBayesNetCospan) = validate(o)

# Substitution
##############

"""
    substitute(bn::BayesNet, mech::Symbol => N::OpenBayesNet) -> BayesNet
    substitute(m::BayesModel, mech::Symbol => N::OpenBayesNet; note = "") -> BayesModel

Replace mechanism `mech` by the open network `N` (SPEC §13.3). `inputs(N)` must be
the parents of the mechanism in `input_position` order and `outputs(N)` its target,
with matching states and references (`InterfaceMismatchError` otherwise). The
mechanism and its inputs are removed and the network is pushed out with `apex(N)`
along the variable space on the parents and the target, so the hidden variables and
mechanisms of `N` are added while the interface of the containing network is
unchanged.

`N` is validated on entry, so a replacement built with `Open(...; validate = false)`
is rejected here: it is rule 3 of the typed-interface rule (every mechanism-free apex
variable is an input) that keeps the interface of the containing network unchanged, an
`N` carrying an extra exogenous variable being exactly what would add an input to it.
The hidden variables of `N` and the mechanisms it adds must not be named like a
variable or a remaining mechanism of `bn` (`NameClashError`), and the result is
validated (closed if `bn` was closed, with unique names when `bn` and `apex(N)` had
them).

On a `BayesModel` the rewrite is recorded as a `:substitute` event whose
`removed` record is the old mechanism and whose note lists the mechanisms of `N`; the
hidden variables of `N` receive spaces, and kernels for the new mechanisms are bound
afterwards with `bind_kernel`.
"""
function substitute(bn::BayesNet, sub::Pair{Symbol,<:OpenBayesNet})
    mech, N = sub
    _two_feet(N)
    validate(N)
    m = mechanism_id(bn, mech)
    t, ps = target(bn, m), inputs(bn, m)
    S_in, = _foot(bn, ps)
    d = _interface_difference(S_in, input_space(N))
    d === nothing ||
        throw(InterfaceMismatchError(d..., "substitute: parents of $mech vs inputs(N)"))
    S_out, = _foot(bn, [t])
    d = _interface_difference(S_out, output_space(N))
    d === nothing ||
        throw(InterfaceMismatchError(d..., "substitute: target of $mech vs outputs(N)"))
    closed = isempty(exogenous(bn))
    bn2 = deepcopy(bn)
    cascading_rem_part!(bn2, :Mechanism, m)
    _check_substitution_names(bn2, N)
    P, _, _ = _pushout_along(bn2, vcat(ps, t), apex(N),
                             vcat(input_variables(N), output_variables(N)))
    validate(P; closed=closed,
             unique_names=_unique_named(bn2) && _unique_named(apex(N)))
    return P
end

# The parts of `N` that the pushout adds to `bn` (the hidden variables, that is those
# outside the interface, and every mechanism) must not be named like a part of `bn`
# that survives: the pushout merges only the interface, so a shared name would give two
# variables or two mechanisms of that name.
function _check_substitution_names(bn::AbstractBayesNet, N::OpenBayesNetCospan)
    apN = apex(N)
    iface = Set{Int}(vcat(input_variables(N), output_variables(N)))
    taken = Set(variable_names(bn))
    for v in parts(apN, :Variable)
        v in iface && continue
        name = variable_name(apN, v)
        name in taken &&
            throw(NameClashError(:Variable, name, name,
                                 "substitute: hidden variable of the replacement"))
    end
    mtaken = Set(mechanism_names(bn))
    for m in mechanisms(apN)
        name = mechanism_name(apN, m)
        name in mtaken &&
            throw(NameClashError(:Mechanism, name, name,
                                 "substitute: mechanism of the replacement"))
    end
    return nothing
end

function substitute(m::BayesModel, sub::Pair{Symbol,<:OpenBayesNet};
                    note::AbstractString="")
    mech, N = sub
    bn = syntax(m)
    mid = mechanism_id(bn, mech)
    removed = mechanism_record(bn, mid)
    added_names = join(mechanism_names(apex(N)), ", ")
    text = isempty(note) ? "added mechanisms: $added_names" :
           "$note (added mechanisms: $added_names)"
    ev = ModelEvent(:substitute, variable_name(bn, target(bn, mid)), removed, nothing;
                    note=text)
    syn = substitute(bn, sub)
    return _with(m; syntax=syn, spaces=_complete_spaces(spaces(m), syn),
                 history=vcat(history(m), [ev]))
end
