"""
The categorical route to a model's joint distribution and the finite-stochastic
semantics of an open network (SPEC §5, §13, §55.5, §61). Both give the same numbers as
the brute-force evaluators of `BayesianNetworks.jl`, without enumerating the joint
states in the categorical case: `to_free_expression` turns the model into a
`FreeMarkovCategory` expression that MarkovCategories' functor interprets in FinStoch.

The shared helpers (`_factors`, `_product`, `_joint_atol`, `DEFAULT_MAX_STATES`) are
`BayesianNetworks.jl`'s; they need only kernels.
"""

# Categorical evaluation (Proposition 1)
########################################

const _Free = FreeMarkovCategory

_free_tensor(objs) = isempty(objs) ? munit(_Free.Ob) : foldl(otimes, objs)

"""
    to_free_expression(m::BayesModel) -> FreeMarkovCategory.Hom

The string diagram of a closed model as a `FreeMarkovCategory` expression
`I → X_1 ⊗ ... ⊗ X_n` (variables in topological order), built from one object
generator per variable (named by the variable) and one morphism generator per mechanism
(named by the mechanism, `⊗ parents → target`, parents in `input_position` order), with
`mcopy`, `braid`, `otimes` and `compose`. Only the syntax is needed; bind the generators
with [`free_generators`](@ref) and evaluate with [`categorical_joint`](@ref).

Construction ("keep everything"): the expression is built one variable at a time. After
`k` variables the expression is a state `I → X_1 ⊗ ... ⊗ X_k` with one wire per
variable. To add `X_{k+1}` with parents `P_1, ..., P_j`:

1. copy the wires of the parents (`mcopy(P_i)`, `id` on the others), so each parent
   has a second wire right next to its first;
2. move the copies to the right end with adjacent `braid`s, taking the parents in
   `input_position` order so that the copies end up as `P_1 ⊗ ... ⊗ P_j`;
3. apply `id(X_1 ⊗ ... ⊗ X_k) ⊗ κ` where `κ : P_1 ⊗ ... ⊗ P_j → X_{k+1}` is the
   mechanism's generator (for a root, `κ : I → X_{k+1}`).

Nothing is discarded, so the final state is the full joint. Mechanism names must not
coincide with variable names (`DuplicateNameError`).

The expression is the string diagram of the network in the Markov-category sense of
[Fritz2020](@cite): the explicit `mcopy` nodes are the fan-out that a directed acyclic
graph leaves implicit.

Those three steps are one box of [`wiring_expression`](@ref), which this function calls
on [`to_wiring_diagram`](@ref)`(m; outputs = topological order)`: the two builders are
one algorithm, reached from the syntax and from a diagram.
"""
function to_free_expression(m::BayesModel)
    bn = m.syntax
    validate(bn; closed=true, unique_names=true)
    order = topological_order(bn)
    vnames = Set(variable_names(bn))
    for v in order
        mname = mechanism_name(bn, mechanism_of(bn, v))
        mname in vnames &&
            throw(DuplicateNameError(:Generator, mname, [v, mechanism_of(bn, v)]))
    end
    # The three steps are exactly what `wiring_expression` does for every box of a
    # diagram, so the closed model is handed to it as the diagram with no inputs and
    # every variable as an output, in topological order.
    return wiring_expression(to_wiring_diagram(bn;
                                               outputs=Symbol[variable_name(bn, v)
                                                              for v in order]))
end

"""
    free_generators(m::BayesModel) -> Dict{Symbol, Any}

The interpretation of the generators of [`to_free_expression`](@ref)`(m)` in FinStoch:
each variable name to its `space` and each mechanism name to its
`kernel`.
"""
function free_generators(m::BayesModel)
    bn = m.syntax
    gens = Dict{Symbol,Any}()
    for v in variables(bn)
        gens[variable_name(bn, v)] = space(m, variable_name(bn, v))
    end
    for mech in mechanisms(bn)
        gens[mechanism_name(bn, mech)] = kernel(m, variable_name(bn, target(bn, mech)))
    end
    return gens
end

"""
    categorical_joint(m::BayesModel; atol = DEFAULT_ATOL) -> FiniteKernel

The joint distribution of a closed model computed categorically:
`evaluate(to_free_expression(m), free_generators(m))`, that is, the free expression
interpreted in FinStoch by MarkovCategories' functor, with no enumeration of assignments.
Proposition 1 (SPEC §5, §61) states that this equals `joint_distribution`; the
test suite checks it on every example and on random networks.
"""
function categorical_joint(m::BayesModel; atol::Real=DEFAULT_ATOL)
    validate(m; closed=true, unique_names=true, semantics=true, atol=atol)
    return evaluate(to_free_expression(m), free_generators(m))
end

# Open networks (Propositions 2 and 3)
######################################

"""
    interpret(o::OpenBayesNet, kernels; max_states = 1_000_000, atol = DEFAULT_ATOL) -> FiniteKernel
    interpret(o::OpenBayesNet, m::BayesModel; kwargs...)

The finite-stochastic semantics `⟦o⟧ : ⊗ inputs → ⊗ outputs` of an open network: the
product of the apex's mechanism kernels, summed over every apex variable that is not an
output, as a kernel from the input interface (exogenous under the typed-interface rule)
to the output interface. Inputs listed as outputs pass through and an output listed
twice is copied, as in the wiring. `kernels` is a dictionary keyed by
`KernelRef` (the `kernels` of a model, whose keys survive composition because
`kernel_ref` is an attribute of the apex) or by target variable name; a
`BayesModel` supplies its `kernels`. Every mechanism must resolve
(`MissingKernelError`) and fit (`KernelBindingError`).

Summing out the apex variables that are not outputs is categorical marginalisation, the
operation [LorenzinZanasi2025](@cite) analyse as the categorical form of variable
elimination.

Propositions 2 and 3 (SPEC §55.5): `interpret(compose(A, B)) ≈ compose(interpret(A),
interpret(B))` and `interpret(otimes(A, B)) ≈ otimes(interpret(A), interpret(B))`.
"""
function interpret(o::OpenBayesNetCospan, lookup; max_states::Integer=DEFAULT_MAX_STATES,
                   atol::Real=DEFAULT_ATOL)
    validate(o)
    bn = apex(o)
    in_ids, out_ids = input_variables(o), output_variables(o)
    ids = variables(bn)
    n = prod(Int128[nstates(bn, v) for v in ids]; init=Int128(1))
    n <= max_states || throw(ModelTooLargeError(Int(min(n, typemax(Int))), max_states))
    pos = Dict{Int,Int}(v => i for (i, v) in enumerate(ids))
    dims = Tuple(nstates(bn, v) for v in ids)
    factors = _factors(bn, lookup, pos; atol=atol)
    X = FiniteSpace(FiniteAxis[axis(bn, v) for v in in_ids])
    Y = FiniteSpace(FiniteAxis[axis(bn, v) for v in out_ids])
    T = zeros(Float64, (size(Y)..., size(X)...))
    sel = Int[pos[v] for v in vcat(out_ids, in_ids)]
    for ci in CartesianIndices(dims)
        p = _product(factors, ci)
        p == 0 && continue
        T[ntuple(j -> ci[sel[j]], length(sel))...] += p
    end
    return FiniteKernel(X, Y, T; atol=_joint_atol(atol, length(factors)))
end

interpret(o::OpenBayesNetCospan, m::BayesModel; kw...) = interpret(o, m.kernels; kw...)
