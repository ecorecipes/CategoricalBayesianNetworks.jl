using Random

# Property tests over random small DAGs (SPEC section 56), for the categorical layer:
# Proposition 1 (`categorical_joint` equals the brute-force joint) and Propositions 2
# and 3 (`interpret` is functorial for `compose` and `otimes`). The `random_model`
# generator is the same one `BayesianNetworks.jl` uses.

function random_model(rng::AbstractRNG; nvars::Integer=rand(rng, 2:5),
                      max_states::Integer=3,
                      max_parents::Integer=2)
    names_ = [Symbol("V", i) for i in 1:nvars]
    vars = [x => [Symbol(x, "_", j) for j in 1:rand(rng, 2:max_states)] for x in names_]
    mechs = Pair{Symbol,Any}[]
    for i in 2:nvars
        k = rand(rng, 0:min(max_parents, i - 1))
        ps = shuffle(rng, names_[1:(i - 1)])[1:k]   # random parent order too
        push!(mechs, names_[i] => Tuple(ps))
    end
    bn = bayesnet(vars...; mechanisms=mechs)
    m = BayesModel(bn)
    for x in names_
        m = bind_kernel(m, x => random_kernel(rng, parent_space(m, x), space(m, x)))
    end
    return m
end

@testset "Random networks, categorically" begin
    rng = MersenneTwister(20240906)
    @testset "Proposition 1 on random models" begin
        for _ in 1:25
            m = random_model(rng)
            bn = syntax(m)
            J = joint_distribution(m)
            @test categorical_joint(m) ≈ J
            x = rand(rng, variable_names(bn))
            s = rand(rng, states(bn, x))
            md = do_intervention(m, x => s)
            @test categorical_joint(md) ≈ joint_distribution(md)
        end
    end

    @testset "open-network compositionality on random pieces" begin
        for trial in 1:10
            m = random_model(rng; nvars=4)
            bn = syntax(m)
            order = variable_name.(Ref(bn), topological_order(bn))
            # Split at a variable c: A generates order[1:i] and exports c = order[i];
            # B takes c as input and generates the rest, if they only depend on c and
            # on each other (otherwise skip the trial).
            i = rand(rng, 1:(length(order) - 1))
            c = order[i]
            headn, tailn = order[1:i], order[(i + 1):end]
            ok = all(all(variable_name(bn, p) in vcat([c], tailn) for p in parents(bn, y))
                     for y in tailn)
            ok || continue
            refs = Dict(x => kernel_ref(bn, mechanism_of(bn, x)) for x in order)
            A = Open(bayesnet([x => states(bn, x) for x in headn]...;
                              mechanisms=[x => Tuple(variable_name.(Ref(bn),
                                                                    parents(bn, x)))
                                          for x in headn],
                              kernel_refs=refs); outputs=[c])
            B = Open(bayesnet([x => states(bn, x) for x in vcat([c], tailn)]...;
                              mechanisms=[x => Tuple(variable_name.(Ref(bn),
                                                                    parents(bn, x)))
                                          for x in tailn], closed=false, kernel_refs=refs);
                     inputs=[c], outputs=[last(tailn)])
            kA, kB = interpret(A, m), interpret(B, m)
            @test interpret(compose(A, B), m) ≈ compose(kA, kB)
            @test interpret(otimes(A, B), m) ≈ otimes(kA, kB)
            @test compose(kA, kB) ≈ marginal(m, last(tailn))
        end
    end
end
