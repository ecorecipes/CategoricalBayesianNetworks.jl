@testset "Position-aware composition and actual colimit maps" begin
    CBN = CategoricalBayesianNetworks
    maps(leg, sort) = Vector{Int}(collect(CBN.components(leg)[sort]))

    function shuffled_leg(foot, leg, shuffle)
        if !shuffle
            return CBN.OpenACSetLeg(foot; Variable=maps(leg, :Variable),
                                    State=maps(leg, :State))
        end
        changed = VariableSpace()
        for v in parts(foot, :Variable)
            add_variable!(changed, variable_name(foot, v); states=Symbol[],
                          space_ref=space_ref(foot, v))
        end
        order = reverse(collect(parts(foot, :State)))
        for s in order
            add_state!(changed, subpart(foot, s, :state_variable),
                       subpart(foot, s, :state_name);
                       position=subpart(foot, s, :state_position))
        end
        return CBN.OpenACSetLeg(changed; Variable=maps(leg, :Variable),
                                State=maps(leg, :State)[order])
    end

    function shuffle_feet(o; input=false, output=false)
        return OpenBayesNet(apex(o),
                            shuffled_leg(input_space(o), left_leg(o), input),
                            shuffled_leg(output_space(o), right_leg(o), output))
    end

    A = Open(bayesnet(:Seed => [:low, :high], :Middle => [:a, :b, :c];
                      mechanisms=[:Middle => :Seed], closed=false);
             inputs=[:Seed], outputs=[:Middle, :Seed])
    B = Open(bayesnet(:Middle => [:a, :b, :c], :Seed => [:low, :high],
                      :Tail => [:off, :on];
                      mechanisms=[:Tail => (:Middle, :Seed)], closed=false);
             inputs=[:Middle, :Seed], outputs=[:Tail])
    a = shuffle_feet(A; input=true)
    b = shuffle_feet(B; input=true, output=true)
    a_before, b_before = deepcopy(a), deepcopy(b)
    @test validate(a) === nothing
    @test validate(b) === nothing
    @test interface_matches(output_space(a), input_space(b))
    @test output_space(a) != input_space(b)

    C, ia, ib = CBN._compose_structural_with_maps(a, b)
    @test C == compose_structural(a, b) == compose(a, b)
    @test input_space(C) == input_space(a)
    @test output_space(C) == output_space(b)
    @test subpart(input_space(C), :state_position) == [2, 1]
    @test subpart(output_space(C), :state_position) == [2, 1]
    generic = CBN.force(invoke(compose,
                               Tuple{CBN.StructuredCospan{L},
                                     CBN.StructuredCospan{L}} where {L},
                               A, B))
    @test apex(C) == apex(generic)
    @test canonicalize(apex(compose_structural(shuffle_feet(A; output=true), B))) ==
          canonicalize(apex(generic))
    @test a == a_before && b == b_before

    for (source, leg) in ((apex(a), ia), (apex(b), ib))
        @test CBN.is_natural(leg)
        @test dom(leg) == source && codom(leg) == apex(C)
        for sort in (:Variable, :State, :Mechanism, :Input)
            @test length(maps(leg, sort)) == nparts(source, sort)
        end
    end
    for sort in (:Variable, :State)
        @test maps(left_leg(C), sort) == maps(ia, sort)[maps(left_leg(a), sort)]
        @test maps(right_leg(C), sort) == maps(ib, sort)[maps(right_leg(b), sort)]
    end

    tail = zeros(3, 2, 2)
    for m in 1:3, s in 1:2
        tail[m, s, :] = [(m + 2s)/8, 1 - (m + 2s)/8]
    end
    ks = Dict(:Middle => cpt(axis(apex(A), :Seed), axis(apex(A), :Middle),
                             [0.5 0.25 0.25; 0.25 0.5 0.25]),
              :Tail => cpt([axis(apex(B), :Middle), axis(apex(B), :Seed)],
                           axis(apex(B), :Tail), tail))
    @test isapprox(interpret(C, ks), compose_kernel(interpret(a, ks), interpret(b, ks)))
    @test interpret(C, ks).table[1, :] == [0.46875, 0.75]
    @test canonicalize(apex(compose_structural(id(dom(a)), a))) == canonicalize(apex(a))
    @test canonicalize(apex(compose_structural(b, id(codom(b))))) == canonicalize(apex(b))

    D = Open(bayesnet(:Tail => [:off, :on], :Final => [:no, :yes];
                      mechanisms=[:Final => :Tail], closed=false);
             inputs=[:Tail], outputs=[:Final])
    @test canonicalize(apex(compose_structural(compose_structural(a, b), D))) ==
          canonicalize(apex(compose_structural(a, compose_structural(b, D))))

    T, ta, tb = CBN._otimes_with_maps(a, b)
    generic_tensor = CBN.force(invoke(otimes,
                                      Tuple{CBN.StructuredCospan{L},
                                            CBN.StructuredCospan{L}} where {L},
                                      a, b))
    @test T == otimes(a, b) == generic_tensor
    for (source, leg) in ((apex(a), ta), (apex(b), tb))
        @test CBN.is_natural(leg)
        @test dom(leg) == source && codom(leg) == apex(T)
        for sort in (:Variable, :State, :Mechanism, :Input)
            @test length(maps(leg, sort)) == nparts(source, sort)
            @test allunique(maps(leg, sort))
        end
    end

    @testset "right cocone maps need not be injective" begin
        repeated = Open(bayesnet(:X => [:low, :high]); outputs=[:X, :X])
        raw = BayesNet()
        x1 = add_variable!(raw, :X; states=[:low, :high])
        x2 = add_variable!(raw, :X; states=[:low, :high])
        y = add_variable!(raw, :Y; states=[:off, :on])
        mech = add_mechanism!(raw, y; inputs=[x1, x2])
        receiver = CBN._open(raw, [x1, x2], [y])
        result, left_map, right_map = CBN._compose_structural_with_maps(repeated, receiver)
        vr, sr = maps(right_map, :Variable), maps(right_map, :State)
        @test validate(result; unique_names=false) === nothing
        @test validate(apex(result); closed=true, unique_names=false) === nothing
        @test vr[x1] == vr[x2]
        @test sr[state_ids(raw, x1)] == sr[state_ids(raw, x2)]
        @test !allunique(vr) && !allunique(sr)
        @test allunique(maps(right_map, :Mechanism))
        @test allunique(maps(right_map, :Input))
        @test nparts(apex(result), :Variable) == 2
        @test nparts(apex(result), :State) == 4
        @test inputs(apex(result), maps(right_map, :Mechanism)[mech]) == [vr[x1], vr[x1]]
        @test CBN.is_natural(left_map) && CBN.is_natural(right_map)
    end
end
