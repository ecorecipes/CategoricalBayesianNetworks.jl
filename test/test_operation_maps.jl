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

        table = zeros(2, 2, 2)
        table[1, 1, :] = [7/8, 1/8]
        table[1, 2, :] = [0.0, 1.0]
        table[2, 1, :] = [1.0, 0.0]
        table[2, 2, :] = [1/4, 3/4]
        lookup = Dict(:X => cpt(axis(apex(repeated), :X), [1/4, 3/4]),
                      :Y => cpt([axis(raw, x1), axis(raw, x2)], axis(raw, y), table))
        shuffled = shuffle_feet(receiver; input=true, output=true)
        actual = interpret(compose_structural(repeated, shuffled), lookup)
        @test actual ≈ compose_kernel(interpret(repeated, lookup), interpret(shuffled, lookup))
        @test actual.table == [13/32, 19/32]
    end

    @testset "distinct hidden generators survive colliding names" begin
        for same_variable_name in (true, false)
            left_bn, right_bn = BayesNet(), BayesNet()
            s = add_variable!(left_bn, :Seed; states=[:low, :high])
            hl = add_variable!(left_bn, :Hidden; states=[:low, :high])
            mid = add_variable!(left_bn, :Middle; states=[:low, :high])
            lh = add_mechanism!(left_bn, hl; name=:Shared, kernel_ref=NamedRef("left-hidden"))
            add_mechanism!(left_bn, mid; inputs=[s, hl], kernel_ref=NamedRef("left-middle"))
            rm = add_variable!(right_bn, :Middle; states=[:low, :high])
            rs = add_variable!(right_bn, :Seed; states=[:low, :high])
            hr = add_variable!(right_bn, same_variable_name ? :Hidden : :OtherHidden; states=[:low, :high])
            y = add_variable!(right_bn, :End; states=[:low, :high])
            rh = add_mechanism!(right_bn, hr; name=:Shared, kernel_ref=NamedRef("right-hidden"))
            add_mechanism!(right_bn, y; inputs=[rm, hr], kernel_ref=NamedRef("right-end"))
            left = shuffle_feet(CBN._open(left_bn, [s], [mid, s]); input=true)
            right = shuffle_feet(CBN._open(right_bn, [rm, rs], [y, rs, y]); input=true, output=true)
            before = deepcopy((left, right))
            @test_throws DuplicateNameError compose(left, right)
            composite, il, ir = CBN._compose_structural_with_maps(left, right)
            @test validate(composite) === nothing
            @test nparts(apex(composite), :Variable) == 5
            @test nparts(apex(composite), :Mechanism) == 4
            @test maps(il, :Variable)[hl] != maps(ir, :Variable)[hr]
            @test maps(il, :Mechanism)[lh] != maps(ir, :Mechanism)[rh]
            @test CBN.is_natural(il) && CBN.is_natural(ir)
            @test input_space(composite) == input_space(left)
            @test output_space(composite) == output_space(right)

            ltab, rtab = zeros(2, 2, 2), zeros(2, 2, 2)
            for i in 1:2, h in 1:2
                ltab[i, h, :] = [(8 - 2i - h)/8, (2i + h)/8]
                rtab[i, h, :] = [(8 - i - 2h)/8, (i + 2h)/8]
            end
            lookup = Dict{KernelRef,FiniteKernel}(
                NamedRef("left-hidden") => cpt(axis(left_bn, hl), [1/4, 3/4]),
                NamedRef("left-middle") => cpt([axis(left_bn, s), axis(left_bn, hl)],
                                               axis(left_bn, mid), ltab),
                NamedRef("right-hidden") => cpt(axis(right_bn, hr), [3/4, 1/4]),
                NamedRef("right-end") => cpt([axis(right_bn, rm), axis(right_bn, hr)],
                                            axis(right_bn, y), rtab))
            actual = interpret(composite, lookup)
            @test actual ≈ compose_kernel(interpret(left, lookup), interpret(right, lookup))
            for state in 1:2, out in 1:2, passed in 1:2, copied in 1:2
                expected = passed == state && copied == out ?
                    sum([1//4, 3//4][a] * Rational{BigInt}(ltab[state, a, m]) *
                        [3//4, 1//4][b] * Rational{BigInt}(rtab[m, b, out])
                        for a in 1:2, b in 1:2, m in 1:2) : 0//1
                @test actual.table[out, passed, copied, state] == Float64(expected)
            end
            @test (left, right) == before
        end
    end
end
