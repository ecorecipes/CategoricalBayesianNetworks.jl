@testset "total structural composition and name-safe compatibility" begin
    a = Open(bayesnet(:X => [:no, :yes]))
    @test interface_matches(output_space(a), input_space(a))
    @test_throws DuplicateNameError compose(a, a)
    aa = compose_structural(a, a)
    @test validate(aa) === nothing
    @test nparts(apex(aa), :Variable) == 2
    @test nparts(apex(aa), :Mechanism) == 2
    @test is_isomorphic(apex(aa), apex(otimes(a, a)))
    left = compose_structural(aa, a)
    right = compose_structural(a, aa)
    @test is_isomorphic(apex(left), apex(right))
    @test is_isomorphic(apex(compose_structural(id(dom(a)), a)), apex(a))
    @test is_isomorphic(apex(compose_structural(a, id(codom(a)))), apex(a))
    parallel = compose_structural(otimes(a, a), otimes(a, a))
    @test is_isomorphic(apex(parallel), apex(otimes(aa, aa)))
    @test nparts(apex(parallel), :Mechanism) == 4
    A, B = abiotic_open(), biotic_open()
    @test is_isomorphic(apex(compose_structural(A, B)), apex(compose(A, B)))
    @test input_space(compose_structural(A, B)) == input_space(A)
    @test output_space(compose_structural(A, B)) == output_space(B)
end

@testset "space references survive wiring and constrain connections" begin
    ref = NamedRef("habitat-space")
    p = VariablePort(:X, [:no, :yes], ref)
    @test p != VariablePort(:X, [:no, :yes])
    @test hash(p) == hash(VariablePort(:X, [:no, :yes], ref))
    bn = bayesnet(:X => [:no, :yes], :Y => [:low, :high];
                  mechanisms=[:Y => :X], space_refs=Dict(:X => ref))
    wd = to_wiring_diagram(bn)
    back = first(from_wiring_diagram(wd))
    @test space_ref(back, :X) == ref
    @test is_isomorphic(bn, back)
    @test copy(wd) == wd
    open_bn = bayesnet(:X => [:no, :yes]; closed=false, space_refs=Dict(:X => ref))
    copied = to_wiring_diagram(Open(open_bn; inputs=[:X], outputs=[:X, :X]))
    rebuilt, ins, outs = from_wiring_diagram(copied)
    @test space_ref(rebuilt, :X) == ref
    @test ins == [:X] && outs == [:X, :X]
    mismatch = BayesWiringDiagram([p], [VariablePort(:X, [:no, :yes], NamedRef("other"))])
    add_wire!(mismatch,
              Port(input_id(mismatch), OutputPort, 1) => Port(output_id(mismatch),
                                                              InputPort, 1))
    @test_throws WiringDiagramError from_wiring_diagram(mismatch)
    @test_throws WiringDiagramError wiring_expression(mismatch)
end

@testset "free expressions copy each repeated parent occurrence" begin
    bn = bayesnet(:A => [:a0, :a1], :B => [:b0, :b1], :Y => [:y0, :y1];
                  mechanisms=[:Y => (:B, :A, :B)])
    table = zeros(2, 2, 2, 2)
    for b1 in 1:2, a in 1:2, b2 in 1:2
        p = 0.1b1 + 0.2a + 0.05b2
        table[b1, a, b2, :] = [p, 1 - p]
    end
    m = bind_cpt(BayesModel(bn), [:A => [0.4, 0.6], :B => [0.3, 0.7], :Y => table])
    oracle = joint_distribution(m)
    @test categorical_joint(m) ≈ oracle
    wd = to_wiring_diagram(m)
    @test evaluate(wiring_expression(wd), free_generators(m)) ≈ oracle
    @test evaluate(to_hom_expr(FreeMarkovCategory, wd), free_generators(m)) ≈ oracle
    @test is_isomorphic(first(from_wiring_diagram(wd)), syntax(m))
end
