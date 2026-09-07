using Random

# The kernels of a model keyed by target name, so that open sub-networks built without
# references can be interpreted with them.
function kernels_by_name(m::BayesModel)
    bn = syntax(m)
    return Dict{Symbol,FiniteKernel}(variable_name(bn, target(bn, mech)) => kernel(m,
                                                                                   variable_name(bn,
                                                                                                 target(bn,
                                                                                                        mech)))
                                     for mech in mechanisms(bn))
end

# Generators for an expression over the variables and mechanisms of `bn`, read from `m`.
function generators_from(m::BayesModel, bn::AbstractBayesNet)
    gens = Dict{Symbol,Any}(x => space(m, x) for x in variable_names(bn))
    for mech in mechanisms(bn)
        gens[mechanism_name(bn, mech)] = kernel(m, variable_name(bn, target(bn, mech)))
    end
    return gens
end

@testset "Wiring diagrams" begin
    m = reference_habitat_model()
    ref = syntax(m)
    order = variable_name.(Ref(ref), topological_order(ref))

    @testset "port and box values" begin
        p = VariablePort(:X, [:a, :b])
        @test p == VariablePort(:X, [:a, :b])
        @test p != VariablePort(:X, [:b, :a])
        @test hash(p) == hash(VariablePort(:X, [:a, :b]))
        @test VariablePort(ref, :Climate) == VariablePort(:Climate, [:dry, :normal, :wet])
        @test VariablePort(ref, 1) == VariablePort(ref, :Climate)
        b = MechanismBox(:m, NamedRef("k"))
        @test b == MechanismBox(:m, NamedRef("k"))
        @test b != MechanismBox(:m, NoRef())
        @test hash(b) == hash(MechanismBox(:m, NamedRef("k")))
        @test sprint(show, p) == "X{a,b}"
        @test sprint(show, b) == "m"
    end

    @testset "to_wiring_diagram" begin
        d = to_wiring_diagram(ref)
        @test d isa BayesWiringDiagram
        @test d isa WiringDiagram{ThMarkovCategory.Meta.T}
        @test isempty(input_ports(d))
        @test [p.name for p in output_ports(d)] == order
        @test nboxes(d) == 7
        @test nwires(d) == nparts(ref, :Input) + 7
        # Boxes follow the topological order of their targets.
        @test [box(d, b).value.name for b in box_ids(d)] ==
              [Symbol(x, "_mechanism") for x in order]
        veg = box(d,
                  findfirst(b -> box(d, b).value.name == :Vegetation_mechanism,
                            box_ids(d)))
        @test input_ports(veg) ==
              [VariablePort(ref, :SoilMoisture), VariablePort(ref, :GrazingPressure)]
        @test output_ports(veg) == [VariablePort(ref, :Vegetation)]
        @test veg.value.kernel_ref == NamedRef("Vegetation_mechanism")
        # SoilMoisture fans out: to Vegetation and to the outer output port.
        sm = findfirst(b -> box(d, b).value.name == :SoilMoisture_mechanism, box_ids(d))
        outs = out_wires(d, Port(sm, OutputPort, 1))
        @test length(outs) == 2
        @test Set(w.target.box for w in outs) ==
              Set([output_id(d), findfirst(b -> box(d, b) == veg, box_ids(d))])
        # A model gives the same diagram; copy keeps the type.
        @test to_wiring_diagram(m) == d
        @test copy(d) == d && copy(d) isa BayesWiringDiagram
        # Chosen outputs, with repetition and pass-through inputs.
        d2 = to_wiring_diagram(ref; outputs=[:Occupancy, :Climate, :Occupancy])
        @test [p.name for p in output_ports(d2)] == [:Occupancy, :Climate, :Occupancy]
        @test nboxes(d2) == 7
        @test nwires(d2) == nparts(ref, :Input) + 3
        # Open networks: the feet are the outer ports.
        B = Open(biotic_bn(); inputs=[:SoilMoisture], outputs=[:Occupancy, :SoilMoisture])
        dB = to_wiring_diagram(B)
        @test [p.name for p in input_ports(dB)] == [:SoilMoisture]
        @test [p.name for p in output_ports(dB)] == [:Occupancy, :SoilMoisture]
        @test nboxes(dB) == 4
        # the pass-through wire and the wire into Vegetation both leave the input port
        @test length(out_wires(dB, Port(input_id(dB), OutputPort, 1))) == 2
        @test to_wiring_diagram(biotic_bn(); inputs=[:SoilMoisture],
                                outputs=[:Occupancy, :SoilMoisture]) == dB
        # Default interface of an open apex: exogenous inputs, the rest as outputs.
        d3 = to_wiring_diagram(biotic_bn())
        @test [p.name for p in input_ports(d3)] == [:SoilMoisture]
        @test [p.name for p in output_ports(d3)] ==
              [:GrazingPressure, :Vegetation, :HabitatQuality, :Occupancy]
        # Typed-interface rule on the chosen interface.
        @test_throws InterfaceError to_wiring_diagram(ref; inputs=[:Climate])
        @test_throws InterfaceError to_wiring_diagram(biotic_bn(); inputs=Symbol[])
        e = try
            to_wiring_diagram(biotic_bn(); inputs=[:SoilMoisture, :SoilMoisture])
        catch err
            err
        end
        @test e isa InterfaceError && e.rule == 2
        @test_throws UnknownVariableError to_wiring_diagram(ref; outputs=[:Weather])
        @test_throws DuplicateNameError to_wiring_diagram(apex(otimes(abiotic_open(),
                                                                      abiotic_open())))
    end

    @testset "round trip" begin
        d = to_wiring_diagram(ref)
        bn, ins, outs = from_wiring_diagram(d)
        @test bn isa BayesNet
        @test canonicalize(bn) == canonicalize(ref)
        @test ins == Symbol[]
        @test outs == order
        # Interfaces come back.
        B = Open(biotic_bn(); inputs=[:SoilMoisture], outputs=[:Occupancy, :SoilMoisture])
        bn, ins, outs = from_wiring_diagram(to_wiring_diagram(B))
        @test canonicalize(bn) == canonicalize(apex(B))
        @test (ins, outs) == ([:SoilMoisture], [:Occupancy, :SoilMoisture])
        # References survive.
        hard = do_intervention(ref, :Vegetation => :dense)
        bn, _, _ = from_wiring_diagram(to_wiring_diagram(hard))
        @test canonicalize(bn) == canonicalize(hard)
        @test kernel_ref(bn, Symbol("do[Vegetation=dense]")) == PointMassRef(:dense)
        # asia
        asia = syntax(read_bayesnet(fixture_path("bif/asia.bif")))
        @test canonicalize(first(from_wiring_diagram(to_wiring_diagram(asia)))) ==
              canonicalize(asia)
        # random DAGs, with random parent orders
        rng = MersenneTwister(20250906)
        for _ in 1:20
            bn = syntax(random_model(rng; nvars=rand(rng, 2:6), max_parents=3))
            @test canonicalize(first(from_wiring_diagram(to_wiring_diagram(bn)))) ==
                  canonicalize(bn)
        end
    end

    @testset "from_wiring_diagram errors" begin
        T = ThMarkovCategory.Meta.T
        X, Y, Z = VariablePort(:X, [:a, :b]), VariablePort(:Y, [:c, :d]),
                  VariablePort(:Z, [:e, :f])
        # Fan-in into one port.
        d = BayesWiringDiagram([X, Y], [Z])
        b = add_box!(d, Box(MechanismBox(:f, NoRef()), [X], [Z]))
        add_wire!(d, Port(input_id(d), OutputPort, 1) => Port(b, InputPort, 1))
        add_wire!(d, Port(b, OutputPort, 1) => Port(output_id(d), InputPort, 1))
        @test from_wiring_diagram(d)[2:3] == ([:X, :Y], [:Z])
        add_wire!(d, Port(input_id(d), OutputPort, 2) => Port(b, InputPort, 1))
        e = try
            from_wiring_diagram(d)
        catch err
            err
        end
        @test e isa WiringDiagramError && e.what == :wires && e.box == b && e.port == 1
        @test occursin("2 wires", sprint(showerror, e))
        # A port wired to a variable with another name.
        d = BayesWiringDiagram([X], [Z])
        b = add_box!(d, Box(MechanismBox(:f, NoRef()), [Y], [Z]))
        add_wire!(d, Port(input_id(d), OutputPort, 1) => Port(b, InputPort, 1))
        add_wire!(d, Port(b, OutputPort, 1) => Port(output_id(d), InputPort, 1))
        e = try
            from_wiring_diagram(d)
        catch err
            err
        end
        @test e isa WiringDiagramError && e.what == :port_mismatch
        # An unwired output port.
        d = BayesWiringDiagram([X], [Z])
        e = try
            from_wiring_diagram(d)
        catch err
            err
        end
        @test e isa WiringDiagramError && e.what == :wires && e.box == output_id(d)
        # Two output ports, untyped ports, foreign box values, nested diagrams.
        d = WiringDiagram{T}(Any[], Any[])
        add_box!(d, Box(MechanismBox(:f, NoRef()), [], [Y, Z]))
        @test_throws WiringDiagramError from_wiring_diagram(d)
        d = WiringDiagram{T}(Any[:X], Any[])
        @test_throws WiringDiagramError from_wiring_diagram(d)
        d = WiringDiagram{T}(Any[], Any[])
        add_box!(d, Box(:f, [], [Z]))
        @test_throws WiringDiagramError from_wiring_diagram(d)
        d = WiringDiagram{T}(Any[], Any[])
        add_box!(d, to_wiring_diagram(ref))
        e = try
            from_wiring_diagram(d)
        catch err
            err
        end
        @test e isa WiringDiagramError && e.what == :box
        # Two boxes producing the same variable.
        d = BayesWiringDiagram([], [Z])
        add_box!(d, Box(MechanismBox(:f, NoRef()), [], [Z]))
        b = add_box!(d, Box(MechanismBox(:g, NoRef()), [], [Z]))
        add_wire!(d, Port(b, OutputPort, 1) => Port(output_id(d), InputPort, 1))
        @test_throws DuplicateNameError from_wiring_diagram(d)
    end

    @testset "expressions" begin
        gens = free_generators(m)
        J = joint_distribution(m)
        d = to_wiring_diagram(ref)
        for f in (d -> to_hom_expr(FreeMarkovCategory, d), wiring_expression)
            expr = f(d)
            @test expr isa FreeMarkovCategory.Hom
            @test dom(expr) == munit(FreeMarkovCategory.Ob)
            @test codom(expr) == otimes([Ob(FreeMarkovCategory, x) for x in order])
            @test evaluate(expr, gens) ≈ J
            # Reordered, repeated and dropped outputs.
            d2 = to_wiring_diagram(ref; outputs=reverse(order))
            @test evaluate(f(d2), gens) ≈ joint_distribution(m; variables=reverse(order))
            d3 = to_wiring_diagram(ref; outputs=[:Occupancy, :Climate, :Occupancy])
            @test evaluate(f(d3), gens) ≈
                  interpret(Open(ref; outputs=[:Occupancy, :Climate, :Occupancy]), m)
            d4 = to_wiring_diagram(ref; outputs=[:SoilMoisture])
            @test evaluate(f(d4), gens) ≈ marginal(m, :SoilMoisture)
            d5 = to_wiring_diagram(ref; outputs=Symbol[])
            k5 = evaluate(f(d5), gens)
            @test isempty(k5.dom) && isempty(k5.codom) && only(k5.table) ≈ 1
            # Open networks: inputs, pass-through and copies.
            for outs in ([:Occupancy], [:Occupancy, :SoilMoisture],
                         [:SoilMoisture, :Vegetation, :Vegetation], Symbol[])
                B = Open(biotic_bn(); inputs=[:SoilMoisture], outputs=outs)
                expr = f(to_wiring_diagram(B))
                @test dom(expr) == Ob(FreeMarkovCategory, :SoilMoisture)
                @test evaluate(expr, generators_from(m, biotic_bn())) ≈
                      interpret(B, kernels_by_name(m))
            end
            # Two inputs, in interface order.
            B2 = Open(biotic_bn(; grazing_input=true);
                      inputs=[:GrazingPressure, :SoilMoisture], outputs=[:Occupancy])
            expr = f(to_wiring_diagram(B2))
            @test dom(expr) == otimes(Ob(FreeMarkovCategory, :GrazingPressure),
                                      Ob(FreeMarkovCategory, :SoilMoisture))
            @test evaluate(expr, generators_from(m, biotic_bn(; grazing_input=true))) ≈
                  interpret(B2, kernels_by_name(m))
        end
        # Catlab's reduction handles fan-out; only fully discarded boxes go to the
        # direct builder.
        @test CategoricalBayesianNetworks._all_boxes_reach_outputs(d)
        @test !CategoricalBayesianNetworks._all_boxes_reach_outputs(to_wiring_diagram(ref;
                                                                                      outputs=[:SoilMoisture]))
        @test to_hom_expr(FreeMarkovCategory, CategoricalBayesianNetworks._symbolic(d)) ==
              to_hom_expr(FreeMarkovCategory, d)
        # Random networks: both builders agree with the joint.
        rng = MersenneTwister(20250907)
        for _ in 1:10
            rm = random_model(rng; nvars=rand(rng, 2:5), max_parents=3)
            rd = to_wiring_diagram(rm)
            @test evaluate(to_hom_expr(FreeMarkovCategory, rd), free_generators(rm)) ≈
                  joint_distribution(rm)
            @test evaluate(wiring_expression(rd), free_generators(rm)) ≈
                  joint_distribution(rm)
        end
        # The identity diagram.
        empty = Open(bayesnet(:X => [:a, :b]; closed=false); inputs=[:X], outputs=[:X])
        expr = wiring_expression(to_wiring_diagram(empty))
        @test expr == id(Ob(FreeMarkovCategory, :X))
    end

    @testset "substitute cross-check" begin
        two_step = bayesnet(:SoilMoisture => [:low, :medium, :high],
                            :GrazingPressure => [:low, :high], :Stress => [:lo, :hi],
                            :Vegetation => [:sparse, :moderate, :dense];
                            mechanisms=[:Stress => (:SoilMoisture, :GrazingPressure),
                                        :Vegetation => :Stress], closed=false)
        N = Open(two_step; inputs=[:SoilMoisture, :GrazingPressure], outputs=[:Vegetation])
        S = substitute(ref, :Vegetation_mechanism => N)
        d = to_wiring_diagram(ref)
        b = findfirst(i -> box(d, i).value.name == :Vegetation_mechanism, box_ids(d))
        dS = substitute(d, b, to_wiring_diagram(N))
        @test dS isa BayesWiringDiagram
        @test nboxes(dS) == 8
        bn, ins, outs = from_wiring_diagram(dS)
        @test canonicalize(bn) == canonicalize(S)
        @test outs == order
        # and the two diagrams of the substituted network agree up to box numbering
        @test Set(box(dS, i) for i in box_ids(dS)) ==
              Set(box(to_wiring_diagram(S), i) for i in box_ids(to_wiring_diagram(S)))
    end
end
