using Catlab.CategoricalAlgebra: OpenACSetLeg

# The SPEC section 45 reference network split into an abiotic component (closed, exporting
# SoilMoisture) and a biotic component (importing SoilMoisture).
function abiotic_bn()
    return bayesnet(:Climate => [:dry, :normal, :wet], :Irrigation => [:low, :high],
                    :SoilMoisture => [:low, :medium, :high];
                    mechanisms=[:SoilMoisture => (:Climate, :Irrigation)])
end

function biotic_bn(; grazing_input::Bool=false)
    mechs = Any[:Vegetation => (:SoilMoisture, :GrazingPressure),
                :HabitatQuality => :Vegetation, :Occupancy => :HabitatQuality]
    grazing_input || push!(mechs, :GrazingPressure => ())
    return bayesnet(:SoilMoisture => [:low, :medium, :high],
                    :GrazingPressure => [:low, :high],
                    :Vegetation => [:sparse, :moderate, :dense],
                    :HabitatQuality => [:poor, :good],
                    :Occupancy => [:absent, :present]; mechanisms=mechs, closed=false)
end

abiotic_open() = Open(abiotic_bn(); outputs=[:SoilMoisture])
biotic_open() = Open(biotic_bn(); inputs=[:SoilMoisture], outputs=[:Occupancy])

@testset "Open networks" begin
    A = abiotic_open()
    B = biotic_open()

    @testset "construction and accessors" begin
        @test A isa OpenBayesNet
        @test B isa OpenBayesNet
        @test inputs(A) == Symbol[]
        @test outputs(A) == [:SoilMoisture]
        @test inputs(B) == [:SoilMoisture]
        @test outputs(B) == [:Occupancy]
        @test apex(A) == abiotic_bn()
        @test input_space(B) isa VariableSpace
        @test states(input_space(B), :SoilMoisture) == [:low, :medium, :high]
        @test states(output_space(B), :Occupancy) == [:absent, :present]
        @test input_variables(B) == [variable_id(biotic_bn(), :SoilMoisture)]
        @test output_variables(B) == [variable_id(biotic_bn(), :Occupancy)]
        @test dom(B).ob == input_space(B)
        @test codom(B).ob == output_space(B)
        @test length(legs(B)) == 2
        @test feet(B) == [input_space(B), output_space(B)]
        @test left_leg(B) === legs(B)[1]
        @test right_leg(B) === legs(B)[2]
        @test Open(biotic_bn(), [:SoilMoisture], [:Occupancy]) == B
        @test interface_matches(output_space(A), input_space(B))
        @test !interface_matches(input_space(B), output_space(B))
        @test validate(B) === nothing
        @test isvalid(B)
        @test isempty(validation_errors(B))
        @test occursin("[:SoilMoisture] -> [:Occupancy]", sprint(show, B))
        @test_throws UnknownVariableError Open(biotic_bn(); inputs=[:Nope])
    end

    @testset "space_ref is carried into the feet" begin
        bn = bayesnet(:X => [:a, :b]; closed=false, space_refs=Dict(:X => NamedRef("x")))
        o = Open(bn; inputs=[:X], outputs=[:X])
        @test space_ref(input_space(o), :X) == NamedRef("x")
    end

    @testset "repeated outputs are an implicit copy" begin
        o = Open(abiotic_bn(); outputs=[:SoilMoisture, :SoilMoisture])
        @test outputs(o) == [:SoilMoisture, :SoilMoisture]
        @test output_variables(o) == [3, 3]
        @test validate(o) === nothing
    end

    @testset "monoidal structure from Catlab" begin
        u = munit(OpenBayesNetOb)
        @test u isa OpenBayesNetOb
        @test nparts(u.ob, :Variable) == 0
        @test otimes(u, dom(B)).ob == input_space(B)
        i = id(dom(B))
        @test i isa OpenBayesNet
        @test inputs(i) == outputs(i) == [:SoilMoisture]
        @test nparts(apex(i), :Mechanism) == 0
        @test canonicalize(apex(compose(i, B))) == canonicalize(apex(B))
        @test canonicalize(apex(compose(A, id(codom(A))))) == canonicalize(apex(A))
    end

    @testset "typed-interface rule" begin
        # Rule 1: an input with a mechanism in the apex.
        @test_throws InterfaceError Open(biotic_bn(); inputs=[:GrazingPressure],
                                         outputs=[:Occupancy])
        e = try
            Open(biotic_bn(); inputs=[:GrazingPressure], outputs=[:Occupancy])
        catch err
            err
        end
        @test e.rule == 1
        @test e.variables == [:GrazingPressure]
        @test occursin("GrazingPressure", sprint(showerror, e))
        # Rule 2: the input leg is not injective.
        e = try
            Open(biotic_bn(); inputs=[:SoilMoisture, :SoilMoisture], outputs=[:Occupancy])
        catch err
            err
        end
        @test e isa InterfaceError && e.rule == 2 && e.variables == [:SoilMoisture]
        # Rule 3: an exogenous variable that is not an input.
        e = try
            Open(biotic_bn(); outputs=[:Occupancy])
        catch err
            err
        end
        @test e isa InterfaceError && e.rule == 3 && e.variables == [:SoilMoisture]
        # Rule 4: a cycle in the apex.
        cyclic = biotic_bn()
        add_input!(cyclic, mechanism_of(cyclic, :Vegetation), :Occupancy)
        @test_throws CyclicBayesNetError Open(cyclic; inputs=[:SoilMoisture],
                                              outputs=[:Occupancy])
        # Rule 5: a leg whose foot does not match the apex (wrong name, wrong states).
        # Legs are built directly with Catlab's `OpenACSetLeg` to bypass `Open`.
        bn = biotic_bn()
        good = let f = VariableSpace()
            add_variable!(f, :Occupancy; states=states(bn, :Occupancy))
            OpenACSetLeg(f; Variable=[variable_id(bn, :Occupancy)],
                         State=state_ids(bn, :Occupancy))
        end
        foot = VariableSpace()
        add_variable!(foot, :Moisture; states=[:low, :medium, :high])
        bad = OpenBayesNet(bn, OpenACSetLeg(foot; Variable=[1], State=[1, 2, 3]), good)
        e = try
            validate(bad)
        catch err
            err
        end
        @test e isa InterfaceError && e.rule == 5 && e.variables == [:Moisture]
        foot = VariableSpace()
        add_variable!(foot, :SoilMoisture; states=[:low, :high])
        bad = OpenBayesNet(bn, OpenACSetLeg(foot; Variable=[1], State=[1, 3]), good)
        @test validation_errors(bad)[1] == InterfaceError(5, [:SoilMoisture], [1])
        foot = VariableSpace()
        add_variable!(foot, :SoilMoisture; states=[:low, :medium, :high])
        bad = OpenBayesNet(bn, OpenACSetLeg(foot; Variable=[1], State=[3, 2, 1]), good)
        @test validation_errors(bad)[1] == InterfaceError(5, [:SoilMoisture], [1])
        # validate = false skips the rule; the errors are still reported on request.
        o = Open(biotic_bn(); outputs=[:Occupancy], validate=false)
        @test !isvalid(o)
        @test map(typeof, validation_errors(o)) == [InterfaceError]
        # Apex errors come first; a dangling reference stops the interface checks.
        broken = biotic_bn()
        add_part!(broken, :Mechanism; mechanism_name=:orphan, kernel_ref=NoRef())
        o = Open(broken; outputs=[:Occupancy], validate=false)
        @test map(typeof, validation_errors(o)) == [DanglingReferenceError]
        # A name or position without a value (an ACSet built part by part) is a
        # `MissingAttributeError`, which stops the interface checks too: never a
        # `MethodError`. This variable is exogenous and not an input, so rule 3 would read
        # its missing name.
        unnamed = biotic_bn()
        v = add_part!(unnamed, :Variable; space_ref=NoRef())
        @test_throws MissingAttributeError Open(unnamed; inputs=[:SoilMoisture],
                                                outputs=[:Occupancy])
        o = Open(unnamed; inputs=[:SoilMoisture], outputs=[:Occupancy], validate=false)
        @test validation_errors(o) == [MissingAttributeError(:Variable, v, :variable_name)]
        @test !isvalid(o)
        @test_throws MissingAttributeError compose(abiotic_open(), o)
        # The feet copy the names and positions of the interface variables and their
        # states, so `Open` reports a missing one while building them, whatever `validate`.
        unplaced = biotic_bn()
        s = add_part!(unplaced, :State; state_variable=variable_id(unplaced, :SoilMoisture),
                      state_name=:saturated)
        for check in (true, false)
            e = try
                Open(unplaced; inputs=[:SoilMoisture], outputs=[:Occupancy], validate=check)
            catch err
                err
            end
            @test e == MissingAttributeError(:State, s, :state_position)
        end
        # A foot state without a position is not preserved by its leg: rule 5.
        foot = VariableSpace()
        add_variable!(foot, :SoilMoisture; states=[:low, :medium])
        add_part!(foot, :State; state_variable=1, state_name=:high)
        bad = OpenBayesNet(bn,
                           OpenACSetLeg(foot; Variable=[variable_id(bn, :SoilMoisture)],
                                        State=state_ids(bn, :SoilMoisture)), good)
        @test validation_errors(bad) == [InterfaceError(5, [:SoilMoisture], [1])]
    end

    @testset "rename_variable" begin
        renamed = rename_variable(abiotic_bn(), :SoilMoisture => :Soil)
        @test variable_names(renamed) == [:Climate, :Irrigation, :Soil]
        @test variable_names(abiotic_bn()) == [:Climate, :Irrigation, :SoilMoisture]
        @test_throws UnknownVariableError rename_variable(abiotic_bn(), :Nope => :Soil)
        o = rename_variable(A, :SoilMoisture => :Soil)
        @test outputs(o) == [:Soil]
        @test variable_names(apex(o))[3] == :Soil
        @test validate(o) === nothing
        m = rename_variable(observe(BayesModel(reference_habitat_bn()), :Climate => :dry),
                            :Climate => :Weather)
        @test evidence(m) == Dict(:Weather => :dry)
        @test has_variable(syntax(m), :Weather)
    end
end
