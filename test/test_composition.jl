@testset "Composition" begin
    ref = reference_habitat_bn()
    A = abiotic_open()
    B = biotic_open()

    @testset "compose reproduces the reference network" begin
        C = compose(A, B)
        @test C isa OpenBayesNet
        @test inputs(C) == Symbol[]
        @test outputs(C) == [:Occupancy]
        @test validate(C) === nothing
        @test validate(apex(C); closed=true, unique_names=true) === nothing
        @test canonicalize(apex(C)) == canonicalize(ref)
        @test is_isomorphic(apex(C), ref)
        @test A ⋅ B == C
        # The glued variable is a single variable with its states in order.
        @test count(==(:SoilMoisture), variable_names(apex(C))) == 1
        @test states(apex(C), :SoilMoisture) == [:low, :medium, :high]
        @test variable_name.(Ref(apex(C)), parents(apex(C), :Vegetation)) ==
              [:SoilMoisture, :GrazingPressure]
        # The output leg points at the Occupancy of the composite.
        @test variable_name(apex(C), only(output_variables(C))) == :Occupancy
        # Composition round-trips through canonicalize and JSON.
        @test canonicalize(parse_json_bayesnet(json_bayesnet(apex(C)))) ==
              canonicalize(ref)
    end

    @testset "compose is strict about interfaces" begin
        B2 = Open(biotic_bn(; grazing_input=true); inputs=[:SoilMoisture, :GrazingPressure],
                  outputs=[:Occupancy])
        e = try
            compose(A, B2)
        catch err
            err
        end
        @test e isa InterfaceMismatchError
        @test e.what == :length
        @test occursin("compose", sprint(showerror, e))
        # Same name, different states.
        Bs = Open(bayesnet(:SoilMoisture => [:low, :high],
                           :Occupancy => [:absent, :present];
                           mechanisms=[:Occupancy => :SoilMoisture], closed=false);
                  inputs=[:SoilMoisture], outputs=[:Occupancy])
        e = try
            compose(A, Bs)
        catch err
            err
        end
        @test e isa InterfaceMismatchError && e.what == :states && e.position == 1
        # Same states, different name: rename to line the interfaces up.
        Bn = rename_variable(B, :SoilMoisture => :Moisture)
        @test_throws InterfaceMismatchError compose(A, Bn)
        @test canonicalize(apex(compose(rename_variable(A, :SoilMoisture => :Moisture),
                                        Bn))) ==
              canonicalize(rename_variable(ref, :SoilMoisture => :Moisture))
        # Different space_ref.
        Br = Open(bayesnet(:SoilMoisture => [:low, :medium, :high],
                           :Occupancy => [:absent, :present];
                           mechanisms=[:Occupancy => :SoilMoisture], closed=false,
                           space_refs=Dict(:SoilMoisture => NamedRef("sm")));
                  inputs=[:SoilMoisture], outputs=[:Occupancy])
        e = try
            compose(A, Br)
        catch err
            err
        end
        @test e isa InterfaceMismatchError && e.what == :space_ref
    end

    @testset "glue" begin
        G = glue(A, B; along=[:SoilMoisture => :SoilMoisture])
        @test canonicalize(apex(G)) == canonicalize(ref)
        @test inputs(G) == Symbol[]
        @test outputs(G) == [:Occupancy]
        @test G == compose(A, B)
        # Unglued inputs of B and unglued outputs of A pass through.
        A2 = Open(abiotic_bn(); outputs=[:Climate, :SoilMoisture])
        B2 = Open(biotic_bn(; grazing_input=true); inputs=[:SoilMoisture, :GrazingPressure],
                  outputs=[:Occupancy])
        G2 = glue(A2, B2; along=[:SoilMoisture => :SoilMoisture])
        @test inputs(G2) == [:GrazingPressure]
        @test outputs(G2) == [:Climate, :Occupancy]
        @test validate(G2) === nothing
        @test isempty(parents(apex(G2), :GrazingPressure))
        @test sort(variable_names(apex(G2))) == sort(variable_names(ref))
        # Gluing is by explicit pairs, never by name.
        Bn = rename_variable(B, :SoilMoisture => :Moisture)
        Gn = glue(A, Bn; along=[:SoilMoisture => :Moisture])
        @test validate(Gn) === nothing
        @test nparts(apex(Gn), :Variable) == 7
        @test variable_name(apex(Gn), variable_id(apex(Gn), :SoilMoisture)) == :SoilMoisture
        @test !has_variable(apex(Gn), :Moisture)
        # Errors.
        e = try
            glue(A, B; along=[:Climate => :SoilMoisture])
        catch err
            err
        end
        @test e isa InterfaceMismatchError && e.what == :missing_output
        e = try
            glue(A, B; along=[:SoilMoisture => :Occupancy])
        catch err
            err
        end
        @test e isa InterfaceMismatchError && e.what == :missing_input
        Bs = Open(bayesnet(:SoilMoisture => [:low, :high],
                           :Occupancy => [:absent, :present];
                           mechanisms=[:Occupancy => :SoilMoisture], closed=false);
                  inputs=[:SoilMoisture], outputs=[:Occupancy])
        e = try
            glue(A, Bs; along=[:SoilMoisture => :SoilMoisture])
        catch err
            err
        end
        @test e isa InterfaceMismatchError && e.what == :states
        @test_throws InterfaceMismatchError glue(A2, B2;
                                                 along=[:SoilMoisture => :SoilMoisture,
                                                        :SoilMoisture => :GrazingPressure])
    end

    @testset "glue refuses to rename onto an occupied name" begin
        # `Bx` already has a variable called :SoilMoisture, so renaming its input :M to
        # A's output name would give the composite two variables of that name.
        Bx = bayesnet(:M => [:low, :medium, :high], :SoilMoisture => [:a, :b],
                      :Vegetation => [:sparse, :moderate, :dense];
                      mechanisms=[:Vegetation => (:M, :SoilMoisture)], closed=false)
        BX = Open(Bx; inputs=[:M, :SoilMoisture], outputs=[:Vegetation])
        e = try
            glue(A, BX; along=[:SoilMoisture => :M])
        catch err
            err
        end
        @test e isa NameClashError
        @test (e.part, e.name, e.other) == (:Variable, :SoilMoisture, :M)
        @test occursin("SoilMoisture", sprint(showerror, e))
        # Renaming onto a free name is still allowed, and a swap is not a clash.
        By = rename_variable(BX, :SoilMoisture => :Other)
        @test validate(glue(A, By; along=[:SoilMoisture => :M])) === nothing
        # Composites of uniquely named pieces are validated with `unique_names = true`.
        dup = bayesnet(:SoilMoisture => [:low, :medium, :high],
                       :Climate => [:dry, :normal, :wet],
                       :Vegetation => [:sparse, :moderate, :dense];
                       mechanisms=[:Climate => :SoilMoisture, :Vegetation => :Climate],
                       closed=false)
        D = Open(dup; inputs=[:SoilMoisture], outputs=[:Vegetation])
        @test_throws DuplicateNameError glue(A, D; along=[:SoilMoisture => :SoilMoisture])
        @test_throws DuplicateNameError compose(A, D)
        # Tensoring legitimately repeats names, and is still accepted.
        @test validate(otimes(A, A); unique_names=false) === nothing
    end

    @testset "otimes" begin
        T = otimes(A, A)
        @test T isa OpenBayesNet
        @test T == A ⊗ A
        @test variable_names(apex(T)) ==
              [:Climate, :Irrigation, :SoilMoisture, :Climate, :Irrigation, :SoilMoisture]
        @test mechanism_names(apex(T)) == vcat(mechanism_names(abiotic_bn()),
                                               mechanism_names(abiotic_bn()))
        @test outputs(T) == [:SoilMoisture, :SoilMoisture]
        @test output_variables(T) == [3, 6]
        @test validate(T) === nothing
        @test validate(apex(T); closed=true, unique_names=false) === nothing
        @test_throws DuplicateNameError validate(T; unique_names=true)
        @test_throws DuplicateNameError validate(apex(T); unique_names=true)
        AB = otimes(A, B)
        @test inputs(AB) == [:SoilMoisture]
        @test outputs(AB) == [:SoilMoisture, :Occupancy]
        @test validate(AB) === nothing
        @test nparts(apex(AB), :Variable) == 8
    end

    @testset "oapply" begin
        uwd = @relation (occ,) begin
            abiotic(soil)
            biotic(soil, occ)
        end
        R = oapply(uwd, [A, B])
        @test R isa OpenBayesNet
        @test canonicalize(apex(R)) == canonicalize(ref)
        @test inputs(R) == Symbol[]
        @test outputs(R) == [:Occupancy]
        @test R == glue(A, B; along=[:SoilMoisture => :SoilMoisture])
        @test oapply(uwd, Dict(:abiotic => A, :biotic => B)) == R
        # Unglued interface variables become outer ports; inputs are the mechanism-free ones.
        uwd2 = @relation (grazing, occ) begin
            abiotic(soil)
            biotic(soil, grazing, occ)
        end
        B2 = Open(biotic_bn(; grazing_input=true); inputs=[:SoilMoisture, :GrazingPressure],
                  outputs=[:Occupancy])
        R2 = oapply(uwd2, [A, B2])
        @test inputs(R2) == [:GrazingPressure]
        @test outputs(R2) == [:Occupancy]
        @test canonicalize(apex(R2)) ==
              canonicalize(glue(A, B2; along=[:SoilMoisture => :SoilMoisture]) |> apex)
        # Two mechanism-bearing variables at one junction.
        Bc = Open(biotic_bn(); inputs=Symbol[], outputs=[:SoilMoisture, :Occupancy],
                  validate=false)
        closed_biotic = biotic_bn()
        add_mechanism!(closed_biotic, :SoilMoisture)
        Bc = Open(closed_biotic; outputs=[:SoilMoisture, :Occupancy])
        @test_throws DuplicateGeneratorError oapply(uwd, [A, Bc])
        bad = oapply(uwd, [A, Bc]; validate=false)
        @test validation_errors(bad)[1] isa DuplicateGeneratorError
        @test_throws DuplicateGeneratorError validate_composition(bad)
        # A cycle created by the wiring.
        uwd3 = @relation () begin
            f(x, y)
            g(y, x)
        end
        F = Open(bayesnet(:X => [:a, :b], :Y => [:a, :b]; mechanisms=[:Y => :X],
                          closed=false); inputs=[:X], outputs=[:Y])
        G = Open(bayesnet(:Y => [:a, :b], :X => [:a, :b]; mechanisms=[:X => :Y],
                          closed=false); inputs=[:Y], outputs=[:X])
        @test_throws CyclicBayesNetError oapply(uwd3, [F, G])
        # Mismatched feet at a junction and wrong port counts.
        Bs = Open(bayesnet(:SoilMoisture => [:low, :high],
                           :Occupancy => [:absent, :present];
                           mechanisms=[:Occupancy => :SoilMoisture], closed=false);
                  inputs=[:SoilMoisture], outputs=[:Occupancy])
        e = try
            oapply(uwd, [A, Bs])
        catch err
            err
        end
        @test e isa InterfaceMismatchError && e.what == :states
        @test_throws InterfaceMismatchError oapply(uwd, [A, B2])
        @test_throws ArgumentError oapply(uwd, [A])
        @test_throws ArgumentError oapply(uwd, Dict(:abiotic => A))
        # An outer port on a junction that no box touches is a typed error, not
        # Catlab's `MethodError`.
        uwd4 = @relation (occ, extra) begin
            abiotic(soil)
            biotic(soil, occ)
        end
        e = try
            oapply(uwd4, [A, B])
        catch err
            err
        end
        @test e isa InterfaceMismatchError && e.what == :missing_junction
        @test e.left == :extra
        @test occursin("no box touches", sprint(showerror, e))
    end

    @testset "substitute" begin
        two_step = bayesnet(:SoilMoisture => [:low, :medium, :high],
                            :GrazingPressure => [:low, :high], :Stress => [:lo, :hi],
                            :Vegetation => [:sparse, :moderate, :dense];
                            mechanisms=[:Stress => (:SoilMoisture, :GrazingPressure),
                                        :Vegetation => :Stress], closed=false)
        N = Open(two_step; inputs=[:SoilMoisture, :GrazingPressure], outputs=[:Vegetation])
        S = substitute(ref, :Vegetation_mechanism => N)
        @test S isa BayesNet
        @test validate(S; closed=true, unique_names=true) === nothing
        @test sort(variable_names(S)) == sort(vcat(variable_names(ref), :Stress))
        @test nparts(S, :Mechanism) == 8
        # The interface of the containing network is unchanged: every original variable
        # keeps its states, and every other mechanism keeps its name, ref and inputs.
        for v in variables(ref)
            @test states(S, variable_name(ref, v)) == states(ref, v)
        end
        record(bn, m) = (mechanism_name(bn, m), kernel_ref(bn, m),
                         variable_name.(Ref(bn), inputs(bn, m)))
        for m in mechanisms(ref)
            mechanism_name(ref, m) == :Vegetation_mechanism && continue
            @test record(S, mechanism_id(S, mechanism_name(ref, m))) == record(ref, m)
        end
        @test variable_name.(Ref(S), parents(S, :Vegetation)) == [:Stress]
        @test variable_name.(Ref(S), parents(S, :Stress)) ==
              [:SoilMoisture, :GrazingPressure]
        @test variable_name.(Ref(S), children(S, :SoilMoisture)) == [:Stress]
        @test canonicalize(parse_json_bayesnet(json_bayesnet(S))) == canonicalize(S)
        # Substituting back the closed form of the original mechanism gives the original.
        veg = Open(bayesnet(:SoilMoisture => [:low, :medium, :high],
                            :GrazingPressure => [:low, :high],
                            :Vegetation => [:sparse, :moderate, :dense];
                            mechanisms=[:Vegetation => (:SoilMoisture, :GrazingPressure)],
                            closed=false); inputs=[:SoilMoisture, :GrazingPressure],
                   outputs=[:Vegetation])
        @test canonicalize(substitute(ref, :Vegetation_mechanism => veg)) ==
              canonicalize(ref)
        # Interface errors: wrong parent order, wrong target, wrong states.
        Nrev = Open(two_step; inputs=[:GrazingPressure, :SoilMoisture],
                    outputs=[:Vegetation])
        e = try
            substitute(ref, :Vegetation_mechanism => Nrev)
        catch err
            err
        end
        @test e isa InterfaceMismatchError && e.what == :variable_name && e.position == 1
        @test_throws InterfaceMismatchError substitute(ref, :HabitatQuality_mechanism => N)
        @test_throws UnknownMechanismError substitute(ref, :nope => N)
        # On a model the rewrite is recorded.
        m = substitute(BayesModel(ref), :Vegetation_mechanism => N; note="stress pathway")
        @test canonicalize(syntax(m)) == canonicalize(S)
        ev = only(history(m))
        @test ev.kind == :substitute
        @test ev.target == :Vegetation
        @test ev.removed == MechanismRecord(:Vegetation_mechanism, NoRef(),
                                            [:SoilMoisture, :GrazingPressure])
        @test ev.added === nothing
        @test occursin("stress pathway", ev.note)
        @test occursin("Stress_mechanism", ev.note)
    end

    @testset "substitute validates the replacement" begin
        bn = bayesnet(:Climate => [:dry, :wet], :S => [:low, :high],
                      :V => [:sparse, :dense];
                      mechanisms=[:S => :Climate, :V => :S])
        # A hidden variable of N named like a variable of `bn` would give two variables
        # (and two mechanisms) of that name.
        inner = bayesnet(:S => [:low, :high], :Climate => [:dry, :wet],
                         :V => [:sparse, :dense];
                         mechanisms=[:Climate => :S, :V => :Climate], closed=false)
        N = Open(inner; inputs=[:S], outputs=[:V])
        e = try
            substitute(bn, :V_mechanism => N)
        catch err
            err
        end
        @test e isa NameClashError && (e.part, e.name) == (:Variable, :Climate)
        # A hidden variable with a free name makes the same replacement legal (the
        # mechanism it carries must be free too, which the default name makes it).
        Nr = Open(bayesnet(:S => [:low, :high], :Stress => [:dry, :wet],
                           :V => [:sparse, :dense];
                           mechanisms=[:Stress => :S, :V => :Stress], closed=false);
                  inputs=[:S], outputs=[:V])
        P = substitute(bn, :V_mechanism => Nr)
        @test isvalid(P; closed=true, unique_names=true)
        @test sort(variable_names(P)) == [:Climate, :S, :Stress, :V]
        # A mechanism of N named like one that stays in `bn`.
        inner3 = bayesnet(:S => [:low, :high], :Stress => [:lo, :hi],
                          :V => [:sparse, :dense];
                          mechanisms=[:Stress => :S, :V => :Stress], closed=false)
        set_subpart!(inner3, mechanism_id(inner3, :Stress_mechanism), :mechanism_name,
                     :S_mechanism)
        N3 = Open(inner3; inputs=[:S], outputs=[:V])
        e = try
            substitute(bn, :V_mechanism => N3)
        catch err
            err
        end
        @test e isa NameClashError && (e.part, e.name) == (:Mechanism, :S_mechanism)
        # An unvalidated replacement with an extra exogenous variable would change the
        # interface of an open containing network; `substitute` validates `N` first.
        obn = bayesnet(:Climate => [:dry, :wet], :S => [:low, :high],
                       :V => [:sparse, :dense];
                       mechanisms=[:S => :Climate, :V => :S], closed=false)
        extra = bayesnet(:S => [:low, :high], :Extra => [:x, :y],
                         :V => [:sparse, :dense];
                         mechanisms=[:V => (:S, :Extra)], closed=false)
        Nx = Open(extra; inputs=[:S], outputs=[:V], validate=false)
        e = try
            substitute(obn, :V_mechanism => Nx)
        catch err
            err
        end
        @test e isa InterfaceError && e.rule == 3 && e.variables == [:Extra]
        Po = substitute(obn, :V_mechanism => Nr)
        @test variable_name.(Ref(Po), exogenous(Po)) ==
              variable_name.(Ref(obn), exogenous(obn))
    end
end
