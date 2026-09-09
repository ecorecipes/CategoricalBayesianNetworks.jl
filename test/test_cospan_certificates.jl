@testset "Raw four-sort cospan certificates" begin
    CBN = CategoricalBayesianNetworks
    json(value) = CBN.JSON3.write(value)
    map_values(leg, sort) = Vector{Int}(collect(CBN.components(leg)[sort]))

    function raw_example()
        bn = BayesNet()
        x = add_variable!(bn, :X; states=Symbol[], space_ref=NamedRef("shared"))
        y = add_variable!(bn, :Y; states=Symbol[], space_ref=PolicyRef(:space))
        h = add_variable!(bn, :X; states=[:hidden], space_ref=PointMassRef(:hidden))
        x2 = add_state!(bn, x, :x1; position=2)
        add_state!(bn, y, :y1; position=2)
        x1 = add_state!(bn, x, :x0; position=1)
        add_state!(bn, y, :y0; position=1)
        m = add_mechanism!(bn, y; name=:F, kernel_ref=NamedRef("kernel"))
        add_mechanism!(bn, h; name=:F, kernel_ref=NoRef())
        add_input!(bn, m, x; position=2)
        add_input!(bn, m, x; position=1)
        foot = VariableSpace()
        add_variable!(foot, :X; states=Symbol[], space_ref=NamedRef("shared"))
        add_state!(foot, 1, :x1; position=2)
        add_state!(foot, 1, :x0; position=1)
        return OpenBayesNet(bn, CBN.OpenACSetLeg(foot; Variable=[x], State=[x2, x1]),
                            CBN._leg(bn, [y, x, y]))
    end

    function relation(o)
        bn = apex(o)
        attr(v) = (variable_name=variable_name(bn, v), space_ref=space_ref(bn, v),
                   states=states(bn, v))
        return [(label=(mechanism_name=mechanism_name(bn, m), kernel_ref=kernel_ref(bn, m)),
                 inputs=[attr(v) for v in inputs(bn, m)], output=attr(target(bn, m)))
                for m in mechanisms(bn)]
    end

    o = raw_example()
    before = deepcopy(o)
    cert = export_open_certificate(o)
    @test cert.format == "ecorecipes.open-network-certificate"
    @test cert.version == "1.0.0" && cert.index_base === 1
    @test cert.kind == "network"
    @test keys(cert.networks) == (:C,)
    @test !haskey(cert, :cocone)
    @test cert.signature == (kind="unrestricted",)
    @test cert.metadata.comparison_authority.role == "comparison-only"
    @test cert.metadata.comparison_authority.manifest_sha256 ==
          "070b9b202f6e703b077b7527d47c1d53cab047fd969608ee733bc1308ccfa5c7"
    @test cert.metadata.producer_version == string(Base.pkgversion(CBN))
    data = cert.networks.C
    @test getproperty.(data.apex.Variable, :id) == [1, 2, 3]
    @test getproperty.(data.apex.Variable, :variable_name) == ["X", "Y", "X"]
    @test getproperty.(data.apex.Mechanism, :mechanism_name) == ["F", "F"]
    @test getproperty.(data.apex.State, :id) == collect(1:5)
    @test getproperty.(data.apex.State, :state_position) == [1, 2, 2, 1, 1]
    @test getproperty.(data.apex.Input, :input_position) == [2, 1]
    @test getproperty.(data.apex.Input, :input_variable) == [1, 1]
    @test data.input.Variable == [1] && data.input.State == [2, 4]
    @test getproperty.(data.input.foot.State, :state_position) == [2, 1]
    @test data.output.Variable == [2, 1, 2]
    @test data.output.State == map_values(right_leg(o), :State)
    @test data.apex.Variable[1].space_ref == (type="NamedRef", id="shared")
    @test data.apex.Variable[2].space_ref == (type="PolicyRef", decision="space")
    @test data.apex.Variable[3].space_ref == (type="PointMassRef", state="hidden")
    @test data.apex.Mechanism[2].kernel_ref == (type="NoRef",)
    @test o == before
    @test export_open_certificate(o) == cert
    @test CBN.JSON3.read(json(cert)).networks.C.apex.State[2].state_position == 2
    @test !occursin("null", json(cert))

    @testset "relational signatures" begin
        entries = relation(o)
        finite = export_open_certificate(o; signature=entries)
        @test finite.signature.kind == "finite-relation"
        @test length(finite.signature.entries) == 2
        @test finite.signature.entries[1].inputs[1] ==
              (variable_name="X", space_ref=(type="NamedRef", id="shared"),
               states=["x0", "x1"])
        @test export_open_certificate(o;
                                      signature=CBN.JSON3.read(json(finite.signature.entries))).signature ==
              finite.signature
        @test length(export_open_certificate(o; signature=vcat(entries, entries)).signature.entries) ==
              4
        @test_throws OpenCertificateError export_open_certificate(o; signature=entries[1:1])
        @test_throws OpenCertificateError export_open_certificate(o; signature=[])
        wrong = deepcopy(entries)
        wrong[1].inputs[2].states[1] = :wrong
        @test_throws OpenCertificateError export_open_certificate(o; signature=wrong)
        @test_throws OpenCertificateError export_open_certificate(o; signature=x -> true)
        @test_throws OpenCertificateError export_open_certificate(o;
                                                                  signature=[merge(entries[1],
                                                                                   (valid=true,))])

        bn = bayesnet(:A => [:a, :b], :B => [:c, :d]; mechanisms=[:B => :A])
        for m in mechanisms(bn)
            set_subpart!(bn, m, :mechanism_name, :F)
        end
        shared_label = Open(bn; outputs=[:B])
        shared_relation = export_open_certificate(shared_label;
                                                  signature=relation(shared_label)).signature
        @test shared_relation.entries[1].label == shared_relation.entries[2].label
        @test length.(getproperty.(shared_relation.entries, :inputs)) == [1, 0]
        @test shared_relation.entries[1].output != shared_relation.entries[2].output
        wire = Open(bayesnet(:X => [:a, :b]; closed=false); inputs=[:X], outputs=[:X])
        @test export_open_certificate(wire; signature=[]).signature ==
              (kind="finite-relation", entries=[])
    end

    @testset "actual operation maps" begin
        A = Open(bayesnet(:X => [:low, :high]); outputs=[:X, :X])
        bn = BayesNet()
        x1 = add_variable!(bn, :X; states=[:low, :high])
        x2 = add_variable!(bn, :X; states=[:low, :high])
        y = add_variable!(bn, :Y; states=[:off, :on])
        add_mechanism!(bn, y; inputs=[x1, x2])
        B = CBN._open(bn, [x1, x2], [y])
        saved = deepcopy((A, B))
        result = export_open_operation_certificate(:compose_structural, A, B)
        C, ia, ib = CBN._compose_structural_with_maps(A, B)
        @test result.kind == "compose_structural"
        @test keys(result.networks) == (:A, :B, :C)
        @test result.networks.A == export_open_certificate(A).networks.C
        @test result.networks.B == export_open_certificate(B).networks.C
        @test result.networks.C == export_open_certificate(C).networks.C
        for sort in (:Variable, :State, :Mechanism, :Input)
            @test result.cocone.A[sort] == map_values(ia, sort)
            @test result.cocone.B[sort] == map_values(ib, sort)
        end
        @test result.cocone.B.Variable[x1] == result.cocone.B.Variable[x2]
        @test result.cocone.B.State[1:2] == result.cocone.B.State[3:4]
        @test length(result.networks.C.apex.Variable) == 2
        @test length(result.networks.C.apex.Input) == 2
        @test (A, B) == saved
        finite = export_open_operation_certificate(:compose_structural, A, B;
                                                   signature=vcat(relation(A), relation(B)))
        @test finite.networks == result.networks && finite.cocone == result.cocone

        tensor = export_open_operation_certificate(:otimes, o, o)
        T, ta, tb = CBN._otimes_with_maps(o, o)
        @test tensor.kind == "otimes"
        @test tensor.networks.C == export_open_certificate(T).networks.C
        for sort in (:Variable, :State, :Mechanism, :Input)
            @test tensor.cocone.A[sort] == map_values(ta, sort)
            @test tensor.cocone.B[sort] == map_values(tb, sort)
            @test allunique(vcat(tensor.cocone.A[sort], tensor.cocone.B[sort]))
        end
        @test_throws InterfaceMismatchError export_open_operation_certificate(:compose_structural,
                                                                              o, o)
        for operation in (:compose, :unknown, "otimes", missing)
            @test_throws OpenCertificateError export_open_operation_certificate(operation,
                                                                                A, B)
        end
    end

    @testset "empty objects, exact text and ownership" begin
        empty = Open(BayesNet())
        empty_data = export_open_certificate(empty)
        @test all(isempty, values(empty_data.networks.C.apex))
        @test isempty(empty_data.networks.C.input.Variable)
        @test isempty(export_open_operation_certificate(:compose_structural, empty, empty).cocone.B.State)
        @test isempty(export_open_operation_certificate(:otimes, empty, empty).networks.C.apex.Input)
        @test export_open_certificate(o; description="explicit",
                                      producer_version="custom").metadata.description ==
              "explicit"
        @test export_open_certificate(o; comparison_manifest_sha256=repeat("a", 64)).metadata.comparison_authority.manifest_sha256 ==
              repeat("a", 64)
        names = [Symbol("\u00e9"), Symbol("e\u0301")]
        text = Open(bayesnet(names[1] => [:a], names[2] => [:b]); outputs=names)
        @test getproperty.(export_open_certificate(text).networks.C.apex.Variable,
                           :variable_name) ==
              String.(names)
        own_source = deepcopy(o)
        independent = export_open_certificate(own_source)
        set_subpart!(apex(own_source), 1, :variable_name, :changed)
        @test independent == cert
    end

    @testset "explicit profile failures" begin
        for text in ("", "bad\ntext", "bad\x7f", "bad\u0085", repeat("a", 129))
            bad = Open(bayesnet(:X => [:a]); outputs=[:X])
            set_subpart!(apex(bad), 1, :kernel_ref, NamedRef(text))
            @test_throws OpenCertificateError export_open_certificate(bad)
        end
        for text in ("", "bad\ttext", repeat("a", 2049), missing)
            @test_throws OpenCertificateError export_open_certificate(o; description=text)
        end
        for digest in ("", repeat("A", 64), repeat("a", 63), repeat("g", 64))
            @test_throws OpenCertificateError export_open_certificate(o;
                                                                      comparison_manifest_sha256=digest)
        end
        no_states = CBN._open(bayesnet(:X => Symbol[]), Int[], Int[])
        @test_throws OpenCertificateError export_open_certificate(no_states)
        labels = [Symbol("s", i) for i in 1:256]
        largest = Open(bayesnet(:X => labels); outputs=[:X])
        @test length(export_open_certificate(largest).networks.C.apex.State) == 256
        too_many = Open(bayesnet(:X => vcat(labels, [:extra])); outputs=[:X])
        @test_throws OpenCertificateError export_open_certificate(too_many)
        @test_throws OpenCertificateError export_open_operation_certificate(:otimes,
                                                                            largest,
                                                                            largest)
        r = relation(o)
        @test_throws OpenCertificateError export_open_certificate(o;
                                                                  signature=fill(r[1], 513))
        @test_throws OpenCertificateError export_open_certificate(o;
                                                                  signature=[merge(r[1],
                                                                                   (inputs=fill(r[1].inputs[1],
                                                                                                257),))])
        long_states = [Symbol(lpad(string(i), 128, 's')) for i in 1:256]
        big_attr = (variable_name=:X, space_ref=NoRef(), states=long_states)
        huge = [(label=(mechanism_name=:F, kernel_ref=NoRef()),
                 inputs=fill(big_attr, 40), output=big_attr)]
        @test_throws OpenCertificateError export_open_certificate(o; signature=huge)
        bad_ref = (type="NamedRef", id="x", extra="unexpected")
        @test_throws OpenCertificateError export_open_certificate(o;
                                                                  signature=[merge(r[1],
                                                                                   (label=(mechanism_name=:F,
                                                                                           kernel_ref=bad_ref),))])
        err = OpenCertificateError(:text, "networks.C.apex.Variable[0]",
                                   Symbol("bad\nname"), "invalid")
        @test occursin("\\n", sprint(showerror, err))
        @test !occursin('\n', sprint(showerror, err))
    end
end
