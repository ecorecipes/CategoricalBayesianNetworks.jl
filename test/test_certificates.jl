using BayesianNetworks: BayesianNetworks

struct CertificateTestRef <: BayesianNetworks.KernelRef end

function mixed_certificate_network()
    bn = BayesNet()
    x = add_variable!(bn, :x; states=Symbol.(["true", "false"]),
                      space_ref=NamedRef("bool:x"))
    visible = add_variable!(bn, :visible; states=Symbol.(["false", "true"]),
                            space_ref=NamedRef("bool:visible"))
    hidden = add_variable!(bn, :hidden; states=Symbol.(["true", "false"]),
                           space_ref=NamedRef("bool:hidden"))
    for v in (x, hidden)
        for (s, position) in zip(incident(bn, v, :state_variable), (2, 1))
            set_subpart!(bn, s, :state_position, position)
        end
    end
    parity = add_part!(bn, :Mechanism; target=visible, mechanism_name=:parity,
                       kernel_ref=NamedRef("kernel:parity"))
    add_part!(bn, :Input; input_variable=x, input_mechanism=parity, input_position=2)
    add_part!(bn, :Input; input_variable=x, input_mechanism=parity, input_position=1)
    add_part!(bn, :Mechanism; target=hidden, mechanism_name=:prior,
              kernel_ref=NamedRef("kernel:prior"))
    return Open(bn; inputs=[:x], outputs=[:x, :visible, :visible])
end

function certificate_profile(c)
    ref(r) = BayesianNetworks.JSON3.write(r)
    function attrs(v)
        return (v.name, ref(v.spaceRef),
                Tuple(r.name for r in sort(collect(v.stateRows); by=r -> r.position)))
    end
    variable(id) = attrs(c.variableData[id + 1])
    mechanisms = [(m.name, ref(m.kernelRef), variable(m.target),
                   Tuple(variable(r.varId)
                         for r in
                             sort(collect(m.inputRows); by=r -> r.position)))
                  for m in c.mechanisms]
    function boundary(rows)
        return [(variable(r.varId), r.attrs.name, ref(r.attrs.spaceRef),
                 Tuple(r.attrs.states)) for r in rows]
    end
    return (sort(attrs.(c.variableData); by=repr), sort(mechanisms; by=repr),
            boundary(c.inputs), boundary(c.outputs))
end

@testset "open-network structural certificates" begin
    o = mixed_certificate_network()
    before = deepcopy(o)
    ranks = Dict(1 => 0, 2 => 1, 3 => 0)
    c = open_network_certificate(o; ranks)
    fixture = joinpath(@__DIR__, "..", "proofs", "certificate-fixtures", "mixed.json")
    parsed = BayesianNetworks.JSON3.read(BayesianNetworks.JSON3.write(c))
    @test parsed == BayesianNetworks.JSON3.read(read(fixture, String))
    @test c.format == "OpenNet.RawCertificate/v1" && c.variableCount == 3
    @test c.mechanisms[1].inputRows == [(varId=0, position=2), (varId=0, position=1)]
    @test [r.varId for r in c.outputs] == [0, 1, 1]
    @test isempty(c.mechanisms[2].inputRows)
    @test c.variableData[1].stateRows[1] == (name="true", position=2)
    @test c.inputs[1].attrs.states == ["false", "true"]
    @test apex(o) == apex(before) && input_space(o) == input_space(before)
    @test ranks == Dict(1 => 0, 2 => 1, 3 => 0)

    automatic = open_network_certificate(o)
    @test all(automatic.variableData[r.varId + 1].rank <
              automatic.variableData[m.target + 1].rank
              for m in automatic.mechanisms for r in m.inputRows)
    renumbered = Open(canonicalize(apex(o)); inputs=[:x], outputs=[:x, :visible, :visible])
    @test certificate_profile(open_network_certificate(renumbered)) ==
          certificate_profile(c)
    @test open_network_certificate(renumbered).outputs[1].varId != c.outputs[1].varId

    # A reference type the v1 profile has no tag for is content the certificate cannot
    # represent (ADR 0015).
    custom = deepcopy(o)
    set_subpart!(apex(custom), 1, :kernel_ref, CertificateTestRef())
    e = try
        open_network_certificate(custom)
    catch err
        err
    end
    @test e isa OpenCertificateError && e.what === :unsupported_reference
    @test e.path == "mechanisms.kernelRef" && e.name == mechanism_name(apex(custom), 1)

    empty = open_network_certificate(Open(BayesNet()))
    @test empty.variableCount == 0
    @test isempty(empty.variableData) && isempty(empty.mechanisms)
    @test isempty(empty.inputs) && isempty(empty.outputs)
    scalar = Open(bayesnet(:same => [:no, :yes]))
    pair = open_network_certificate(compose_structural(scalar, scalar))
    @test pair.variableCount == 2 && length(pair.mechanisms) == 2
    @test [m.target for m in pair.mechanisms] == [0, 1]
    @test all(v.name == "same" for v in pair.variableData)
    @test all(v.spaceRef == (tag="noRef",) for v in pair.variableData)
    @test isempty(pair.inputs) && isempty(pair.outputs)

    reference_cases = deepcopy(apex(o))
    set_subpart!(reference_cases, 1, :kernel_ref, PolicyRef(:decision_name))
    set_subpart!(reference_cases, 2, :kernel_ref, PointMassRef(Symbol("true")))
    refs = open_network_certificate(Open(reference_cases; inputs=[:x],
                                         outputs=[:x, :visible, :visible]))
    @test refs.variableData[1].spaceRef == (tag="named", id="bool:x")
    @test refs.mechanisms[1].kernelRef == (tag="policy", decision="decision_name")
    @test refs.mechanisms[2].kernelRef == (tag="pointMass", state="true")

    bad_foot = deepcopy(o)
    set_subpart!(input_space(bad_foot), 1, :space_ref, NamedRef("wrong-foot"))
    @test_throws InterfaceError open_network_certificate(bad_foot)
    for invalid in (Dict(1 => 0), Dict(1 => 0, 2 => 1, 3 => 0, 4 => 2),
                    Dict(1 => -1, 2 => 1, 3 => 0), Dict(1 => 0, 2 => 0, 3 => 0),
                    Dict(1 => 1, 2 => 0, 3 => 0), Dict(1 => 0.0, 2 => 1.0, 3 => 0.0),
                    Dict{Any,Int}(true => 0, 2 => 1, 3 => 0),
                    Dict(1 => false, 2 => true, 3 => false))
        @test_throws ArgumentError open_network_certificate(o; ranks=invalid)
    end
    @test_throws ArgumentError open_network_certificate(o; ranks=[0, 1, 0])
end
