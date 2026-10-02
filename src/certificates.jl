_certificate_ref(::NoRef, owner) = (tag="noRef",)
_certificate_ref(ref::NamedRef, owner) = (tag="named", id=ref.id)
_certificate_ref(ref::PointMassRef, owner) = (tag="pointMass", state=String(ref.state))
_certificate_ref(ref::PolicyRef, owner) = (tag="policy", decision=String(ref.decision))
# A reference type the v1 profile has no tag for (a user-defined `KernelRef` subtype) is
# model content the certificate cannot represent (ADR 0015), so `OpenCertificateError`.
function _certificate_ref(ref::KernelRef, owner)
    path, name = owner
    return throw(OpenCertificateError(:unsupported_reference, path, name,
                                      "OpenNet.RawCertificate/v1 does not support reference type $(typeof(ref))"))
end
# An unset reference (`nothing`, or an attribute variable) is structurally valid, since
# only the semantics layer needs one bound. The certificate records the value of every
# reference, so it cannot represent one (ADR 0015). `owner` names the part and attribute.
function _certificate_ref(::Union{Nothing,AttrVar}, owner)
    path, name, ob, id, attr = owner
    return throw(OpenCertificateError(:unset_reference, path, name,
                                      "$ob $id has no value for $attr, and OpenNet.RawCertificate/v1 records every reference (NoRef() records none)"))
end

function _certificate_ranks(bn::AbstractBayesNet, ids::Vector{Int}, supplied)
    if supplied === nothing
        return Dict(v => i - 1 for (i, v) in enumerate(topological_order(bn)))
    end
    supplied isa AbstractDict ||
        throw(ArgumentError("ranks must be a dictionary keyed by source variable part ids"))
    all(k -> k isa Integer && !(k isa Bool), keys(supplied)) ||
        throw(ArgumentError("rank keys must be integer variable part ids, not names or booleans"))
    missing = setdiff(ids, collect(keys(supplied)))
    unknown = setdiff(collect(keys(supplied)), ids)
    isempty(missing) && isempty(unknown) ||
        throw(ArgumentError("ranks must cover exactly the variable parts; missing=$missing, unknown=$unknown"))
    ranks = Dict(v => supplied[v] for v in ids)
    for v in ids
        r = ranks[v]
        r isa Integer && !(r isa Bool) && r >= 0 ||
            throw(ArgumentError("rank of variable part $v ($(repr(variable_name(bn, v)))) must be a nonnegative integer, got $(repr(r))"))
    end
    for i in parts(bn, :Input)
        parent = subpart(bn, i, :input_variable)
        child = target(bn, subpart(bn, i, :input_mechanism))
        ranks[parent] < ranks[child] ||
            throw(ArgumentError("rank must increase at input part $i: variable part $parent ($(repr(variable_name(bn, parent)))) -> $child ($(repr(variable_name(bn, child))))"))
    end
    return ranks
end

function _certificate_boundary(foot::AbstractVariableSpace, mapping::Vector{Int}, dense)
    return [(varId=dense[mapping[i]],
             attrs=(name=String(variable_name(foot, v)),
                    spaceRef=_certificate_ref(subpart(foot, v, :space_ref),
                                              ("boundary.spaceRef",
                                               variable_name(foot, v), :Variable, v,
                                               :space_ref)),
                    states=String.(states(foot, v))))
            for (i, v) in enumerate(parts(foot, :Variable))]
end

"""
    open_network_certificate(o::OpenBayesNet; ranks=nothing) -> NamedTuple

Export the JSON-compatible `OpenNet.RawCertificate/v1` structural record checked
by the general-category Lean project. Validate `o` with `unique_names=false`,
then enumerate every apex variable and mechanism in source part order, including
hidden parts. Variable references in the result are dense **0-based** indices;
state and input positions remain the actual **1-based** attributes.

Names and all four reference tags are preserved without sanitization. Input rows
retain repeated occurrences, output rows retain order and multiplicity, and
boundary attributes are read from the actual feet rather than reconstructed
from the apex. No numerical table is included or renormalized.

By default, ranks are the zero-based positions in the apex's topological order.
An explicit `ranks` dictionary must be keyed by source variable part ids, cover
them exactly, contain nonnegative integers, and increase strictly along every
input occurrence. Invalid rank arguments raise `ArgumentError` with the offending
parts; structural errors use the normal [`validate`](@ref) exceptions. A space or
kernel reference the v1 profile has no tag for (a user-defined `KernelRef` subtype)
raises `OpenCertificateError` with `what = :unsupported_reference`. An unset one, which
is structurally valid, raises it with `what = :unset_reference`, naming the part and the
attribute, since the certificate records the value of every reference.

The result can be serialized by JSON3 or another JSON writer. Its format is
specified in `proofs/EXPORTER-CONTRACT.md`. Exporting is not by itself a proof
that the Julia runtime, serializer or numerical implementation has been verified;
the Lean checker establishes validity of the supplied finite record.
"""
function open_network_certificate(o::OpenBayesNetCospan; ranks=nothing)
    validate(o; unique_names=false)
    bn = apex(o)
    ids = collect(Int, parts(bn, :Variable))
    dense = Dict(v => i - 1 for (i, v) in enumerate(ids))
    rank = _certificate_ranks(bn, ids, ranks)
    variable_data = [(name=String(variable_name(bn, v)),
                      spaceRef=_certificate_ref(subpart(bn, v, :space_ref),
                                                ("variables.spaceRef",
                                                 variable_name(bn, v), :Variable, v,
                                                 :space_ref)),
                      stateRows=[(name=String(subpart(bn, s, :state_name)),
                                  position=subpart(bn, s, :state_position))
                                 for s in incident(bn, v, :state_variable)],
                      rank=rank[v]) for v in ids]
    mechanism_data = [(name=String(mechanism_name(bn, m)),
                       kernelRef=_certificate_ref(subpart(bn, m, :kernel_ref),
                                                  ("mechanisms.kernelRef",
                                                   mechanism_name(bn, m), :Mechanism, m,
                                                   :kernel_ref)),
                       target=dense[target(bn, m)],
                       inputRows=[(varId=dense[subpart(bn, i, :input_variable)],
                                   position=subpart(bn, i, :input_position))
                                  for i in incident(bn, m, :input_mechanism)])
                      for m in parts(bn, :Mechanism)]
    return (format="OpenNet.RawCertificate/v1", variableCount=length(ids),
            variableData=variable_data, mechanisms=mechanism_data,
            inputs=_certificate_boundary(input_space(o), input_variables(o), dense),
            outputs=_certificate_boundary(output_space(o), output_variables(o), dense))
end
