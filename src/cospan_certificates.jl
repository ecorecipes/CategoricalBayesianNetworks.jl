const _OPEN_CERTIFICATE_AUTHORITY = "070b9b202f6e703b077b7527d47c1d53cab047fd969608ee733bc1308ccfa5c7"
const _OPEN_CERTIFICATE_MAX_PARTS = 256
const _OPEN_CERTIFICATE_MAX_BYTES = 1 << 20

function _open_cert_fail(what, path, message; name=nothing)
    return throw(OpenCertificateError(what, path, name, message))
end

function _open_cert_text(value, path; name=nothing, limit=128)
    value isa Union{Symbol,AbstractString} ||
        _open_cert_fail(:text, path, "expected a string or Symbol"; name)
    text = String(value)
    isvalid(text) && 1 <= length(text) <= limit &&
        all(c -> !(UInt32(c) <= 0x1f || 0x7f <= UInt32(c) <= 0x9f ||
                   0xd800 <= UInt32(c) <= 0xdfff), text) ||
        _open_cert_fail(:text, path,
                        "expected 1:$limit Unicode scalar values without C0/C1 controls, DEL or surrogates";
                        name)
    return text
end

function _open_cert_fields(value, fields, path)
    value isa Union{NamedTuple,AbstractDict} ||
        _open_cert_fail(:shape, path, "expected a NamedTuple or dictionary")
    actual = collect(keys(value))
    all(k -> k isa Union{Symbol,AbstractString}, actual) ||
        _open_cert_fail(:shape, path, "record keys must be strings or Symbols")
    names = String.(actual)
    length(names) == length(fields) && Set(names) == Set(String.(fields)) ||
        _open_cert_fail(:shape, path, "expected exactly the fields $(join(fields, ", "))")
    return NamedTuple{fields}(Tuple(value[actual[findfirst(==(String(f)), names)]]
                                    for f in fields))
end

function _open_cert_reference(ref, path; name=nothing)
    if ref isa Union{NamedTuple,AbstractDict}
        key = ref isa NamedTuple || haskey(ref, :type) ? :type : "type"
        haskey(ref, key) ||
            _open_cert_fail(:reference, path, "missing reference type"; name)
        tag = ref[key]
        tag isa AbstractString ||
            _open_cert_fail(:reference, path, "reference type must be a string tag"; name)
        fields = tag == "NoRef" ? (:type,) :
                 tag == "NamedRef" ? (:type, :id) :
                 tag == "PointMassRef" ? (:type, :state) :
                 tag == "PolicyRef" ? (:type, :decision) : nothing
        fields === nothing &&
            _open_cert_fail(:reference, path, "unsupported reference tag"; name)
        data = _open_cert_fields(ref, fields, path)
        if length(fields) == 2
            _open_cert_text(data[fields[2]], path * "." * String(fields[2]); name)
        end
        ref = BayesianNetworks._kernel_ref_from(data)
    end
    ref isa Union{NoRef,NamedRef,PointMassRef,PolicyRef} ||
        _open_cert_fail(:reference, path, "unsupported reference type $(typeof(ref))"; name)
    data = StructTypes.lower(ref)
    for key in keys(data)
        key == :type || _open_cert_text(data[key], path * "." * String(key); name)
    end
    return data
end

function _open_cert_budget!(used, value, path)
    size = ncodeunits(JSON3.write(value))
    size <= _OPEN_CERTIFICATE_MAX_BYTES - used[] ||
        _open_cert_fail(:resource, path, "compact certificate exceeds 1 MiB")
    used[] += size
    return value
end

function _open_cert_vector(value, path; limit=_OPEN_CERTIFICATE_MAX_PARTS)
    value isa AbstractVector ||
        _open_cert_fail(:shape, path, "expected a vector")
    length(value) <= limit ||
        _open_cert_fail(:resource, path, "at most $limit entries are supported")
    return value
end

function _open_cert_attribute(value, path, used)
    data = _open_cert_fields(value, (:variable_name, :space_ref, :states), path)
    names = [_open_cert_text(s, path * ".states")
             for s in _open_cert_vector(data.states, path * ".states")]
    !isempty(names) && allunique(names) ||
        _open_cert_fail(:states, path, "state labels must be nonempty and distinct")
    result = (variable_name=_open_cert_text(data.variable_name, path * ".variable_name"),
              space_ref=_open_cert_reference(data.space_ref, path * ".space_ref"),
              states=names)
    return _open_cert_budget!(used, result, path)
end

function _open_cert_signature(signature, used)
    signature === nothing && return (kind="unrestricted",)
    rows = _open_cert_vector(signature, "signature.entries"; limit=512)
    entries = NamedTuple[]
    for (i, row) in enumerate(rows)
        path = "signature.entries[$(i - 1)]"
        data = _open_cert_fields(row, (:label, :inputs, :output), path)
        label = _open_cert_fields(data.label, (:mechanism_name, :kernel_ref),
                                  path * ".label")
        lowered_label = (mechanism_name=_open_cert_text(label.mechanism_name,
                                                        path * ".label.mechanism_name"),
                         kernel_ref=_open_cert_reference(label.kernel_ref,
                                                         path * ".label.kernel_ref"))
        _open_cert_budget!(used, lowered_label, path * ".label")
        input_types = [_open_cert_attribute(a, path * ".inputs[$(j - 1)]", used)
                       for (j, a) in
                           enumerate(_open_cert_vector(data.inputs, path * ".inputs"))]
        output_type = _open_cert_attribute(data.output, path * ".output", used)
        push!(entries, (label=lowered_label, inputs=input_types, output=output_type))
    end
    return (kind="finite-relation", entries=entries)
end

function _open_cert_profile(o::OpenBayesNetCospan, path)
    for (space, sorts, suffix) in
        ((apex(o), (:Variable, :State, :Mechanism, :Input), ".apex"),
         (input_space(o), (:Variable, :State), ".input.foot"),
         (output_space(o), (:Variable, :State), ".output.foot"))
        for sort in sorts
            n = nparts(space, sort)
            n <= _OPEN_CERTIFICATE_MAX_PARTS ||
                _open_cert_fail(:resource, path * suffix * "." * String(sort),
                                "at most $_OPEN_CERTIFICATE_MAX_PARTS raw parts per sort are supported")
            collect(parts(space, sort)) == collect(1:n) ||
                _open_cert_fail(:part_ids, path * suffix * "." * String(sort),
                                "raw part IDs must be contiguous and one-based")
        end
    end
    return nothing
end

function _open_cert_space(space::AbstractVariableSpace, path, used)
    vars = NamedTuple[]
    for v in parts(space, :Variable)
        name = variable_name(space, v)
        nstates(space, v) > 0 ||
            _open_cert_fail(:states, path * ".Variable[$(v - 1)]",
                            "the certificate profile requires at least one state"; name)
        row = (id=v,
               variable_name=_open_cert_text(name, path * ".Variable.variable_name"; name),
               space_ref=_open_cert_reference(space_ref(space, v),
                                              path * ".Variable.space_ref"; name))
        push!(vars, _open_cert_budget!(used, row, path))
    end
    state_rows = NamedTuple[]
    for s in parts(space, :State)
        v = subpart(space, s, :state_variable)
        name = variable_name(space, v)
        row = (id=s, state_variable=v,
               state_name=_open_cert_text(subpart(space, s, :state_name),
                                          path * ".State[$(s - 1)].state_name"; name),
               state_position=subpart(space, s, :state_position))
        push!(state_rows, _open_cert_budget!(used, row, path))
    end
    return (Variable=vars, State=state_rows)
end

function _open_cert_leg(foot, leg, path, used)
    data = _open_cert_space(foot, path * ".foot", used)
    maps = (Variable=Vector{Int}(collect(components(leg)[:Variable])),
            State=Vector{Int}(collect(components(leg)[:State])))
    _open_cert_budget!(used, maps, path)
    return (foot=data, Variable=maps.Variable, State=maps.State)
end

function _open_cert_network(o::OpenBayesNetCospan, path, used)
    _open_cert_profile(o, path)
    validate(o; unique_names=false)
    bn = apex(o)
    space = _open_cert_space(bn, path * ".apex", used)
    mechanism_rows = NamedTuple[]
    for m in parts(bn, :Mechanism)
        name = mechanism_name(bn, m)
        row = (id=m, target=target(bn, m),
               mechanism_name=_open_cert_text(name,
                                              path *
                                              ".apex.Mechanism[$(m - 1)].mechanism_name";
                                              name),
               kernel_ref=_open_cert_reference(kernel_ref(bn, m),
                                               path *
                                               ".apex.Mechanism[$(m - 1)].kernel_ref";
                                               name))
        push!(mechanism_rows, _open_cert_budget!(used, row, path))
    end
    input_rows = NamedTuple[]
    for i in parts(bn, :Input)
        row = (id=i, input_mechanism=subpart(bn, i, :input_mechanism),
               input_variable=subpart(bn, i, :input_variable),
               input_position=subpart(bn, i, :input_position))
        push!(input_rows, _open_cert_budget!(used, row, path))
    end
    return (apex=merge(space, (Mechanism=mechanism_rows, Input=input_rows)),
            input=_open_cert_leg(input_space(o), left_leg(o), path * ".input", used),
            output=_open_cert_leg(output_space(o), right_leg(o), path * ".output", used))
end

function _open_cert_check_signature(o, signature, path)
    signature.kind == "unrestricted" && return nothing
    bn = apex(o)
    function attribute(v)
        return (variable_name=String(variable_name(bn, v)),
                space_ref=StructTypes.lower(space_ref(bn, v)),
                states=String.(states(bn, v)))
    end
    for m in mechanisms(bn)
        label = (mechanism_name=String(mechanism_name(bn, m)),
                 kernel_ref=StructTypes.lower(kernel_ref(bn, m)))
        triple = (label=label, inputs=[attribute(v) for v in inputs(bn, m)],
                  output=attribute(target(bn, m)))
        triple in signature.entries ||
            _open_cert_fail(:signature, path * ".apex.Mechanism[$(m - 1)]",
                            "the complete local label/input/output triple is absent from the finite relation";
                            name=mechanism_name(bn, m))
    end
    return nothing
end

function _open_cert_cocone(leg, source, target, path, used)
    dom(leg) == source && codom(leg) == target && is_natural(leg) ||
        _open_cert_fail(:cocone, path,
                        "colimit map does not have the captured source and result")
    data = NamedTuple{(:Variable, :State, :Mechanism, :Input)}(Tuple(Vector{Int}(collect(components(leg)[sort]))
                                                                     for sort in
                                                                         (:Variable, :State,
                                                                          :Mechanism,
                                                                          :Input)))
    return _open_cert_budget!(used, data, path)
end

function _open_cert_metadata(description, comparison_manifest_sha256, producer_version,
                             used)
    digest = _open_cert_text(comparison_manifest_sha256,
                             "metadata.comparison_authority.manifest_sha256")
    occursin(r"^[0-9a-f]{64}$", digest) ||
        _open_cert_fail(:metadata, "metadata.comparison_authority.manifest_sha256",
                        "expected 64 lowercase hexadecimal characters")
    data = (producer="CategoricalBayesianNetworks.jl",
            producer_version=_open_cert_text(producer_version, "metadata.producer_version"),
            description=_open_cert_text(description, "metadata.description"; limit=2048),
            comparison_authority=(role="comparison-only", manifest_sha256=digest))
    return _open_cert_budget!(used, data, "metadata")
end

function _open_cert_finish(metadata, signature, kind, networks; cocone=nothing)
    data = (format="ecorecipes.open-network-certificate", version="1.0.0",
            index_base=1, metadata=metadata, signature=signature, kind=kind,
            networks=networks)
    cocone === nothing || (data = merge(data, (cocone=cocone,)))
    ncodeunits(JSON3.write(data)) <= _OPEN_CERTIFICATE_MAX_BYTES ||
        _open_cert_fail(:resource, "\$", "compact certificate exceeds 1 MiB")
    return data
end

"""
    export_open_certificate(o::OpenBayesNet; signature=nothing,
        description="Raw open-network structure",
        comparison_manifest_sha256=..., producer_version=...) -> NamedTuple

Capture the complete one-based raw cospan profile
`ecorecipes.open-network-certificate` version `1.0.0`. Apex Variable/State/
Mechanism/Input rows, both complete feet and both actual Variable/State leg
arrays retain their original part-ID order and explicit positions. Duplicate
names, repeated slots/outputs, pass-through, empty networks and hidden
components are preserved. No numerical tables are included.

`signature=nothing` explicitly encodes unrestricted local typing. A vector of
entries encodes a finite relation: each entry has `label=(mechanism_name,
kernel_ref)`, `inputs=[(variable_name,space_ref,states), ...]`, and `output`
with the same attribute fields. Records may be NamedTuples or dictionaries;
names may be strings or Symbols, and references may be `KernelRef`s or their
exact tagged JSON objects. Several entries may share a label or even repeat.
Every mechanism must match a complete triple, not a label-only lookup.

The versioned profile requires nonempty state bundles; at most 256 parts per
sort, map entries or input/state labels; 512 signature entries; 1:128 Unicode
scalar values per name/reference; and at most 1 MiB of compact JSON3 output.
C0/C1 controls, DEL, invalid UTF-8 and surrogates are rejected.
Descriptions allow up to 2048 scalar values. `OpenCertificateError`
reports profile failures. Structure is checked with `unique_names=false`.

Metadata is descriptive, not attestation. The default comparison digest names
the frozen implementation-v1 comparison packet, **not** the currently loaded
Julia code; the default producer version is the package version. Explicit
metadata must obey the same string restrictions.

The result owns its arrays; do not mutate inputs during capture. This is a
separate format from [`open_network_certificate`](@ref). Passing the reference
consumer is not a theorem about Julia or JSON parsing. Literal HOL proof
attempts must actually build and pass their kernel audit.
"""
function export_open_certificate(o::OpenBayesNetCospan; signature=nothing,
                                 description="Raw open-network structure",
                                 comparison_manifest_sha256=_OPEN_CERTIFICATE_AUTHORITY,
                                 producer_version=string(Base.pkgversion(@__MODULE__)))
    _open_cert_profile(o, "networks.C")
    snapshot = deepcopy(o)
    used = Ref(0)
    metadata = _open_cert_metadata(description, comparison_manifest_sha256,
                                   producer_version, used)
    sig = _open_cert_signature(signature, used)
    data = _open_cert_network(snapshot, "networks.C", used)
    _open_cert_check_signature(snapshot, sig, "networks.C")
    return _open_cert_finish(metadata, sig, "network", (C=data,))
end

"""
    export_open_operation_certificate(operation, A, B; kwargs...) -> NamedTuple

Compute `operation` (`:compose_structural` or `:otimes`) once and capture A, B,
the actual result C, their complete raw feet/legs and both actual four-sort
apex cocone maps. The keywords and resource profile are those of
[`export_open_certificate`](@ref). The producer does not reconstruct maps by
names, recompute a second colimit, or accept a claimed `valid`/`iso` flag.

Composition aligns the middle feet by variable position and `state_position`,
not raw State IDs, and retains the original outer feet. Its right Variable
and State cocone maps may be noninjective when A repeats an output. Tensor
preserves disjoint material and concatenates the feet.

Inputs are captured before the operation and left unchanged. The returned
object is data for independent checking, not a proof of the Julia operation,
parser or a universal raw-cocone-to-category refinement theorem.
"""
function export_open_operation_certificate(operation, A::OpenBayesNetCospan,
                                           B::OpenBayesNetCospan; signature=nothing,
                                           description="Raw open-network operation",
                                           comparison_manifest_sha256=_OPEN_CERTIFICATE_AUTHORITY,
                                           producer_version=string(Base.pkgversion(@__MODULE__)))
    operation isa Symbol && operation in (:compose_structural, :otimes) ||
        _open_cert_fail(:operation, "kind", "choose :compose_structural or :otimes")
    _open_cert_profile(A, "networks.A")
    _open_cert_profile(B, "networks.B")
    a, b = deepcopy((A, B))
    used = Ref(0)
    metadata = _open_cert_metadata(description, comparison_manifest_sha256,
                                   producer_version, used)
    sig = _open_cert_signature(signature, used)
    adata = _open_cert_network(a, "networks.A", used)
    bdata = _open_cert_network(b, "networks.B", used)
    _open_cert_check_signature(a, sig, "networks.A")
    _open_cert_check_signature(b, sig, "networks.B")
    c, ia, ib = operation == :compose_structural ?
                _compose_structural_with_maps(a, b) : _otimes_with_maps(a, b)
    cdata = _open_cert_network(c, "networks.C", used)
    _open_cert_check_signature(c, sig, "networks.C")
    cocone = (A=_open_cert_cocone(ia, apex(a), apex(c), "cocone.A", used),
              B=_open_cert_cocone(ib, apex(b), apex(c), "cocone.B", used))
    return _open_cert_finish(metadata, sig, String(operation), (A=adata, B=bdata, C=cdata);
                             cocone=cocone)
end
