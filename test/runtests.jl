using Test
using CategoricalBayesianNetworks

@testset "CategoricalBayesianNetworks" begin
    include("test_open.jl")
    include("test_composition.jl")
    include("test_operation_maps.jl")
    include("test_semantics.jl")
    include("test_evaluation.jl")
    include("test_causal.jl")
    include("test_properties.jl")
    include("test_formats_bridge.jl")
    include("test_wiring.jl")
    include("test_graphics.jl")
    include("test_dynamic.jl")
    include("test_regressions.jl")
    include("test_certificates.jl")
    include("test_cospan_certificates.jl")
    include("test_docstrings.jl")
end
