using Test
using CategoricalBayesianNetworks

@testset "CategoricalBayesianNetworks" begin
    include("test_open.jl")
    include("test_composition.jl")
    include("test_semantics.jl")
    include("test_evaluation.jl")
    include("test_causal.jl")
    include("test_properties.jl")
    include("test_formats_bridge.jl")
    include("test_wiring.jl")
    include("test_graphics.jl")
    include("test_dynamic.jl")
end
