using Catlab.Graphics: Graphviz as CatlabGraphviz

# An open network is drawn with `BayesianNetworks`' own DOT syntax tree; a wiring diagram
# with Catlab's renderer, which returns Catlab's.
dot_source(g) = sprint(Graphviz.pprint, g)
catlab_dot_source(g) = sprint(CatlabGraphviz.pprint, g)

@testset "Categorical graphics" begin
    m = reference_habitat_model()
    ref = syntax(m)

    @testset "open networks" begin
        B = Open(biotic_bn(); inputs=[:SoilMoisture], outputs=[:Occupancy])
        g = to_graphviz(B)
        @test g isa Graphviz.Graph
        nodes = Dict(n.name => n.attrs
                     for n in filter(s -> s isa Graphviz.Node, g.stmts))
        bn = apex(B)
        @test nodes["v$(variable_id(bn, :SoilMoisture))"][:style] == "filled,dashed"
        @test nodes["v$(variable_id(bn, :Occupancy))"][:style] == "filled,bold"
        @test nodes["v$(variable_id(bn, :Vegetation))"][:style] == "filled"
        # The interface defaults to the network's own.
        A = abiotic_open()
        ga = to_graphviz(A)
        nodes_a = Dict(n.name => n.attrs
                       for n in filter(s -> s isa Graphviz.Node, ga.stmts))
        @test nodes_a["v$(variable_id(apex(A), :SoilMoisture))"][:style] == "filled,bold"
    end

    @testset "wiring diagrams" begin
        d = to_wiring_diagram(ref)
        g = to_graphviz(d)
        @test g isa CatlabGraphviz.Graph
        src = catlab_dot_source(g)
        @test occursin("Vegetation_mechanism", src)
        @test occursin("SoilMoisture", src)
        @test g.graph_attrs[:rankdir] == "LR"
        g2 = to_graphviz(d; orientation=TopToBottom, labels=false)
        @test g2.graph_attrs[:rankdir] == "TB"
        @test !occursin("label=\"SoilMoisture\"", catlab_dot_source(g2))
    end

    @testset "SVG rendering" begin
        for g in (to_graphviz(abiotic_open()), to_graphviz(to_wiring_diagram(ref)))
            svg = sprint(show, MIME"image/svg+xml"(), g)
            @test occursin("<svg", svg)
            @test occursin("SoilMoisture", svg)
        end
    end
end
