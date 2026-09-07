"""
Graphviz drawings of the categorical layer, added as methods of `BayesianNetworks.jl`'s
`BayesianNetworks.to_graphviz`. An open network is drawn as its apex
with the interface marked; a wiring diagram is drawn by Catlab's renderer for directed
wiring diagrams, with the port and box labels of the network.
"""

# Labels for Catlab's wiring-diagram renderer.
box_label(::MIME, b::MechanismBox) = string(b.name)
wire_label(::MIME, p::VariablePort) = string(p.name)

"""
    to_graphviz(o::OpenBayesNet; inputs = inputs(o), outputs = outputs(o), kwargs...)

Draw the apex of an open network with `BayesianNetworks.to_graphviz`, with the input
variables given a dashed border and the output variables a bold one. Every keyword of
the network method is accepted.
"""
function to_graphviz(o::OpenBayesNetCospan; inputs=CategoricalBayesianNetworks.inputs(o),
                     outputs=CategoricalBayesianNetworks.outputs(o), kw...)
    return to_graphviz(apex(o); inputs=inputs, outputs=outputs, kw...)
end

"""
    to_graphviz(d::BayesWiringDiagram; orientation = LeftToRight, labels = true, kwargs...) -> Catlab.Graphics.Graphviz.Graph

Draw a network's wiring diagram with Catlab's Graphviz renderer for directed wiring
diagrams: boxes are labelled with the mechanism name and wires with the variable name.
All of Catlab's keyword arguments are accepted. The result is a
`Catlab.Graphics.Graphviz.Graph`, not the `BayesianNetworks.Graphviz.Graph` the network
methods return; both `show` as SVG.
"""
function to_graphviz(d::BayesWiringDiagram; orientation::LayoutOrientation=LeftToRight,
                     labels::Bool=true, kw...)
    return Catlab.Graphics.to_graphviz(d; orientation=orientation, labels=labels,
                                       kw...)
end
