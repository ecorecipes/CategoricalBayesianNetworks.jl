"""
Renaming a variable of an open network: the feet are renamed along with the apex, so
the legs still point at the same parts. `BayesianNetworks.jl` carries the methods for a
plain network and for a model.
"""

"""
    rename_variable(o::OpenBayesNet, old::Symbol => new::Symbol) -> OpenBayesNet

A copy of the open network in which variable `old` is called `new`, in the apex and in
both feet. Names play no role in gluing (only legs do), so renaming is the explicit way
to line up interfaces that differ only by name.
"""
function rename_variable(o::OpenBayesNetCospan, r::Pair{Symbol,Symbol})
    return _open(rename_variable(apex(o), r), input_variables(o), output_variables(o))
end
