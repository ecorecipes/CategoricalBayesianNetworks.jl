# Exceptions of CategoricalBayesianNetworks (ADR 0013). A type this package introduces lives
# here, in this package's own module, under `BayesianNetworks`' `BayesNetError`: the package
# is built on BayesianNetworks, so its errors belong to that tier. Most errors raised here are
# BayesianNetworks' own (`InterfaceError`, `InterfaceMismatchError`, `NameClashError`,
# `WiringDiagramError`, ...) and MarkovCategories' `UnboundGeneratorError` from `evaluate`;
# they pass through unchanged and are re-exported as their owners' bindings. A docstring names
# another package's type as a code span, never with `@ref`.

"""
    ConflictingKernelError(ref, first, second)

Two models bind different kernels to the same `BayesianNetworks.KernelRef`, so they cannot be
combined into one kernel dictionary. See [`merge_kernels`](@ref).
"""
struct ConflictingKernelError <: BayesNetError
    ref::KernelRef
    first::FiniteKernel
    second::FiniteKernel
end

function Base.showerror(io::IO, e::ConflictingKernelError)
    return print(io,
                 "ConflictingKernelError: two models bind different kernels to ", e.ref,
                 ". `bind_kernel` derives a mechanism's default reference from its name, so ",
                 "independently built networks that name a mechanism alike collide. Give the ",
                 "mechanisms distinct names before binding their kernels, or set their kernel_ref ",
                 "explicitly. (`rename_variable` does not rewrite an already-bound reference.)")
end
