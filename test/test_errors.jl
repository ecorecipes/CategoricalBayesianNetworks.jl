# The exception hierarchy of ADR 0013. The one type this package introduces lives in its own
# module under BayesianNetworks' `BayesNetError`; MarkovCategories' exception types, which
# `evaluate` raises, are re-exported as the same bindings.
using MarkovCategories: MarkovCategories

function exported_exception_names(M)
    return filter(names(M)) do n
        T = getglobal(M, n)
        return T isa Type && T <: Exception
    end
end

@testset "errors" begin
    @test ConflictingKernelError <: BayesNetError
    @test ConflictingKernelError <: AnyBayesNetError
    @test parentmodule(ConflictingKernelError) === CategoricalBayesianNetworks
    exported = names(CategoricalBayesianNetworks)
    mc = exported_exception_names(MarkovCategories)
    @test :UnboundGeneratorError in mc
    for n in mc
        @test n in exported
        @test getglobal(CategoricalBayesianNetworks, n) === getglobal(MarkovCategories, n)
    end
    @test UnboundGeneratorError <: FiniteKernelsError
end
