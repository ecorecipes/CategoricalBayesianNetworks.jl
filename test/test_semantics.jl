@testset "Semantics of substitution" begin
    m = reference_habitat_model()

    @testset "substitution adds spaces for hidden variables" begin
        N = Open(bayesnet(:HabitatQuality => [:poor, :good], :Detect => [:no, :yes],
                          :Occupancy => [:absent, :present];
                          mechanisms=[:Detect => :HabitatQuality, :Occupancy => :Detect],
                          closed=false); inputs=[:HabitatQuality], outputs=[:Occupancy])
        msub = substitute(m, :Occupancy_mechanism => N)
        @test haskey(spaces(msub), :Detect)
        @test missing_kernels(msub) == [:Detect, :Occupancy] ||
              Set(missing_kernels(msub)) == Set([:Detect, :Occupancy])
        @test validate(msub; closed=true) === nothing
    end

    @testset "renaming an open network" begin
        A = abiotic_open()
        R = rename_variable(A, :SoilMoisture => :Moisture)
        @test variable_names(apex(R)) == replace(variable_names(apex(A)),
                                                 :SoilMoisture => :Moisture)
        @test outputs(R) == [:Moisture]
        @test inputs(R) == inputs(A)
        @test validate(R) === nothing
    end
end
