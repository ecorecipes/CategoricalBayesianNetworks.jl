# The dynamic-network results that go through the categorical layer: an unrolled network
# is the pushout of its slices, so `unroll` must agree with `glue`, and the categorical
# evaluator must agree with the brute-force joint on an unrolled model.

@testset "Dynamic networks, categorically" begin
    @testset "unroll agrees with glue for horizon 1" begin
        dbn = vegetation_herbivore_dbn()
        A = Open(initial_slice(dbn); outputs=[:Vegetation_0, :Herbivores_0])
        B = Open(transition_slice(dbn, 1); inputs=[:Vegetation_0, :Herbivores_0],
                 outputs=[:Vegetation_1, :Herbivores_1])
        G = glue(A, B;
                 along=[:Vegetation_0 => :Vegetation_0,
                        :Herbivores_0 => :Herbivores_0])
        @test inputs(G) == Symbol[]
        @test outputs(G) == [:Vegetation_1, :Herbivores_1]
        @test canonicalize(apex(G)) == canonicalize(unroll(dbn, 1))
        # And gluing one more slice on gives horizon 2.
        G2 = glue(Open(apex(G); outputs=[:Vegetation_1, :Herbivores_1]),
                  Open(transition_slice(dbn, 2); inputs=[:Vegetation_1, :Herbivores_1],
                       outputs=[:Vegetation_2, :Herbivores_2]);
                  along=[:Vegetation_1 => :Vegetation_1, :Herbivores_1 => :Herbivores_1])
        @test canonicalize(apex(G2)) == canonicalize(unroll(dbn, 2))
        # With management the slice has an extra root per slice.
        dbm = vegetation_herbivore_dbn(; management=true)
        Am = Open(initial_slice(dbm); outputs=[:Vegetation_0, :Herbivores_0])
        Bm = Open(transition_slice(dbm, 1); inputs=[:Vegetation_0, :Herbivores_0],
                  outputs=[:Vegetation_1, :Herbivores_1])
        Gm = glue(Am, Bm;
                  along=[:Vegetation_0 => :Vegetation_0,
                         :Herbivores_0 => :Herbivores_0])
        @test canonicalize(apex(Gm)) == canonicalize(unroll(dbm, 1))
        @test nparts(apex(Gm), :Variable) == 6
    end

    @testset "categorical evaluation of an unrolled model" begin
        um = unroll(vegetation_herbivore_model(), 3)
        @test categorical_joint(um) ≈ joint_distribution(um)
    end
end
