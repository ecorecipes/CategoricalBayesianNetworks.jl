# The categorical evaluator on a network read from a file: the same numbers as the
# brute-force joint, on a model nobody wrote by hand.

@testset "Formats bridge, categorically" begin
    @testset "asia" begin
        m = read_bayesnet(fixture_path("bif/asia.bif"))
        @test categorical_joint(m) ≈ joint_distribution(m)
    end
end
