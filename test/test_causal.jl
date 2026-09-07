# The categorical counterparts of `BayesianNetworks`' numeric causal tests (SPEC section
# 55.4): the same models evaluated through the free Markov-category expression, and
# substitution, which is a pushout of open networks.

@testset "Observation versus intervention, categorically" begin
    chain = bind_cpt(BayesModel(bayesnet(:X => [:x0, :x1], :Y => [:y0, :y1],
                                         :Z => [:z0, :z1];
                                         mechanisms=[:Y => :X, :Z => :Y])),
                     [:X => [0.3, 0.7], :Y => [0.9 0.1; 0.2 0.8], :Z => [0.6 0.4; 0.1 0.9]])
    doy = do_intervention(chain, :Y => :y1)

    @testset "categorical evaluation agrees under intervention" begin
        @test categorical_joint(doy) ≈ joint_distribution(doy)
        @test categorical_joint(chain) ≈ joint_distribution(chain)
    end

    @testset "categorical evaluation agrees under a soft intervention" begin
        m = reference_habitat_model()
        fenced = cpt(axis(syntax(m), :SoilMoisture), axis(syntax(m), :Vegetation),
                     [0.5 0.4 0.1; 0.2 0.5 0.3; 0.05 0.25 0.7])
        ms = soft_intervention(m, :Vegetation => fenced)
        @test categorical_joint(ms) ≈ joint_distribution(ms)
    end

    @testset "substitution preserves semantics" begin
        # Replace Occupancy's mechanism by a two-step network HabitatQuality -> Detect ->
        # Occupancy whose composite kernel equals the original P(Occupancy | HabitatQuality).
        m = reference_habitat_model()
        bn = syntax(m)
        hq, occ = axis(bn, :HabitatQuality), axis(bn, :Occupancy)
        det = FiniteAxis(:Detect, [:no, :yes])
        k1 = cpt(hq, det, [0.9 0.1; 0.1 0.9])
        # Solve k2 so that k1 ⋅ k2 == P(Occupancy | HabitatQuality) = [0.8 0.2; 0.25 0.75].
        target_ = [0.8 0.2; 0.25 0.75]           # rows = HabitatQuality
        k2_table = [0.9 0.1; 0.1 0.9] \ target_   # rows = Detect
        @test all(>=(0), k2_table)
        k2 = cpt(det, occ, k2_table)
        @test compose(k1, k2) ≈ kernel(m, :Occupancy)
        N = Open(bayesnet(:HabitatQuality => [:poor, :good], :Detect => [:no, :yes],
                          :Occupancy => [:absent, :present];
                          mechanisms=[:Detect => :HabitatQuality, :Occupancy => :Detect],
                          closed=false); inputs=[:HabitatQuality], outputs=[:Occupancy])
        m2 = bind_kernel(substitute(m, :Occupancy_mechanism => N),
                         [:Detect => k1, :Occupancy => k2])
        @test validate(m2; closed=true, unique_names=true, semantics=true) === nothing
        @test nparts(syntax(m2), :Variable) == 8
        vars = variable_names(bn)
        @test marginal(m2, vars) ≈ marginal(m, vars)
        @test marginal(m2, :Occupancy) ≈ marginal(m, :Occupancy)
        @test marginal(observe(m2, :Occupancy => :present), :Climate) ≈
              marginal(observe(m, :Occupancy => :present), :Climate)
        @test categorical_joint(m2) ≈ joint_distribution(m2)
        ev = last(history(m2))
        @test ev.kind == :substitute && ev.target == :Occupancy
        # Through the open-network semantics the substituted network is the same kernel.
        @test interpret(N, Dict(:Detect => k1, :Occupancy => k2)) ≈ kernel(m, :Occupancy)
    end
end
