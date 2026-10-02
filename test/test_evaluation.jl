using Random

@testset "Categorical evaluation" begin
    m = reference_habitat_model()
    bn = syntax(m)

    @testset "categorical evaluation (Proposition 1)" begin
        expr = to_free_expression(m)
        @test expr isa FreeMarkovCategory.Hom
        @test dom(expr) == munit(FreeMarkovCategory.Ob)
        @test codom(expr) ==
              otimes([Ob(FreeMarkovCategory, x)
                      for x in variable_name.(Ref(bn), topological_order(bn))])
        gens = free_generators(m)
        @test gens[:Climate] == space(m, :Climate)
        @test gens[:Occupancy_mechanism] == kernel(m, :Occupancy)
        @test length(gens) == 14
        C = categorical_joint(m)
        @test C ≈ joint_distribution(m)
        @test C.codom == joint_distribution(m).codom
        @test C ≈ evaluate(expr, gens)
        # The expression has the expected shape on a chain and a fork.
        chain = bind_cpt(BayesModel(bayesnet(:X => [:a, :b], :Y => [:c, :d];
                                             mechanisms=[:Y => :X])),
                         [:X => [0.3, 0.7], :Y => [0.9 0.1; 0.2 0.8]])
        e = to_free_expression(chain)
        @test string(e) == "compose(X_mechanism,mcopy(X),otimes(id(X),Y_mechanism))"
        @test categorical_joint(chain).table ≈ [0.3*0.9 0.3*0.1; 0.7*0.2 0.7*0.8]
        fork = bind_cpt(BayesModel(bayesnet(:X => [:a, :b], :Y => [:c, :d], :Z => [:e, :f];
                                            mechanisms=[:Y => :X, :Z => :X])),
                        [:X => [0.3, 0.7], :Y => [0.9 0.1; 0.2 0.8],
                         :Z => [0.5 0.5; 0.1 0.9]])
        ef = to_free_expression(fork)
        @test occursin("braid", string(ef))   # the copy of X is moved past Y
        @test categorical_joint(fork) ≈ joint_distribution(fork)
        # Parent order that disagrees with the topological order.
        tz = zeros(2, 2, 3)                      # (Y, X, Z)
        tz[1, 1, :] = [0.2, 0.3, 0.5]
        tz[1, 2, :] = [0.1, 0.1, 0.8]
        tz[2, 1, :] = [0.6, 0.2, 0.2]
        tz[2, 2, :] = [0.3, 0.3, 0.4]
        rev = bind_cpt(BayesModel(bayesnet(:X => [:a, :b], :Y => [:c, :d],
                                           :Z => [:e, :f, :g];
                                           mechanisms=[:Y => :X, :Z => (:Y, :X)])),
                       [:X => [0.3, 0.7], :Y => [0.9 0.1; 0.2 0.8], :Z => tz])
        @test names(kernel(rev, :Z).dom) == [:Y, :X]
        @test categorical_joint(rev) ≈ joint_distribution(rev)
        # Interventions are evaluated categorically too.
        md = do_intervention(m, :GrazingPressure => :low)
        @test categorical_joint(md) ≈ joint_distribution(md)
        @test haskey(free_generators(md), Symbol("do[GrazingPressure=low]"))
        # Preconditions.
        @test_throws MissingKernelError categorical_joint(BayesModel(reference_habitat_bn()))
        @test_throws MissingMechanismError to_free_expression(BayesModel(biotic_bn()))
        clash = bayesnet(:X => [:a, :b]; closed=false)
        add_mechanism!(clash, :X; name=:X)
        @test_throws DuplicateNameError to_free_expression(BayesModel(clash))
    end

    @testset "interpret (Propositions 2 and 3)" begin
        refs(xs) = Dict(x => NamedRef("$(x)_mechanism") for x in xs)
        A = Open(bayesnet(:Climate => [:dry, :normal, :wet], :Irrigation => [:low, :high],
                          :SoilMoisture => [:low, :medium, :high];
                          mechanisms=[:SoilMoisture => (:Climate, :Irrigation)],
                          kernel_refs=refs([:Climate, :Irrigation, :SoilMoisture]));
                 outputs=[:SoilMoisture])
        B = Open(bayesnet(:SoilMoisture => [:low, :medium, :high],
                          :GrazingPressure => [:low, :high],
                          :Vegetation => [:sparse, :moderate, :dense],
                          :HabitatQuality => [:poor, :good],
                          :Occupancy => [:absent, :present];
                          mechanisms=[:GrazingPressure => (),
                                      :Vegetation => (:SoilMoisture, :GrazingPressure),
                                      :HabitatQuality => :Vegetation,
                                      :Occupancy => :HabitatQuality], closed=false,
                          kernel_refs=refs([:GrazingPressure, :Vegetation, :HabitatQuality,
                                            :Occupancy]));
                 inputs=[:SoilMoisture], outputs=[:Occupancy])
        kA = interpret(A, m)
        @test kA.dom == FiniteSpace() && kA.codom == space(m, :SoilMoisture)
        @test kA ≈ marginal(m, :SoilMoisture)
        kB = interpret(B, kernels(m))
        @test kB.dom == space(m, :SoilMoisture) && kB.codom == space(m, :Occupancy)
        @test kB ≈ conditional(m, :Occupancy, :SoilMoisture)
        # Proposition 3: sequential composition.
        C = compose(A, B)
        @test interpret(C, m) ≈ compose(kA, kB)
        @test interpret(C, m) ≈ marginal(m, :Occupancy)
        @test interpret(glue(A, B; along=[:SoilMoisture => :SoilMoisture]), m) ≈ kA ⋅ kB
        # Proposition 2: tensor.
        @test interpret(otimes(A, B), m) ≈ otimes(kA, kB)
        @test interpret(A ⊗ A, m) ≈ kA ⊗ kA
        # Inputs passed through and duplicated outputs.
        Bp = Open(apex(B); inputs=[:SoilMoisture], outputs=[:SoilMoisture, :Occupancy])
        kp = interpret(Bp, m)
        @test names(kp.codom) == [:SoilMoisture, :Occupancy]
        @test all(kp.table[i, :, i] ≈ kB.table[:, i] for i in 1:3)
        @test all(kp.table[i, :, j] ≈ zeros(2) for i in 1:3, j in 1:3 if i != j)
        Bd = Open(apex(B); inputs=[:SoilMoisture], outputs=[:Occupancy, :Occupancy])
        kd = interpret(Bd, m)
        @test kd ≈ compose(kB, mcopy(space(m, :Occupancy)))
        # Kernels keyed by variable name, and errors.
        byname = Dict(x => kernel(m, x) for x in variable_names(syntax(m)))
        @test interpret(B, byname) ≈ kB
        @test_throws MissingKernelError interpret(B, Dict{KernelRef,FiniteKernel}())
        @test_throws MissingKernelError interpret(abiotic_open(), m)   # NoRef mechanisms
        # An unset `kernel_ref` is structurally valid, but kernels keyed by reference need
        # it: `BayesianNetworks`' lookup raises `MissingAttributeError`, not `MethodError`.
        unset = deepcopy(B)
        mu = mechanism_of(apex(unset), :Vegetation)
        set_subpart!(apex(unset), mu, :kernel_ref, nothing)
        e = try
            interpret(unset, m)
        catch err
            err
        end
        @test e == MissingAttributeError(:Mechanism, mu, :kernel_ref)
        @test_throws KernelBindingError interpret(B,
                                                  Dict(x => kernel(m, :Climate)
                                                       for x in variable_names(apex(B))))
        @test_throws ModelTooLargeError interpret(B, m; max_states=10)
        # A closed model as an open network with all variables as outputs is the joint.
        full = Open(syntax(m); outputs=variable_name.(Ref(bn), topological_order(bn)))
        @test interpret(full, m) ≈ joint_distribution(m)
    end

    @testset "normalisation tolerance" begin
        # The same model as `BayesianNetworks`' brute-force tolerance test: rows off by
        # 5e-8, as a file with rounded probabilities gives. The categorical evaluator and
        # `interpret` must accept the tolerance they were built with, not only `validate`.
        rough = bind_cpt(BayesModel(bayesnet(:X => [:a, :b], :Y => [:c, :d];
                                             mechanisms=[:Y => :X])),
                         [:X => [0.5, 0.5 + 5e-8], :Y => [0.9 0.1; 0.2 0.8]];
                         atol=1e-6)
        @test_throws UnnormalizedKernelError categorical_joint(rough)
        J = joint_distribution(rough; atol=1e-6)
        @test categorical_joint(rough; atol=1e-6) ≈ J
        O = Open(syntax(rough); outputs=[:Y])
        @test_throws UnnormalizedKernelError interpret(O, rough)
        @test interpret(O, rough; atol=1e-6).table ≈ marginal(rough, :Y; atol=1e-6).table
    end
end

@testset "merge_kernels catches a kernel reference collision" begin
    # `bind_kernel` derives a mechanism's default reference from its *name*, so two
    # independently built networks that name a mechanism alike collide. `otimes` correctly
    # keeps both as distinct apex parts (ADR 0011), but a plain `merge` of their kernel
    # dictionaries drops one kernel, and `interpret` then returned a normalised, wrong
    # kernel for both parts. `interpret` cannot detect this after the fact -- a genuine
    # duplicate such as `A ⊗ A` presents identically -- so the check belongs in the merge.
    st(n, p) = [Symbol(p * string(i)) for i in 1:n]
    function piece(tab, h)
        bn = bayesnet(:Q => st(3, "q"), h => st(5, "h");
                      mechanisms=[h => (:Q,)], closed=false)
        m = bind_cpt(BayesModel(bn), h => tab)
        return m, Open(syntax(m); inputs=[:Q], outputs=[h])
    end
    nrm(t) = t ./ sum(t; dims=2)
    tA = nrm([0.1 0.2 0.3 0.2 0.2; 0.3 0.1 0.1 0.4 0.1; 0.2 0.2 0.2 0.2 0.2])
    tB = nrm([0.4 0.1 0.1 0.2 0.2; 0.1 0.5 0.1 0.2 0.1; 0.3 0.3 0.1 0.2 0.1])

    mA, A = piece(tA, :H)
    mB, B = piece(tB, :H)
    @test_throws ConflictingKernelError merge_kernels(mA, mB)
    @test_throws ConflictingKernelError merge_kernels(kernels(mA), kernels(mB))
    # The silent-loss path that motivated the check.
    @test !(interpret(otimes(A, B), merge(kernels(mA), kernels(mB))) ≈
            tensor_kernel(interpret(A, mA), interpret(B, mB)))

    # Distinct names carry distinct references; the merge is then clean and Proposition 3
    # holds exactly.
    mA2, A2 = piece(tA, :H)
    mB2, B2 = piece(tB, :H2)
    kT = interpret(otimes(A2, B2), merge_kernels(mA2, mB2))
    @test kT ≈ tensor_kernel(interpret(A2, mA2), interpret(B2, mB2))

    # A genuine duplicate shares a reference with itself and must still merge.
    @test merge_kernels(mA2, mA2) == kernels(mA2)
end
