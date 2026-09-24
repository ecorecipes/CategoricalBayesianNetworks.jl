import CategoricalBayesianNetworksProofs.InterpretationFunctor

/-!
# SA-Pass shadow module: the interpretation is a functor preserving copy and discard

Claim `cbn.functor`, from `kernel_comp`, `map_copy` and `map_discard`.
-/

noncomputable section

namespace CategoricalBayesianNetworksProofs.Shadows.InterpretationFunctor

open CategoryTheory MonoidalCategory OpenNet OpenNet.Interpretation
open FiniteKernelsProofs FiniteKernelsProofs.Finite

/-- `kernel_comp`, `map_copy` and `map_discard`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (S : Signature) (I : Interpretation S),
    (∀ (X Y Z : Interface S) (f : Net X Y) (g : Net Y Z),
        I.kernel (f.comp g) = Kernel.comp (I.kernel f) (I.kernel g)) ∧
      (∀ X : Interface S,
        I.functor.map (OpenNet.copy X) =
          ComonObj.comul (X := I.space X) ≫ (I.stateTensor X X).hom) ∧
      (∀ X : Interface S,
        I.functor.map (OpenNet.discard X) =
          ComonObj.counit (X := I.space X) ≫ I.stateUnit.hom)

/-- "a functor into the existing FinStoch category": the kernel of a substitution is the matrix
product of the two kernels, entry by entry -- the sum-product semantics, not a new notion of
composition. -/
abbrev Shadow1 : Prop :=
  ∀ (S : Signature) (I : Interpretation S) (X Y Z : Interface S) (f : Net X Y) (g : Net Y Z)
      (x : I.Boundary X) (z : I.Boundary Z),
    I.kernel (f.comp g) x z = ∑ y, I.kernel f x y * I.kernel g y z

/-- "preserving copy and discard": the comonoid structure of a foot is carried to the comonoid
structure of its assignment space. -/
abbrev Shadow2 : Prop :=
  ∀ (S : Signature) (I : Interpretation S) (X : Interface S),
    I.functor.map (OpenNet.copy X) =
      ComonObj.comul (X := I.space X) ≫ (I.stateTensor X X).hom ∧
    I.functor.map (OpenNet.discard X) =
      ComonObj.counit (X := I.space X) ≫ I.stateUnit.hom

theorem forward1 : Candidate → Shadow1 := by
  intro h S I X Y Z f g x z
  rw [(h S I).1 X Y Z f g]
  rfl

theorem forward2 : Candidate → Shadow2 := by
  intro h S I X
  exact ⟨(h S I).2.1 X, (h S I).2.2 X⟩

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2 S I
  refine ⟨?_, fun X => (h2 S I X).1, fun X => (h2 S I X).2⟩
  intro X Y Z f g
  funext x z
  rw [h1 S I X Y Z f g x z]
  rfl

end CategoricalBayesianNetworksProofs.Shadows.InterpretationFunctor
