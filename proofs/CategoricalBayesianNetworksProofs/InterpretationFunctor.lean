import CategoricalBayesianNetworksProofs.SemanticTensor
import FiniteKernelsProofs.Theory.FinStoch
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# A genuine stochastic strong monoidal functor

The object map is the finite space of typed boundary assignments. The morphism
map is the explicit sum-product kernel, descended through structural
isomorphism and equipped with its proved stochasticity.

Tensor and unit comparison maps are deterministic bijections between assignment
tuples. Naturality uses the numerical tensor factorization; all structural
coherence is checked on the actual assignment functions.
-/

noncomputable section
namespace OpenNet.Interpretation
open CategoryTheory FiniteKernelsProofs FiniteKernelsProofs.Finite
open MonoidalCategory
variable {S : Signature} (I : Interpretation S)

def space (X : Interface S) : FinStoch := ⟨I.Boundary X⟩

def interpret {X Y : Interface S} (f : X ⟶ Y) : I.space X ⟶ I.space Y :=
  Quotient.liftOn f (fun f => ⟨I.kernel f, I.kernel_stochastic f⟩)
    (fun _ _ ⟨a⟩ => Subtype.ext (I.kernel_iso a))

def functor : Interface S ⥤ FinStoch where
  obj := I.space
  map := I.interpret
  map_id X := by
    apply Subtype.ext
    change I.kernel (Net.wire id (fun _ => rfl)) = Kernel.idK _
    rw [I.kernel_wire]
    apply Kernel.ofFun_congr
    intro x; rfl
  map_comp f g := by
    induction f, g using Quotient.inductionOn₂ with | _ f g =>
      exact Subtype.ext (I.kernel_comp f g)

@[simp] theorem map_ofNet {X Y : Interface S} (f : Net X Y) :
    I.functor.map (ofNet f) = ⟨I.kernel f, I.kernel_stochastic f⟩ := rfl

@[simp] theorem map_wire {X Y : Interface S} (p : Y.Port → X.Port) (hp) :
    I.functor.map (OpenNet.wire p hp) = FinStoch.det (I.wireRead p hp) :=
  Subtype.ext (I.kernel_wire p hp)

def stateTensor (X Y : Interface S) :
    I.space X ⊗ I.space Y ≅ I.space (X.sum Y) :=
  FinStoch.isoOfEquiv (Assignment.sumEquiv I X.type Y.type).symm

def stateUnit : 𝟙_ FinStoch ≅ I.space (Interface.empty S) := by
  letI : Unique (I.Boundary (Interface.empty S)) := by
    change Unique (I.Assignment (Empty.elim : Empty → S.Ty))
    infer_instance
  exact FinStoch.isoOfEquiv (Equiv.ofUnique Unit (I.Boundary (Interface.empty S)))

theorem tensor_natural {X Y X' Y' : Interface S} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (I.functor.map f ⊗ₘ I.functor.map g) ≫ (I.stateTensor Y Y').hom =
      (I.stateTensor X X').hom ≫ I.functor.map (OpenNet.tensor f g) := by
  induction f, g using Quotient.inductionOn₂ with | _ f g =>
    apply Subtype.ext
    change Kernel.comp (Kernel.tensor (I.kernel f) (I.kernel g))
        (Kernel.ofFun (Assignment.sumEquiv I Y.type Y'.type).symm) =
      Kernel.comp (Kernel.ofFun (Assignment.sumEquiv I X.type X'.type).symm)
        (I.kernel (f.tensor g))
    rw [Kernel.comp_ofEquiv_right, Kernel.comp_ofFun_left]
    funext x y
    obtain ⟨⟨y₁, y₂⟩, rfl⟩ := (Assignment.sumEquiv I Y.type Y'.type).symm.surjective y
    exact (I.kernel_tensor f g x.1 x.2 y₁ y₂).symm

def monoidalCore : I.functor.CoreMonoidal where
  εIso := I.stateUnit
  μIso := I.stateTensor
  μIso_hom_natural_left := by
    intro X Y f X'
    have h := I.tensor_natural f (𝟙 X')
    rw [I.functor.map_id] at h
    exact h
  μIso_hom_natural_right := by
    intro X Y X' f
    have h := I.tensor_natural (𝟙 X') f
    rw [I.functor.map_id] at h
    exact h
  associativity := by
    intro X Y Z
    simp only [OpenNet.associator_eq, OpenNet.assocIso, OpenNet.portIso, I.map_wire]
    apply Subtype.ext
    change Kernel.comp (Kernel.tensor (Kernel.ofFun _) (Kernel.idK _))
      (Kernel.comp (Kernel.ofFun _) (Kernel.ofFun _)) =
      Kernel.comp (Kernel.ofFun _)
        (Kernel.comp (Kernel.tensor (Kernel.idK _) (Kernel.ofFun _)) (Kernel.ofFun _))
    simp only [Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
    apply Kernel.ofFun_congr
    rintro ⟨⟨x, y⟩, z⟩
    apply Assignment.ext
    funext v
    rcases v with a | (b | c) <;> rfl
  left_unitality := by
    intro X
    simp only [OpenNet.leftUnitor_eq, OpenNet.leftIso, OpenNet.portIso, I.map_wire]
    apply Subtype.ext
    change Kernel.ofFun _ = Kernel.comp (Kernel.tensor (Kernel.ofFun _) (Kernel.idK _))
      (Kernel.comp (Kernel.ofFun _) (Kernel.ofFun _))
    simp only [Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
    apply Kernel.ofFun_congr
    intro x
    apply Assignment.ext
    funext v
    rfl
  right_unitality := by
    intro X
    simp only [OpenNet.rightUnitor_eq, OpenNet.rightIso, OpenNet.portIso, I.map_wire]
    apply Subtype.ext
    change Kernel.ofFun _ = Kernel.comp (Kernel.tensor (Kernel.idK _) (Kernel.ofFun _))
      (Kernel.comp (Kernel.ofFun _) (Kernel.ofFun _))
    simp only [Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
    apply Kernel.ofFun_congr
    intro x
    apply Assignment.ext
    funext v
    rfl

instance monoidalFunctor : I.functor.Monoidal := I.monoidalCore.toMonoidal

instance braidedFunctor : I.functor.Braided where
  braided := by
    intro X Y
    change (I.stateTensor X Y).hom ≫ I.functor.map (OpenNet.swapIso X Y).hom =
      (β_ (I.space X) (I.space Y)).hom ≫ (I.stateTensor Y X).hom
    simp only [OpenNet.swapIso, OpenNet.portIso, I.map_wire]
    apply Subtype.ext
    change Kernel.comp (Kernel.ofFun _) (Kernel.ofFun _) =
      Kernel.comp (Kernel.ofFun _) (Kernel.ofFun _)
    simp only [Kernel.ofFun_comp_ofFun]
    apply Kernel.ofFun_congr
    rintro ⟨x, y⟩
    apply Assignment.ext
    funext v
    cases v <;> rfl

theorem map_copy (X : Interface S) :
    I.functor.map (OpenNet.copy X) =
      ComonObj.comul (X := I.space X) ≫ (I.stateTensor X X).hom := by
  rw [OpenNet.copy, I.map_wire]
  apply Subtype.ext
  change Kernel.ofFun _ = Kernel.comp (Kernel.ofFun _) (Kernel.ofFun _)
  rw [Kernel.ofFun_comp_ofFun]
  apply Kernel.ofFun_congr
  intro x
  apply Assignment.ext
  funext v
  cases v <;> rfl

theorem map_discard (X : Interface S) :
    I.functor.map (OpenNet.discard X) =
      ComonObj.counit (X := I.space X) ≫ I.stateUnit.hom := by
  rw [OpenNet.discard, I.map_wire]
  apply Subtype.ext
  change Kernel.ofFun _ = Kernel.comp (Kernel.discard _) (Kernel.ofFun _)
  rw [Kernel.discard_eq_ofFun, Kernel.ofFun_comp_ofFun]
  apply Kernel.ofFun_congr
  intro x
  apply Assignment.ext
  funext v
  exact v.elim

/-- Discard erases hidden mechanisms semantically, not by identifying syntax. -/
theorem semantic_discard {X Y : Interface S} (f : X ⟶ Y) :
    I.functor.map (f ≫ OpenNet.discard Y) = I.functor.map (OpenNet.discard X) := by
  rw [Functor.map_comp, I.map_discard, I.map_discard]
  erw [← Category.assoc, FinStoch.discard_natural]
  rfl

end OpenNet.Interpretation
