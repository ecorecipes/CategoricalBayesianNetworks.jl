import CategoricalBayesianNetworksProofs.Normalization

/-!
# Numerical tensor and foot wiring

Assignments on a disjoint-union interface are canonically equivalent to pairs
of assignments. Under this equivalence, the interpretation of tensor is the
independent product of the actual component kernels. Pure boundary wiring is
the deterministic reindexing kernel, including repeated/copy and empty/delete
maps.
-/

noncomputable section
namespace OpenNet.Interpretation
open FiniteKernelsProofs.Finite
variable {S : Signature} (I : Interpretation S)
variable {X Y X' Y' : Interface S}

def wireRead (p : Y.Port → X.Port) (hp : ∀ y, X.type (p y) = Y.type y)
    (x : I.Boundary X) : I.Boundary Y :=
  Assignment.reindex I x p hp

theorem read_wire (p : Y.Port → X.Port) (hp) (x : I.Boundary X)
    (z : I.Internal (Net.wire p hp)) :
    I.read (Net.wire p hp) x z = I.wireRead p hp x := rfl

theorem joint_wire (p : Y.Port → X.Port) (hp) (x : I.Boundary X)
    (z : I.Internal (Net.wire p hp)) :
    I.joint (Net.wire p hp) x z = 1 := by
  apply Finset.prod_eq_one
  intro a _
  exact a.elim

theorem kernel_wire (p : Y.Port → X.Port) (hp) :
    I.kernel (Net.wire p hp) = Kernel.ofFun (I.wireRead p hp) := by
  classical
  letI : Unique (I.Internal (Net.wire p hp)) := by
    change Unique (I.Assignment (S.result ∘ (Empty.elim : Empty → S.Label)))
    infer_instance
  funext x y
  simp only [kernel, I.read_wire, I.joint_wire, Finset.sum_const, Finset.card_univ,
    Fintype.card_unique, one_nsmul, Kernel.ofFun]

theorem valuation_tensor_left (f : Net X Y) (g : Net X' Y')
    (x : I.Boundary X) (x' : I.Boundary X') (a : I.Internal f) (b : I.Internal g)
    (v : f.Var) :
    I.valuation (f.tensor g) (Assignment.join I x x') (I.combine f g a b)
      (Net.tinl f g v) = I.valuation f x a v := by cases v <;> rfl

theorem valuation_tensor_right (f : Net X Y) (g : Net X' Y')
    (x : I.Boundary X) (x' : I.Boundary X') (a : I.Internal f) (b : I.Internal g)
    (v : g.Var) :
    I.valuation (f.tensor g) (Assignment.join I x x') (I.combine f g a b)
      (Net.tinr f g v) = I.valuation g x' b v := by cases v <;> rfl

theorem joint_tensor (f : Net X Y) (g : Net X' Y')
    (x : I.Boundary X) (x' : I.Boundary X') (a : I.Internal f) (b : I.Internal g) :
    I.joint (f.tensor g) (Assignment.join I x x') (I.combine f g a b) =
      I.joint f x a * I.joint g x' b := by
  unfold joint
  erw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro c _
    change I.weight (f.label c) _ (a c) = _
    congr 1
    change ((f.parents c).map (Net.tinl f g)).map _ = _
    rw [List.map_map]
    exact congrArg (fun k => (f.parents c).map k)
      (funext (I.valuation_tensor_left f g x x' a b))
  · apply Finset.prod_congr rfl
    intro c _
    change I.weight (g.label c) _ (b c) = _
    congr 1
    change ((g.parents c).map (Net.tinr f g)).map _ = _
    rw [List.map_map]
    exact congrArg (fun k => (g.parents c).map k)
      (funext (I.valuation_tensor_right f g x x' a b))

theorem read_tensor (f : Net X Y) (g : Net X' Y')
    (x : I.Boundary X) (x' : I.Boundary X') (a : I.Internal f) (b : I.Internal g) :
    I.read (f.tensor g) (Assignment.join I x x') (I.combine f g a b) =
      Assignment.join I (I.read f x a) (I.read g x' b) := by
  apply Assignment.ext
  funext y
  cases y with
  | inl y => exact I.valuation_tensor_left f g x x' a b (f.output y)
  | inr y => exact I.valuation_tensor_right f g x x' a b (g.output y)

theorem kernel_tensor (f : Net X Y) (g : Net X' Y')
    (x : I.Boundary X) (x' : I.Boundary X') (y : I.Boundary Y) (y' : I.Boundary Y') :
    I.kernel (f.tensor g) (Assignment.join I x x') (Assignment.join I y y') =
      I.kernel f x y * I.kernel g x' y' := by
  classical
  unfold kernel
  erw [← (I.sumLabelsEquiv f.label g.label).symm.sum_comp]
  simp only [Fintype.sum_prod_type, I.read_tensor, I.joint_tensor]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  erw [Assignment.join_injective]
  split_ifs <;> simp_all

end OpenNet.Interpretation
