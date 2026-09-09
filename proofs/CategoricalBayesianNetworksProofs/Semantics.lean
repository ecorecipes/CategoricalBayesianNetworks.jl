import CategoricalBayesianNetworksProofs.Assignments
import FiniteKernelsProofs.Finite.Kernel
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The actual finite sum-product interpretation

For a fixed input assignment, multiply the local mechanism weights over all
internal generators. Sum those products over internal assignments whose
explicit output map gives the requested output. Output occurrences may repeat
or refer directly to inputs, and generators need not reach any output.

Structural isomorphism invariance and composition are proved directly for
these numerical expressions, before adding their stochastic normalization.
-/

noncomputable section
namespace OpenNet.Interpretation
open FiniteKernelsProofs.Finite
variable {S : Signature} (I : Interpretation S)
variable {X Y Z X' Y' : Interface S}

def joint (f : Net X Y) (x : I.Boundary X) (z : I.Internal f) : ℝ :=
  ∏ a, I.weight (f.label a) (I.parents f x z a) (z a)

def kernel (f : Net X Y) : Kernel (I.Boundary X) (I.Boundary Y) := by
  classical
  exact fun x y => ∑ z, if y = I.read f x z then I.joint f x z else 0

theorem joint_nonneg (f : Net X Y) (x : I.Boundary X) (z : I.Internal f) :
    0 ≤ I.joint f x z :=
  Finset.prod_nonneg (fun _ _ => I.nonneg _ _ _)

theorem kernel_nonneg (f : Net X Y) : Kernel.Nonneg (I.kernel f) := by
  classical
  intro x y
  exact Finset.sum_nonneg (fun z _ => by
    split <;> simp only [joint_nonneg, le_refl])

def internalEquiv {f g : Net X Y} (a : Net.Iso f g) : I.Internal f ≃ I.Internal g :=
  Assignment.renameEquiv I a.gen (fun b => congrArg S.result (a.label b))

theorem internalEquiv_apply {f g : Net X Y} (a : Net.Iso f g)
    (z : I.Internal f) (b : f.Gen) :
    I.internalEquiv a z (a.gen b) = z b := by
  change z (a.gen.symm (a.gen b)) = z b
  rw [Equiv.symm_apply_apply]

theorem valuation_iso {f g : Net X Y} (a : Net.Iso f g)
    (x : I.Boundary X) (z : I.Internal f) (v : f.Var) :
    I.valuation g x (I.internalEquiv a z) (Sum.map id a.gen v) =
      I.valuation f x z v := by
  cases v with
  | inl v => rfl
  | inr b => exact I.internalEquiv_apply a z b

theorem parents_iso {f g : Net X Y} (a : Net.Iso f g)
    (x : I.Boundary X) (z : I.Internal f) (b : f.Gen) :
    I.parents g x (I.internalEquiv a z) (a.gen b) = I.parents f x z b := by
  unfold parents
  rw [a.parents, List.map_map]
  exact congrArg (fun k => (f.parents b).map k) (funext (I.valuation_iso a x z))

theorem joint_iso {f g : Net X Y} (a : Net.Iso f g)
    (x : I.Boundary X) (z : I.Internal f) :
    I.joint g x (I.internalEquiv a z) = I.joint f x z := by
  symm
  apply Fintype.prod_equiv a.gen
  intro b
  rw [I.parents_iso, I.internalEquiv_apply, a.label]

theorem read_iso {f g : Net X Y} (a : Net.Iso f g)
    (x : I.Boundary X) (z : I.Internal f) :
    I.read g x (I.internalEquiv a z) = I.read f x z := by
  apply Assignment.ext
  funext y
  change I.valuation g x _ (g.output y) = _
  rw [a.output]
  exact I.valuation_iso a x z _

theorem kernel_iso {f g : Net X Y} (a : Net.Iso f g) : I.kernel f = I.kernel g := by
  classical
  funext x y
  apply Fintype.sum_equiv (I.internalEquiv a)
  intro z
  rw [I.read_iso, I.joint_iso]

abbrev combine (f : Net X Y) (g : Net X' Y') (a : I.Internal f) (b : I.Internal g) :=
  (I.sumLabelsEquiv f.label g.label).symm (a, b)

theorem valuation_comp_left (f : Net X Y) (g : Net Y Z)
    (x : I.Boundary X) (a : I.Internal f) (b : I.Internal g) (v : f.Var) :
    I.valuation (f.comp g) x (I.combine f g a b) (Net.left f g v) =
      I.valuation f x a v := by cases v <;> rfl

theorem valuation_comp_right (f : Net X Y) (g : Net Y Z)
    (x : I.Boundary X) (a : I.Internal f) (b : I.Internal g) (v : g.Var) :
    I.valuation (f.comp g) x (I.combine f g a b) (Net.right f g v) =
      I.valuation g (I.read f x a) b v := by
  cases v with
  | inl y => exact I.valuation_comp_left f g x a b (f.output y)
  | inr c => rfl

theorem joint_comp (f : Net X Y) (g : Net Y Z)
    (x : I.Boundary X) (a : I.Internal f) (b : I.Internal g) :
    I.joint (f.comp g) x (I.combine f g a b) =
      I.joint f x a * I.joint g (I.read f x a) b := by
  unfold joint
  erw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro c _
    change I.weight (f.label c) _ (a c) = _
    congr 1
    change ((f.parents c).map (Net.left f g)).map _ = _
    rw [List.map_map]
    exact congrArg (fun k => (f.parents c).map k)
      (funext (I.valuation_comp_left f g x a b))
  · apply Finset.prod_congr rfl
    intro c _
    change I.weight (g.label c) _ (b c) = _
    congr 1
    change ((g.parents c).map (Net.right f g)).map _ = _
    rw [List.map_map]
    exact congrArg (fun k => (g.parents c).map k)
      (funext (I.valuation_comp_right f g x a b))

theorem read_comp (f : Net X Y) (g : Net Y Z)
    (x : I.Boundary X) (a : I.Internal f) (b : I.Internal g) :
    I.read (f.comp g) x (I.combine f g a b) = I.read g (I.read f x a) b := by
  apply Assignment.ext
  funext y
  exact I.valuation_comp_right f g x a b (g.output y)

theorem kernel_comp (f : Net X Y) (g : Net Y Z) :
    I.kernel (f.comp g) = Kernel.comp (I.kernel f) (I.kernel g) := by
  classical
  funext x y
  change (∑ z, if y = I.read (f.comp g) x z then I.joint (f.comp g) x z else 0) = _
  erw [← (I.sumLabelsEquiv f.label g.label).symm.sum_comp]
  simp only [Fintype.sum_prod_type, I.read_comp, I.joint_comp]
  unfold Kernel.comp kernel
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single (I.read f x b)]
  · simp [mul_ite]
  · intro c _ hc
    simp [hc]
  · simp

end OpenNet.Interpretation
