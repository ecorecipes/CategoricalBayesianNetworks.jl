import CategoricalBayesianNetworksProofs.Semantics
import BayesianNetworksProofs.Finite.Evaluation
import Mathlib.Data.List.Sort

/-!
# Normalization from local kernels and acyclic ranks

For each fixed input assignment, induction on generator rank constructs
inhabitance of every generated state space from the normalized local rows.
Thus no global nonemptiness assumption is imposed on signature state types.
The finite product normalization theorem is then applied to the internal
generator graph, with the actual ordered-slot kernel and input values fixed.
The unordered dependency set is used only for locality and topological order;
the numerical kernel still reads every ordered occurrence.
-/

noncomputable section
namespace OpenNet.Interpretation
open BayesianNetworksProofs
open FiniteKernelsProofs.Finite
variable {S : Signature} (I : Interpretation S) {X Y : Interface S}

theorem generated_nonempty (f : Net X Y) (x : I.Boundary X) (a : f.Gen) :
    Nonempty (I.states (S.result (f.label a))) := by
  classical
  obtain ⟨r, hr⟩ := f.acyclic
  refine (measure r).wf.induction (C := fun a => Nonempty (I.states (S.result (f.label a)))) a ?_
  intro a ih
  have hn (v : f.Var) (hv : v ∈ f.parents a) : Nonempty (I.states (f.varType v)) := by
    cases v with
    | inl p => exact ⟨Assignment.toPi I x p⟩
    | inr b => exact ih b (hr a b hv)
  let p : List I.Value :=
    (f.parents a).attach.map (fun v => ⟨f.varType v.1, Classical.choice (hn v.1 v.2)⟩)
  have hp : p.map Sigma.fst = S.inputs (f.label a) := by
    calc
      p.map Sigma.fst = ((f.parents a).attach.map Subtype.val).map f.varType := by
        simp only [p, List.map_map]; rfl
      _ = S.inputs (f.label a) := by
        rw [List.attach_map_subtype_val]
        exact f.parents_typed a
  have hnorm := I.normalized (f.label a) p hp
  by_contra h
  letI : IsEmpty (I.states (S.result (f.label a))) := not_nonempty_iff.mp h
  simp at hnorm

def internalBN (f : Net X Y) (x : I.Boundary X) : FinBayesNet := by
  classical
  exact {
    V := f.Gen
    M := f.Gen
    states := fun a => I.states (S.result (f.label a))
    nonemptyS := I.generated_nonempty f x
    target := id
    parents := fun a => Finset.univ.filter (fun b => Sum.inr b ∈ f.parents a) }

def internalKernel (f : Net X Y) (x : I.Boundary X) : (I.internalBN f x).Kernel ℝ :=
  fun a z s => I.weight (f.label a)
    (I.parents f x (Assignment.ofPi I z) a) ⟨S.result (f.label a), s⟩

theorem internal_local (f : Net X Y) (x : I.Boundary X) :
    ∀ a, FinBayesNet.Local (I.internalKernel f x) a := by
  classical
  intro a z z' hz
  funext s
  change I.weight _ _ _ = I.weight _ _ _
  congr 1
  apply List.map_congr_left
  intro v hv
  cases v with
  | inl p => rfl
  | inr b =>
    change (⟨S.result (f.label b), z b⟩ : I.Value) = ⟨S.result (f.label b), z' b⟩
    congr 1
    apply hz b
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩

theorem internal_normalized (f : Net X Y) (x : I.Boundary X) :
    ∀ a, FinBayesNet.Normalised (I.internalKernel f x) a := by
  intro a z
  exact I.normalized (f.label a) _ (I.parents_typed f x (Assignment.ofPi I z) a)

def internalOrder (f : Net X Y) (x : I.Boundary X) :
    (I.internalBN f x).TopoOrder := by
  classical
  let r := Classical.choose f.acyclic
  have hr := Classical.choose_spec f.acyclic
  let l := (Finset.univ : Finset f.Gen).toList
  let ordered := l.mergeSort (fun a b => decide (r a ≤ r b))
  have perm : ordered.Perm l := List.mergeSort_perm _ _
  have pair : ordered.Pairwise (fun a b => r a ≤ r b) := by
    have h := List.pairwise_mergeSort (le := fun a b => decide (r a ≤ r b))
      (by
        intro a b c hab hbc
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hab hbc)
      (by
        intro a b
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _) l
    simpa only [decide_eq_true_eq] using h
  exact {
    order := ordered
    nodup := perm.nodup_iff.mpr (Finset.nodup_toList _)
    complete := fun a => perm.mem_iff.mpr (by simp [l])
    parents_before := pair.imp (by
      intro a b hab m hma hb
      change m = a at hma
      subst m
      have hmem : Sum.inr b ∈ f.parents a := (Finset.mem_filter.mp hb).2
      exact (not_lt_of_ge hab) (hr a b hmem))
    no_self := fun a ha => by
      have hmem : Sum.inr a ∈ f.parents a := (Finset.mem_filter.mp ha).2
      exact Nat.lt_irrefl _ (hr a a hmem) }

theorem joint_normalized (f : Net X Y) (x : I.Boundary X) :
    ∑ z, I.joint f x z = 1 := by
  classical
  have h := FinBayesNet.sum_joint_eq_one (I.internalKernel f x)
    (show (I.internalBN f x).Closed from Function.bijective_id)
    (I.internalOrder f x) (I.internal_local f x) (I.internal_normalized f x)
  calc
    ∑ z, I.joint f x z =
        ∑ p : ∀ a, I.states (S.result (f.label a)),
          I.joint f x (Assignment.ofPi I p) :=
      ((Assignment.piEquiv I (S.result ∘ f.label)).sum_comp _).symm
    _ = 1 := h

theorem kernel_normalized (f : Net X Y) : Kernel.Normalised (I.kernel f) := by
  classical
  intro x
  unfold kernel
  rw [Finset.sum_comm]
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using I.joint_normalized f x

theorem kernel_stochastic (f : Net X Y) : Kernel.Stochastic (I.kernel f) :=
  ⟨I.kernel_nonneg f, I.kernel_normalized f⟩

end OpenNet.Interpretation
