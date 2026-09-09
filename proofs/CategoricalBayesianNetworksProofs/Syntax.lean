import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Common
import Mathlib.Logic.Relation

/-!
# Finite typed open-network syntax

A signature assigns each mechanism label an ordered list of input types and one
output type. Types can encode variable names, ordered state tables and references;
labels can encode mechanism names and references. No uniqueness of these attributes
is imposed. Parent *lists*, not sets, retain repeated input occurrences.

An interface is a finite typed set. A network's variables are its input ports plus
its internal generators. Thus its input leg is injective and identifies exactly
the exogenous variables; every other variable has exactly one generator. The
output leg is an arbitrary typed function, allowing copying and pass-through.
A finite ranking witnesses acyclicity but is a proposition, not syntax data.
Neither reachability from outputs nor nonempty interfaces are required.
-/

namespace OpenNet

structure Signature where
  Ty : Type
  Label : Type
  inputs : Label → List Ty
  result : Label → Ty

structure Interface (S : Signature) where
  Port : Type
  finite : Fintype Port
  type : Port → S.Ty

attribute [instance] Interface.finite

variable {S : Signature}

def Interface.sum (X Y : Interface S) : Interface S :=
  ⟨X.Port ⊕ Y.Port, inferInstance, Sum.elim X.type Y.type⟩

def Interface.empty (S : Signature) : Interface S :=
  ⟨Empty, inferInstance, Empty.elim⟩

structure Net (X Y : Interface S) where
  Gen : Type
  finite : Fintype Gen
  label : Gen → S.Label
  parents : Gen → List (X.Port ⊕ Gen)
  output : Y.Port → X.Port ⊕ Gen
  parents_typed : ∀ g, (parents g).map (Sum.elim X.type (S.result ∘ label)) =
    S.inputs (label g)
  output_typed : ∀ y, Sum.elim X.type (S.result ∘ label) (output y) = Y.type y
  acyclic : ∃ rank : Gen → ℕ, ∀ g h, Sum.inr h ∈ parents g → rank h < rank g

attribute [instance] Net.finite

namespace Net
variable {X Y Z W : Interface S}

abbrev Var (f : Net X Y) := X.Port ⊕ f.Gen

def varType (f : Net X Y) : f.Var → S.Ty :=
  Sum.elim X.type (S.result ∘ f.label)

/-- No nonempty directed path can return to its starting generator. -/
theorem no_directed_cycle (f : Net X Y) (a : f.Gen) :
    ¬ Relation.TransGen (fun u v => Sum.inr u ∈ f.parents v) a a := by
  obtain ⟨r, hr⟩ := f.acyclic
  have increasing {u v : f.Gen}
      (p : Relation.TransGen (fun u v => Sum.inr u ∈ f.parents v) u v) : r u < r v := by
    induction p with
    | single h => exact hr _ _ h
    | tail _ h ih => exact lt_trans ih (hr _ _ h)
  intro p
  exact Nat.lt_irrefl _ (increasing p)

/-- Renumbering fixes the boundary and preserves every ordered incidence and label. -/
structure Iso (f g : Net X Y) where
  gen : f.Gen ≃ g.Gen
  label : ∀ a, g.label (gen a) = f.label a
  parents : ∀ a, g.parents (gen a) = (f.parents a).map (Sum.map id gen)
  output : ∀ y, g.output y = Sum.map id gen (f.output y)

def Iso.refl (f : Net X Y) : Iso f f where
  gen := Equiv.refl _
  label _ := rfl
  parents _ := by simp
  output y := by cases f.output y <;> rfl

def Iso.trans {f g h : Net X Y} (a : Iso f g) (b : Iso g h) : Iso f h where
  gen := a.gen.trans b.gen
  label x := (b.label _).trans (a.label _)
  parents x := by
    change h.parents (b.gen (a.gen x)) = _
    rw [b.parents, a.parents, List.map_map]
    congr 1
    funext v
    cases v <;> rfl
  output y := by
    rw [b.output, a.output]
    cases f.output y <;> rfl

def Iso.symm {f g : Net X Y} (a : Iso f g) : Iso g f where
  gen := a.gen.symm
  label x := by simpa using (a.label (a.gen.symm x)).symm
  parents x := by
    have h := congrArg (List.map (Sum.map id a.gen.symm)) (a.parents (a.gen.symm x))
    simp only [Equiv.apply_symm_apply, List.map_map] at h
    simpa using h.symm
  output y := by
    have h := congrArg (Sum.map id a.gen.symm) (a.output y)
    cases e : f.output y <;> simpa [e] using h.symm

instance setoid (X Y : Interface S) : Setoid (Net X Y) where
  r f g := Nonempty (Iso f g)
  iseqv := ⟨fun f => ⟨Iso.refl f⟩,
    fun ⟨a⟩ => ⟨a.symm⟩, fun ⟨a⟩ ⟨b⟩ => ⟨a.trans b⟩⟩

/-- Pure boundary wiring contains no mechanisms. -/
def wire (f : Y.Port → X.Port) (typed : ∀ y, X.type (f y) = Y.type y) :
    Net X Y where
  Gen := Empty
  finite := inferInstance
  label := Empty.elim
  parents := Empty.elim
  output := Sum.inl ∘ f
  parents_typed := fun g => g.elim
  output_typed := typed
  acyclic := ⟨Empty.elim, fun g => g.elim⟩

def identity (X : Interface S) : Net X X := wire id (fun _ => rfl)

/-- The left variable inclusion into sequential gluing. -/
def left (f : Net X Y) (g : Net Y Z) : f.Var → X.Port ⊕ (f.Gen ⊕ g.Gen) :=
  Sum.map id Sum.inl

/-- Substitute the actual, possibly repeated or passed-through, output map. -/
def right (f : Net X Y) (g : Net Y Z) : g.Var → X.Port ⊕ (f.Gen ⊕ g.Gen) :=
  Sum.elim (fun y => left f g (f.output y)) (fun b => Sum.inr (Sum.inr b))

theorem left_typed (f : Net X Y) (g : Net Y Z) (v : f.Var) :
    Sum.elim X.type (S.result ∘ Sum.elim f.label g.label) (left f g v) =
      f.varType v := by cases v <;> rfl

theorem right_typed (f : Net X Y) (g : Net Y Z) (v : g.Var) :
    Sum.elim X.type (S.result ∘ Sum.elim f.label g.label) (right f g v) =
      g.varType v := by
  cases v with
  | inl y => exact (left_typed f g _).trans (f.output_typed y)
  | inr b => rfl

/-- Gluing is acyclic: all first-component ranks precede second-component ranks. -/
theorem compose_acyclic (f : Net X Y) (g : Net Y Z) :
    ∃ rank : f.Gen ⊕ g.Gen → ℕ, ∀ a b,
      Sum.inr b ∈ Sum.elim
        (fun a => (f.parents a).map (left f g))
        (fun b => (g.parents b).map (right f g)) a → rank b < rank a := by
  classical
  obtain ⟨rf, hf⟩ := f.acyclic
  obtain ⟨rg, hg⟩ := g.acyclic
  let bound := Finset.univ.sup rf + 1
  have hb (a : f.Gen) : rf a < bound :=
    Nat.lt_succ_of_le (Finset.le_sup (f := rf) (Finset.mem_univ a))
  refine ⟨Sum.elim rf (fun b => bound + rg b), ?_⟩
  intro a b h
  cases a with
  | inl a =>
    obtain ⟨v, hv, he⟩ := List.mem_map.mp h
    cases v with
    | inl x => simp [left] at he
    | inr c =>
      simp only [left, Sum.map_inr, Sum.inr.injEq] at he
      subst b
      exact hf a c hv
  | inr a =>
    obtain ⟨v, hv, he⟩ := List.mem_map.mp h
    cases v with
    | inl y =>
      cases e : f.output y with
      | inl x => simp [right, left, e] at he
      | inr c =>
        simp only [right, Sum.elim_inl, e, left, Sum.map_inr, Sum.inr.injEq] at he
        subst b
        exact lt_of_lt_of_le (hb c) (Nat.le_add_right _ _)
    | inr c =>
      simp only [right, Sum.elim_inr, Sum.inr.injEq] at he
      subst b
      exact Nat.add_lt_add_left (hg a c hv) bound

/-- Total sequential composition, with a disjoint sum of generators. -/
def comp (f : Net X Y) (g : Net Y Z) : Net X Z where
  Gen := f.Gen ⊕ g.Gen
  finite := inferInstance
  label := Sum.elim f.label g.label
  parents := Sum.elim
    (fun a => (f.parents a).map (left f g))
    (fun b => (g.parents b).map (right f g))
  output := right f g ∘ g.output
  parents_typed := by
    intro a
    cases a with
    | inl a =>
      change ((f.parents a).map (left f g)).map _ = _
      rw [List.map_map]
      exact (congrArg (fun k => (f.parents a).map k) (funext (left_typed f g))).trans
        (f.parents_typed a)
    | inr b =>
      change ((g.parents b).map (right f g)).map _ = _
      rw [List.map_map]
      exact (congrArg (fun k => (g.parents b).map k) (funext (right_typed f g))).trans
        (g.parents_typed b)
  output_typed y := (right_typed f g _).trans (g.output_typed y)
  acyclic := compose_acyclic f g

end Net
end OpenNet
