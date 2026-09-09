import CategoricalBayesianNetworksProofs.CopyDiscard
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-!
# Typed finite state assignments

An interpretation assigns an arbitrary finite state type to each signature type.
The state types need not be inhabited. Local kernels are genuine real-valued
tables on ordered, heterogeneously typed parent values and one child value.
They are nonnegative and normalized on every correctly typed parent row.
Ill-typed rows are not used.

Assignments retain the type tag with each value. This equivalent presentation
of dependent tuples lets renumbering and gluing preserve values literally,
without inserting arbitrary state bijections.
-/

namespace OpenNet

structure Interpretation (S : Signature) where
  states : S.Ty → Type
  finite : ∀ t, Fintype (states t)
  weight : S.Label → List (Sigma states) → Sigma states → ℝ
  nonneg : ∀ l p s, 0 ≤ weight l p s
  normalized : ∀ l p, p.map Sigma.fst = S.inputs l →
    @Finset.sum (states (S.result l)) ℝ _ (@Finset.univ _ (finite _))
      (fun s => weight l p ⟨S.result l, s⟩) = 1

attribute [instance] Interpretation.finite

namespace Interpretation
variable {S : Signature} (I : Interpretation S)

abbrev Value := Sigma I.states

@[ext] structure Assignment {A : Type} (σ : A → S.Ty) where
  value : A → I.Value
  typed : ∀ a, (value a).1 = σ a

instance {A : Type} {σ : A → S.Ty} : CoeFun (I.Assignment σ) (fun _ => A → I.Value) :=
  ⟨Assignment.value⟩

def Assignment.ofPi {A : Type} {σ : A → S.Ty} (x : ∀ a, I.states (σ a)) :
    I.Assignment σ :=
  ⟨fun a => ⟨σ a, x a⟩, fun _ => rfl⟩

def Assignment.toPi {A : Type} {σ : A → S.Ty} (x : I.Assignment σ) :
    ∀ a, I.states (σ a) :=
  fun a => cast (congrArg I.states (x.typed a)) (x a).2

def Assignment.piEquiv {A : Type} (σ : A → S.Ty) :
    (∀ a, I.states (σ a)) ≃ I.Assignment σ where
  toFun := Assignment.ofPi I
  invFun := Assignment.toPi I
  left_inv x := by funext a; rfl
  right_inv x := by
    apply Assignment.ext
    funext a
    change (⟨σ a, cast (congrArg I.states (x.typed a)) (x a).2⟩ : I.Value) = x a
    exact Sigma.ext (x.typed a).symm (cast_heq _ _)

noncomputable instance assignmentFinite {A : Type} [Fintype A] (σ : A → S.Ty) :
    Fintype (I.Assignment σ) := by
  classical
  exact Fintype.ofEquiv (∀ a, I.states (σ a)) (Assignment.piEquiv I σ)

noncomputable instance assignmentDecidableEq {A : Type} (σ : A → S.Ty) :
    DecidableEq (I.Assignment σ) := Classical.decEq _

def Assignment.reindex {A B : Type} {σ : A → S.Ty} {τ : B → S.Ty}
    (x : I.Assignment σ) (f : B → A) (hf : ∀ b, σ (f b) = τ b) :
    I.Assignment τ :=
  ⟨fun b => x (f b), fun b => (x.typed _).trans (hf b)⟩

@[simp] theorem Assignment.reindex_apply {A B : Type} {σ : A → S.Ty} {τ : B → S.Ty}
    (x : I.Assignment σ) (f : B → A) (hf : ∀ b, σ (f b) = τ b) (b : B) :
    Assignment.reindex I x f hf b = x (f b) := rfl

def Assignment.join {A B : Type} {σ : A → S.Ty} {τ : B → S.Ty}
    (x : I.Assignment σ) (y : I.Assignment τ) : I.Assignment (Sum.elim σ τ) :=
  ⟨Sum.elim x.value y.value, fun a => by
    cases a with
    | inl a => exact x.typed a
    | inr b => exact y.typed b⟩

@[simp] theorem Assignment.join_inl {A B : Type} {σ : A → S.Ty} {τ : B → S.Ty}
    (x : I.Assignment σ) (y : I.Assignment τ) (a : A) :
    Assignment.join I x y (Sum.inl a) = x a := rfl

@[simp] theorem Assignment.join_inr {A B : Type} {σ : A → S.Ty} {τ : B → S.Ty}
    (x : I.Assignment σ) (y : I.Assignment τ) (b : B) :
    Assignment.join I x y (Sum.inr b) = y b := rfl

def Assignment.sumEquiv {A B : Type} (σ : A → S.Ty) (τ : B → S.Ty) :
    I.Assignment (Sum.elim σ τ) ≃ I.Assignment σ × I.Assignment τ where
  toFun z := ⟨Assignment.reindex I z Sum.inl (fun _ => rfl),
    Assignment.reindex I z Sum.inr (fun _ => rfl)⟩
  invFun z := Assignment.join I z.1 z.2
  left_inv z := by apply Assignment.ext; funext a; cases a <;> rfl
  right_inv z := by cases z; rfl

def Assignment.splitEquiv {A B : Type} (σ : A ⊕ B → S.Ty) :
    I.Assignment σ ≃ I.Assignment (σ ∘ Sum.inl) × I.Assignment (σ ∘ Sum.inr) where
  toFun z := ⟨Assignment.reindex I z Sum.inl (fun _ => rfl),
    Assignment.reindex I z Sum.inr (fun _ => rfl)⟩
  invFun z := ⟨Sum.elim z.1.value z.2.value, fun a => by
    cases a with
    | inl a => exact z.1.typed a
    | inr b => exact z.2.typed b⟩
  left_inv z := by apply Assignment.ext; funext a; cases a <;> rfl
  right_inv z := by cases z; rfl

def sumLabelsEquiv {A B : Type} (l : A → S.Label) (m : B → S.Label) :
    I.Assignment (S.result ∘ Sum.elim l m) ≃
      I.Assignment (S.result ∘ l) × I.Assignment (S.result ∘ m) :=
  Assignment.splitEquiv I _

def Assignment.renameEquiv {A B : Type} {σ : A → S.Ty} {τ : B → S.Ty}
    (e : A ≃ B) (he : ∀ a, τ (e a) = σ a) :
    I.Assignment σ ≃ I.Assignment τ where
  toFun x := Assignment.reindex I x e.symm (fun b => by simpa using (he (e.symm b)).symm)
  invFun y := Assignment.reindex I y e he
  left_inv x := by apply Assignment.ext; funext a; exact congrArg x (e.symm_apply_apply a)
  right_inv y := by apply Assignment.ext; funext b; exact congrArg y (e.apply_symm_apply b)

def Assignment.empty : I.Assignment (Empty.elim : Empty → S.Ty) :=
  ⟨Empty.elim, fun a => a.elim⟩

instance Assignment.emptyUnique {A : Type} [IsEmpty A] (σ : A → S.Ty) :
    Unique (I.Assignment σ) where
  default := ⟨fun a => isEmptyElim a, fun a => isEmptyElim a⟩
  uniq x := by apply Assignment.ext; funext a; exact isEmptyElim a

theorem Assignment.join_injective {A B : Type} {σ : A → S.Ty} {τ : B → S.Ty}
    (x x' : I.Assignment σ) (y y' : I.Assignment τ) :
    Assignment.join I x y = Assignment.join I x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have hh := congrArg (Assignment.sumEquiv I σ τ) h
    exact Prod.mk.inj hh
  · rintro ⟨rfl, rfl⟩
    rfl

abbrev Boundary (X : Interface S) := I.Assignment X.type
abbrev Internal {X Y : Interface S} (f : Net X Y) :=
  I.Assignment (S.result ∘ f.label)

def valuation {X Y : Interface S} (f : Net X Y)
    (x : I.Boundary X) (z : I.Internal f) : I.Assignment f.varType :=
  Assignment.join I x z

def parents {X Y : Interface S} (f : Net X Y)
    (x : I.Boundary X) (z : I.Internal f) (a : f.Gen) : List I.Value :=
  (f.parents a).map (I.valuation f x z).value

theorem parents_typed {X Y : Interface S} (f : Net X Y)
    (x : I.Boundary X) (z : I.Internal f) (a : f.Gen) :
    (I.parents f x z a).map Sigma.fst = S.inputs (f.label a) := by
  unfold parents
  rw [List.map_map]
  exact (congrArg (fun k => (f.parents a).map k)
    (funext (I.valuation f x z).typed)).trans (f.parents_typed a)

def read {X Y : Interface S} (f : Net X Y)
    (x : I.Boundary X) (z : I.Internal f) : I.Boundary Y :=
  Assignment.reindex I (I.valuation f x z) f.output f.output_typed

end Interpretation
end OpenNet
