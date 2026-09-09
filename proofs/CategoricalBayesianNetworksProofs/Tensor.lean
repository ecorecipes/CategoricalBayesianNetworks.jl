import CategoricalBayesianNetworksProofs.Category

/-!
# Disjoint-union tensor

The tensor keeps both sets of generators, including hidden components. Its two
variable maps are injective and disjoint. The interchange isomorphism merely
reorders the four summands of generators.
-/

namespace OpenNet
variable {S : Signature} {X Y Z W X' Y' Z' : Interface S}
namespace Net

def tinl (f : Net X Y) (g : Net X' Y') : f.Var → (X.sum X').Port ⊕ (f.Gen ⊕ g.Gen) :=
  Sum.map Sum.inl Sum.inl

def tinr (f : Net X Y) (g : Net X' Y') : g.Var → (X.sum X').Port ⊕ (f.Gen ⊕ g.Gen) :=
  Sum.map Sum.inr Sum.inr

theorem tinl_typed (f : Net X Y) (g : Net X' Y') (v : f.Var) :
    Sum.elim (X.sum X').type (S.result ∘ Sum.elim f.label g.label) (tinl f g v) =
      f.varType v := by cases v <;> rfl

theorem tinr_typed (f : Net X Y) (g : Net X' Y') (v : g.Var) :
    Sum.elim (X.sum X').type (S.result ∘ Sum.elim f.label g.label) (tinr f g v) =
      g.varType v := by cases v <;> rfl

theorem tensor_acyclic (f : Net X Y) (g : Net X' Y') :
    ∃ rank : f.Gen ⊕ g.Gen → ℕ, ∀ a b,
      Sum.inr b ∈ Sum.elim
        (fun a => (f.parents a).map (tinl f g))
        (fun b => (g.parents b).map (tinr f g)) a → rank b < rank a := by
  obtain ⟨rf, hf⟩ := f.acyclic
  obtain ⟨rg, hg⟩ := g.acyclic
  refine ⟨Sum.elim rf rg, ?_⟩
  intro a b h
  cases a with
  | inl a =>
    obtain ⟨v, hv, he⟩ := List.mem_map.mp h
    cases v with
    | inl x => simp [tinl] at he
    | inr c =>
      simp only [tinl, Sum.map_inr, Sum.inr.injEq] at he
      subst b
      exact hf a c hv
  | inr a =>
    obtain ⟨v, hv, he⟩ := List.mem_map.mp h
    cases v with
    | inl x => simp [tinr] at he
    | inr c =>
      simp only [tinr, Sum.map_inr, Sum.inr.injEq] at he
      subst b
      exact hg a c hv

def tensor (f : Net X Y) (g : Net X' Y') : Net (X.sum X') (Y.sum Y') where
  Gen := f.Gen ⊕ g.Gen
  finite := inferInstance
  label := Sum.elim f.label g.label
  parents := Sum.elim
    (fun a => (f.parents a).map (tinl f g))
    (fun b => (g.parents b).map (tinr f g))
  output := Sum.elim (tinl f g ∘ f.output) (tinr f g ∘ g.output)
  parents_typed := by
    intro a
    cases a with
    | inl a =>
      change ((f.parents a).map (tinl f g)).map _ = _
      rw [List.map_map]
      exact (congrArg (fun k => (f.parents a).map k) (funext (tinl_typed f g))).trans
        (f.parents_typed a)
    | inr b =>
      change ((g.parents b).map (tinr f g)).map _ = _
      rw [List.map_map]
      exact (congrArg (fun k => (g.parents b).map k) (funext (tinr_typed f g))).trans
        (g.parents_typed b)
  output_typed := by
    intro y
    cases y with
    | inl y => exact (tinl_typed f g _).trans (f.output_typed y)
    | inr y => exact (tinr_typed f g _).trans (g.output_typed y)
  acyclic := tensor_acyclic f g

def Iso.tensor {f f' : Net X Y} {g g' : Net X' Y'}
    (a : Iso f f') (b : Iso g g') : Iso (f.tensor g) (f'.tensor g') where
  gen := Equiv.sumCongr a.gen b.gen
  label x := by
    cases x with
    | inl x => exact a.label x
    | inr x => exact b.label x
  parents x := by
    cases x with
    | inl x =>
      change (f'.parents (a.gen x)).map _ = ((f.parents x).map _).map _
      rw [a.parents, List.map_map, List.map_map]
      congr 1; funext v; cases v <;> rfl
    | inr x =>
      change (g'.parents (b.gen x)).map _ = ((g.parents x).map _).map _
      rw [b.parents, List.map_map, List.map_map]
      congr 1; funext v; cases v <;> rfl
  output y := by
    cases y with
    | inl y =>
      change tinl f' g' (f'.output y) = Sum.map _ _ (tinl f g (f.output y))
      rw [a.output]
      cases f.output y <;> rfl
    | inr y =>
      change tinr f' g' (g'.output y) = Sum.map _ _ (tinr f g (g.output y))
      rw [b.output]
      cases g.output y <;> rfl

def exchange (A B C D : Type) : (A ⊕ B) ⊕ (C ⊕ D) ≃ (A ⊕ C) ⊕ (B ⊕ D) where
  toFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl))
    (Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr))
  invFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl))
    (Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr))
  left_inv x := by rcases x with (a | b) | (c | d) <;> rfl
  right_inv x := by rcases x with (a | b) | (c | d) <;> rfl

def interchange_iso (f : Net X Y) (g : Net X' Y') (h : Net Y Z) (k : Net Y' Z') :
    Iso ((f.tensor g).comp (h.tensor k)) ((f.comp h).tensor (g.comp k)) where
  gen := exchange f.Gen g.Gen h.Gen k.Gen
  label x := by rcases x with (a | b) | (c | d) <;> rfl
  parents x := by
    rcases x with (a | b) | (c | d)
    · change ((f.parents a).map _).map _ = (((f.parents a).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v; cases v <;> rfl
    · change ((g.parents b).map _).map _ = (((g.parents b).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v; cases v <;> rfl
    · change ((h.parents c).map _).map _ = (((h.parents c).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v
      cases v with
      | inl y =>
        cases e : f.output y <;>
          (simp [comp, tensor, right, left, tinl, Function.comp_def, e]; try rfl)
      | inr c => rfl
    · change ((k.parents d).map _).map _ = (((k.parents d).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v
      cases v with
      | inl y =>
        cases e : g.output y <;>
          (simp [comp, tensor, right, left, tinr, Function.comp_def, e]; try rfl)
      | inr d => rfl
  output z := by
    cases z with
    | inl z =>
      cases e : h.output z with
      | inl y => cases ef : f.output y <;> (simp [comp, tensor, right, left, tinl, e, ef]; try rfl)
      | inr a => simp [comp, tensor, right, left, tinl, e]; rfl
    | inr z =>
      cases e : k.output z with
      | inl y => cases eg : g.output y <;> (simp [comp, tensor, right, left, tinr, e, eg]; try rfl)
      | inr a => simp [comp, tensor, right, left, tinr, e]; rfl

end Net

def tensor (f : Hom X Y) (g : Hom X' Y') : Hom (X.sum X') (Y.sum Y') :=
  Quotient.liftOn₂ f g (fun a b => ofNet (a.tensor b))
    (fun _ _ _ _ ⟨a⟩ ⟨b⟩ => Quotient.sound ⟨a.tensor b⟩)

@[simp] theorem tensor_ofNet (f : Net X Y) (g : Net X' Y') :
    tensor (ofNet f) (ofNet g) = ofNet (f.tensor g) := rfl

theorem tensor_comp (f : Hom X Y) (g : Hom X' Y') (h : Hom Y Z) (k : Hom Y' Z') :
    compose (tensor f g) (tensor h k) = tensor (compose f h) (compose g k) := by
  induction f, g using Quotient.inductionOn₂ with | _ f g =>
    induction h, k using Quotient.inductionOn₂ with | _ h k =>
      exact Quotient.sound ⟨Net.interchange_iso f g h k⟩

end OpenNet
