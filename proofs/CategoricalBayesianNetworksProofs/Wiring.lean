import CategoricalBayesianNetworksProofs.Tensor
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Pure wiring and a structural sliding lemma

Pure wiring is contravariant in functions on ports. It can copy, permute or
discard ports but never creates a mechanism. The sliding lemma below is an
incidence-preserving renumbering theorem. Its premises are equations for labels,
individual ordered parent lists and output maps, not assumed category laws.
-/

namespace OpenNet
open CategoryTheory
variable {S : Signature} {X Y Z X' Y' : Interface S}

def wire (p : Y.Port → X.Port) (hp : ∀ y, X.type (p y) = Y.type y) : X ⟶ Y :=
  ofNet (Net.wire p hp)

theorem wire_congr {p q : Y.Port → X.Port} {hp hq} (h : p = q) :
    wire p hp = wire q hq := by subst q; rfl

@[simp] theorem wire_id (X : Interface S) : wire (id : X.Port → X.Port) (fun _ => rfl) =
    𝟙 X := rfl

@[simp] theorem wire_comp (p : Y.Port → X.Port) (q : Z.Port → Y.Port) (hp hq) :
    wire p hp ≫ wire q hq = wire (p ∘ q) (fun z => (hp (q z)).trans (hq z)) := by
  apply Quotient.sound
  refine ⟨⟨Equiv.emptySum Empty Empty, ?_, ?_, ?_⟩⟩
  · rintro (a | a) <;> exact a.elim
  · rintro (a | a) <;> exact a.elim
  · intro z; rfl

@[simp] theorem wire_tensor (p : Y.Port → X.Port) (q : Y'.Port → X'.Port) (hp hq) :
    tensor (wire p hp) (wire q hq) =
      wire (Sum.map p q) (fun y => by cases y with
        | inl y => exact hp y
        | inr y => exact hq y) := by
  apply Quotient.sound
  refine ⟨⟨Equiv.emptySum Empty Empty, ?_, ?_, ?_⟩⟩
  · rintro (a | a) <;> exact a.elim
  · rintro (a | a) <;> exact a.elim
  · rintro (y | y) <;> rfl

def portIso (e : X.Port ≃ Y.Port) (he : ∀ x, Y.type (e x) = X.type x) : X ≅ Y where
  hom := wire e.symm (fun y => by simpa using (he (e.symm y)).symm)
  inv := wire e he
  hom_inv_id := by
    rw [wire_comp, ← wire_id]
    apply wire_congr; funext x; exact e.symm_apply_apply x
  inv_hom_id := by
    rw [wire_comp, ← wire_id]
    apply wire_congr; funext y; exact e.apply_symm_apply y

namespace Net

def slide (f : Net X Y) (g : Net X' Y')
    (i : X'.Port → X.Port) (o : Y'.Port → Y.Port) (hi ho)
    (e : f.Gen ≃ g.Gen)
    (hl : ∀ a, g.label (e a) = f.label a)
    (hp : ∀ a, (g.parents (e a)).map (Sum.map i id) =
      (f.parents a).map (Sum.map id e))
    (hout : ∀ y, Sum.map i id (g.output y) = Sum.map id e (f.output (o y))) :
    Iso (f.comp (Net.wire o ho)) ((Net.wire i hi).comp g) where
  gen := ((Equiv.sumEmpty f.Gen Empty).trans e).trans (Equiv.emptySum Empty g.Gen).symm
  label a := by
    rcases a with a | a
    · exact hl a
    · exact a.elim
  parents a := by
    rcases a with a | a
    · change (g.parents (e a)).map _ = (((f.parents a).map _).map _)
      have h := congrArg (List.map (Sum.map id (Sum.inr : g.Gen → Empty ⊕ g.Gen))) (hp a)
      simp only [List.map_map] at h ⊢
      have L : right (Net.wire i hi) g =
          (Sum.map id (Sum.inr : g.Gen → Empty ⊕ g.Gen)) ∘ Sum.map i id := by
        funext v; cases v <;> rfl
      have R : (Sum.map id
          (((Equiv.sumEmpty f.Gen Empty).trans e).trans (Equiv.emptySum Empty g.Gen).symm)) ∘
          left f (Net.wire o ho) =
          (Sum.map id (Sum.inr : g.Gen → Empty ⊕ g.Gen)) ∘ Sum.map id e := by
        funext v; cases v <;> rfl
      exact (congrArg (fun k => (g.parents (e a)).map k) L).trans
        (h.trans (congrArg (fun k => (f.parents a).map k) R).symm)
    · exact a.elim
  output y := by
    have h := congrArg (Sum.map id (Sum.inr : g.Gen → Empty ⊕ g.Gen)) (hout y)
    change right (Net.wire i hi) g (g.output y) = Sum.map _ _ (left f _ (f.output (o y)))
    have L (v : g.Var) : right (Net.wire i hi) g v =
        Sum.map id (Sum.inr : g.Gen → Empty ⊕ g.Gen) (Sum.map i id v) := by
      cases v <;> rfl
    have R (v : f.Var) : Sum.map id
        (((Equiv.sumEmpty f.Gen Empty).trans e).trans (Equiv.emptySum Empty g.Gen).symm)
        (left f (Net.wire o ho) v) =
        Sum.map id (Sum.inr : g.Gen → Empty ⊕ g.Gen) (Sum.map id e v) := by
      cases v <;> rfl
    exact (L _).trans (h.trans (R _).symm)

end Net

theorem wire_slide (f : Net X Y) (g : Net X' Y')
    (i : X'.Port → X.Port) (o : Y'.Port → Y.Port) (hi ho)
    (e : f.Gen ≃ g.Gen)
    (hl : ∀ a, g.label (e a) = f.label a)
    (hp : ∀ a, (g.parents (e a)).map (Sum.map i id) =
      (f.parents a).map (Sum.map id e))
    (hout : ∀ y, Sum.map i id (g.output y) = Sum.map id e (f.output (o y))) :
    ofNet f ≫ wire o ho = wire i hi ≫ ofNet g :=
  Quotient.sound ⟨Net.slide f g i o hi ho e hl hp hout⟩

end OpenNet
