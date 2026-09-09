import CategoricalBayesianNetworksProofs.Syntax
import Mathlib.CategoryTheory.Category.Basic

/-!
# A category by structural isomorphism, not by equations

The only quotient relation is existence of a bijection on generators preserving
labels, ordered parent lists and the explicit output leg. The category laws are
proved by the empty-sum and sum-associativity bijections; no category equations
are included in that relation.
-/

namespace OpenNet
variable {S : Signature} {X Y Z W : Interface S}
namespace Net

def Iso.comp {f f' : Net X Y} {g g' : Net Y Z}
    (a : Iso f f') (b : Iso g g') : Iso (f.comp g) (f'.comp g') where
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
      congr 1
      funext v
      cases v <;> rfl
    | inr x =>
      change (g'.parents (b.gen x)).map _ = ((g.parents x).map _).map _
      rw [b.parents, List.map_map, List.map_map]
      congr 1
      funext v
      cases v with
      | inl y =>
        simp only [Function.comp_apply, Sum.map_inl, id_eq, right, Sum.elim_inl, a.output]
        cases f.output y <;> rfl
      | inr y => rfl
  output y := by
    simp only [Net.comp, Function.comp_apply, b.output]
    cases g.output y with
    | inl y =>
      simp only [Sum.map_inl, id_eq, right, Sum.elim_inl, a.output]
      cases f.output y <;> rfl
    | inr b => rfl

def id_comp_iso (f : Net X Y) : Iso ((identity X).comp f) f where
  gen := Equiv.emptySum Empty f.Gen
  label x := by rcases x with x | x; exact x.elim; rfl
  parents x := by
    rcases x with x | x
    · exact x.elim
    · change f.parents x = ((f.parents x).map (right (identity X) f)).map _
      rw [List.map_map]
      have h : (Sum.map id (Equiv.emptySum Empty f.Gen)) ∘ right (identity X) f = id := by
        funext v
        cases v <;> rfl
      exact ((congrArg (fun k => (f.parents x).map k) h).trans (List.map_id _)).symm
  output y := by
    change f.output y = Sum.map _ _ (right (identity X) f (f.output y))
    cases f.output y <;> rfl

def comp_id_iso (f : Net X Y) : Iso (f.comp (identity Y)) f where
  gen := Equiv.sumEmpty f.Gen Empty
  label x := by rcases x with x | x; rfl; exact x.elim
  parents x := by
    rcases x with x | x
    · change f.parents x = ((f.parents x).map (left f (identity Y))).map _
      rw [List.map_map]
      have h : (Sum.map id (Equiv.sumEmpty f.Gen Empty)) ∘ left f (identity Y) = id := by
        funext v
        cases v <;> rfl
      exact ((congrArg (fun k => (f.parents x).map k) h).trans (List.map_id _)).symm
    · exact x.elim
  output y := by change _ = Sum.map _ _ (left f _ (f.output y)); cases f.output y <;> rfl

def assoc_iso (f : Net X Y) (g : Net Y Z) (h : Net Z W) :
    Iso ((f.comp g).comp h) (f.comp (g.comp h)) where
  gen := Equiv.sumAssoc f.Gen g.Gen h.Gen
  label a := by rcases a with (a | a) | a <;> rfl
  parents a := by
    rcases a with (a | a) | a
    · change (f.parents a).map _ = (((f.parents a).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v; cases v <;> rfl
    · change ((g.parents a).map _).map _ = (((g.parents a).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v
      cases v with
      | inl y =>
        change right f (g.comp h) (Sum.inl y) = _
        cases e : f.output y <;> simp [right, left, e, Function.comp_def] <;> rfl
      | inr b => rfl
    · change ((h.parents a).map _).map _ = ((h.parents a).map _).map _
      simp only [List.map_map]
      congr 1; funext v
      cases v with
      | inl z =>
        cases eg : g.output z with
        | inl y =>
          cases ef : f.output y <;> (simp [comp, right, left, eg, ef, Function.comp_def]; try rfl)
        | inr b => simp [comp, right, left, eg, Function.comp_def]; rfl
      | inr c => rfl
  output w := by
    cases eh : h.output w with
    | inl z =>
      cases eg : g.output z with
      | inl y => cases ef : f.output y <;> (simp [comp, right, left, eh, eg, ef]; try rfl)
      | inr b => simp [comp, right, left, eh, eg]; rfl
    | inr c => simp [comp, right, left, eh]; rfl

end Net

abbrev Hom (X Y : Interface S) := Quotient (Net.setoid X Y)

def ofNet (f : Net X Y) : Hom X Y := Quotient.mk _ f

theorem ofNet_eq_iff (f g : Net X Y) :
    ofNet f = ofNet g ↔ Nonempty (Net.Iso f g) := Quotient.eq

def compose (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Quotient.liftOn₂ f g (fun a b => ofNet (a.comp b))
    (fun _ _ _ _ ⟨a⟩ ⟨b⟩ => Quotient.sound ⟨a.comp b⟩)

@[simp] theorem compose_ofNet (f : Net X Y) (g : Net Y Z) :
    compose (ofNet f) (ofNet g) = ofNet (f.comp g) := rfl

instance category : CategoryTheory.Category (Interface S) where
  Hom := Hom
  id X := ofNet (Net.identity X)
  comp := compose
  id_comp := by
    intro X Y f
    induction f using Quotient.inductionOn with | _ f =>
      exact Quotient.sound ⟨Net.id_comp_iso f⟩
  comp_id := by
    intro X Y f
    induction f using Quotient.inductionOn with | _ f =>
      exact Quotient.sound ⟨Net.comp_id_iso f⟩
  assoc := by
    intro X Y Z W f g h
    induction f, g using Quotient.inductionOn₂ with | _ f g =>
      induction h using Quotient.inductionOn with | _ h =>
        exact Quotient.sound ⟨Net.assoc_iso f g h⟩

end OpenNet
