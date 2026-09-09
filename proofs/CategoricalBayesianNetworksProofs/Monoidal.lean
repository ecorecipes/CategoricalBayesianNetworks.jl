import CategoricalBayesianNetworksProofs.Wiring
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Symmetric monoidal coherence

The associator, unitors and symmetry are pure bijective wiring on the feet.
Naturality for arbitrary networks follows by explicit generator bijections and
ordered-incidence equations. Pentagon, triangle, hexagons and involutivity reduce
to actual functions on ports, rather than a quotient by coherence equations.
-/

namespace OpenNet
open CategoryTheory
variable {S : Signature}

def assocIso (X Y Z : Interface S) : (X.sum Y).sum Z ≅ X.sum (Y.sum Z) :=
  portIso (Equiv.sumAssoc X.Port Y.Port Z.Port)
    (fun x => by rcases x with (x | y) | z <;> rfl)

def leftIso (X : Interface S) : (Interface.empty S).sum X ≅ X :=
  portIso (Equiv.emptySum Empty X.Port)
    (fun x => by rcases x with x | x; exact x.elim; rfl)

def rightIso (X : Interface S) : X.sum (Interface.empty S) ≅ X :=
  portIso (Equiv.sumEmpty X.Port Empty)
    (fun x => by rcases x with x | x; rfl; exact x.elim)

def swapIso (X Y : Interface S) : X.sum Y ≅ Y.sum X :=
  portIso (Equiv.sumComm X.Port Y.Port)
    (fun x => by cases x <;> rfl)

theorem assoc_natural {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Interface S}
    (f : Hom X₁ Y₁) (g : Hom X₂ Y₂) (h : Hom X₃ Y₃) :
    tensor (tensor f g) h ≫ (assocIso Y₁ Y₂ Y₃).hom =
      (assocIso X₁ X₂ X₃).hom ≫ tensor f (tensor g h) := by
  induction f, g using Quotient.inductionOn₂ with | _ f g =>
    induction h using Quotient.inductionOn with | _ h =>
      refine wire_slide ((f.tensor g).tensor h) (f.tensor (g.tensor h))
        _ _ _ _ (Equiv.sumAssoc f.Gen g.Gen h.Gen) ?_ ?_ ?_
      · rintro ((a | b) | c) <;> rfl
      · rintro ((a | b) | c)
        · change ((f.parents a).map _).map _ = (((f.parents a).map _).map _).map _
          simp only [List.map_map]
          congr 1; funext v; cases v <;> rfl
        · change (((g.parents b).map _).map _).map _ =
            (((g.parents b).map _).map _).map _
          simp only [List.map_map]
          congr 1; funext v; cases v <;> rfl
        · change (((h.parents c).map _).map _).map _ = ((h.parents c).map _).map _
          simp only [List.map_map]
          congr 1; funext v; cases v <;> rfl
      · rintro (y | (y | y))
        · change Sum.map _ _ (Net.tinl f (g.tensor h) (f.output y)) =
            Sum.map _ _ (Net.tinl (f.tensor g) h (Net.tinl f g (f.output y)))
          cases f.output y <;> rfl
        · change Sum.map _ _ (Net.tinr f (g.tensor h) (Net.tinl g h (g.output y))) =
            Sum.map _ _ (Net.tinl (f.tensor g) h (Net.tinr f g (g.output y)))
          cases g.output y <;> rfl
        · change Sum.map _ _ (Net.tinr f (g.tensor h) (Net.tinr g h (h.output y))) =
            Sum.map _ _ (Net.tinr (f.tensor g) h (h.output y))
          cases h.output y <;> rfl

theorem left_natural {X Y : Interface S} (f : Hom X Y) :
    tensor (𝟙 (Interface.empty S)) f ≫ (leftIso Y).hom =
      (leftIso X).hom ≫ f := by
  induction f using Quotient.inductionOn with | _ f =>
    refine wire_slide ((Net.identity (Interface.empty S)).tensor f) f
      _ _ _ _ (Equiv.emptySum Empty f.Gen) ?_ ?_ ?_
    · rintro (a | a); exact a.elim; rfl
    · rintro (a | a)
      · exact a.elim
      · change (f.parents a).map _ = ((f.parents a).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl
    · intro y
      change Sum.map _ _ (f.output y) = Sum.map _ _ (Net.tinr _ _ (f.output y))
      cases f.output y <;> rfl

theorem right_natural {X Y : Interface S} (f : Hom X Y) :
    tensor f (𝟙 (Interface.empty S)) ≫ (rightIso Y).hom =
      (rightIso X).hom ≫ f := by
  induction f using Quotient.inductionOn with | _ f =>
    refine wire_slide (f.tensor (Net.identity (Interface.empty S))) f
      _ _ _ _ (Equiv.sumEmpty f.Gen Empty) ?_ ?_ ?_
    · rintro (a | a); rfl; exact a.elim
    · rintro (a | a)
      · change (f.parents a).map _ = ((f.parents a).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl
      · exact a.elim
    · intro y
      change Sum.map _ _ (f.output y) = Sum.map _ _ (Net.tinl _ _ (f.output y))
      cases f.output y <;> rfl

theorem swap_natural {X Y X' Y' : Interface S} (f : Hom X Y) (g : Hom X' Y') :
    tensor f g ≫ (swapIso Y Y').hom = (swapIso X X').hom ≫ tensor g f := by
  induction f, g using Quotient.inductionOn₂ with | _ f g =>
    refine wire_slide (f.tensor g) (g.tensor f)
      _ _ _ _ (Equiv.sumComm f.Gen g.Gen) ?_ ?_ ?_
    · rintro (a | b) <;> rfl
    · rintro (a | b)
      · change ((f.parents a).map _).map _ = ((f.parents a).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl
      · change ((g.parents b).map _).map _ = ((g.parents b).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl
    · rintro (y | y)
      · change Sum.map _ _ (Net.tinl _ _ (g.output y)) =
          Sum.map _ _ (Net.tinr _ _ (g.output y))
        cases g.output y <;> rfl
      · change Sum.map _ _ (Net.tinr _ _ (f.output y)) =
          Sum.map _ _ (Net.tinl _ _ (f.output y))
        cases f.output y <;> rfl

instance monoidalStruct : MonoidalCategoryStruct (Interface S) where
  tensorObj := Interface.sum
  tensorHom := tensor
  whiskerLeft X _ _ f := tensor (𝟙 X) f
  whiskerRight f Y := tensor f (𝟙 Y)
  tensorUnit := Interface.empty S
  associator := assocIso
  leftUnitor := leftIso
  rightUnitor := rightIso

theorem tensor_id (X Y : Interface S) : tensor (𝟙 X) (𝟙 Y) = 𝟙 (X.sum Y) := by
  rw [← wire_id X, ← wire_id Y, wire_tensor, ← wire_id]
  apply wire_congr
  funext v; cases v <;> rfl

instance monoidal : MonoidalCategory (Interface S) :=
  MonoidalCategory.ofTensorHom
    tensor_id
    (by intros; rfl)
    (by intros; rfl)
    tensor_comp
    assoc_natural
    left_natural
    right_natural
    (by
      intro W X Y Z
      change tensor (assocIso W X Y).hom (𝟙 Z) ≫
        (assocIso W (X.sum Y) Z).hom ≫ tensor (𝟙 W) (assocIso X Y Z).hom =
        (assocIso (W.sum X) Y Z).hom ≫ (assocIso W X (Y.sum Z)).hom
      simp only [assocIso, portIso, ← wire_id, wire_tensor, wire_comp]
      apply wire_congr
      funext v
      rcases v with w | (x | (y | z)) <;> rfl)
    (by
      intro X Y
      change (assocIso X (Interface.empty S) Y).hom ≫ tensor (𝟙 X) (leftIso Y).hom =
        tensor (rightIso X).hom (𝟙 Y)
      simp only [assocIso, leftIso, rightIso, portIso, ← wire_id, wire_tensor, wire_comp]
      apply wire_congr
      funext v
      cases v <;> rfl)

instance symmetric : SymmetricCategory (Interface S) where
  braiding := swapIso
  braiding_naturality_right := by intros X Y Z f; exact swap_natural (𝟙 X) f
  braiding_naturality_left := by intros X Y f Z; exact swap_natural f (𝟙 Z)
  hexagon_forward := by
    intro X Y Z
    change (assocIso X Y Z).hom ≫ (swapIso X (Y.sum Z)).hom ≫ (assocIso Y Z X).hom =
      tensor (swapIso X Y).hom (𝟙 Z) ≫
        (assocIso Y X Z).hom ≫ tensor (𝟙 Y) (swapIso X Z).hom
    simp only [assocIso, swapIso, portIso, ← wire_id, wire_tensor, wire_comp]
    apply wire_congr
    funext v
    rcases v with y | (z | x) <;> rfl
  hexagon_reverse := by
    intro X Y Z
    change (assocIso X Y Z).inv ≫ (swapIso (X.sum Y) Z).hom ≫ (assocIso Z X Y).inv =
      tensor (𝟙 X) (swapIso Y Z).hom ≫
        (assocIso X Z Y).inv ≫ tensor (swapIso X Z).hom (𝟙 Y)
    simp only [assocIso, swapIso, portIso, ← wire_id, wire_tensor, wire_comp]
    apply wire_congr
    funext v
    rcases v with (z | x) | y <;> rfl
  symmetry := by
    intro X Y
    change (swapIso X Y).hom ≫ (swapIso Y X).hom = 𝟙 (X.sum Y)
    simp only [swapIso, portIso, wire_comp, ← wire_id]
    apply wire_congr
    funext v
    cases v <;> rfl

end OpenNet
