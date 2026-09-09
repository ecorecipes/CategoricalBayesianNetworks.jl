import CategoricalBayesianNetworksProofs.Monoidal
import Mathlib.CategoryTheory.CopyDiscardCategory.Basic

/-!
# Copy and discard on the feet

Each finite typed foot has the canonical commutative comonoid structure:
copy is the codiagonal on ports, read contravariantly, and discard has an empty
output foot. These structures are coherent with tensor and the empty unit.
There is deliberately no Markov-category instance: deleting the output of a
mechanism does not erase that hidden mechanism in raw structural syntax.
-/

namespace OpenNet
open CategoryTheory MonoidalCategory
variable {S : Signature}

def copy (X : Interface S) : X ⟶ X.sum X :=
  wire (Sum.elim id id) (fun y => by cases y <;> rfl)

def discard (X : Interface S) : X ⟶ Interface.empty S :=
  wire Empty.elim (fun y => y.elim)

instance comonoid (X : Interface S) : ComonObj X where
  counit := discard X
  comul := copy X
  counit_comul := by
    change copy X ≫ tensor (discard X) (𝟙 X) = (leftIso X).inv
    simp only [copy, discard, leftIso, portIso, ← wire_id, wire_tensor, wire_comp]
    apply wire_congr
    funext v
    rcases v with v | v
    · exact v.elim
    · rfl
  comul_counit := by
    change copy X ≫ tensor (𝟙 X) (discard X) = (rightIso X).inv
    simp only [copy, discard, rightIso, portIso, ← wire_id, wire_tensor, wire_comp]
    apply wire_congr
    funext v
    rcases v with v | v
    · rfl
    · exact v.elim
  comul_assoc := by
    change copy X ≫ tensor (𝟙 X) (copy X) =
      copy X ≫ tensor (copy X) (𝟙 X) ≫ (assocIso X X X).hom
    simp only [copy, assocIso, portIso, ← wire_id, wire_tensor, wire_comp]
    apply wire_congr
    funext v
    rcases v with a | (b | c) <;> rfl

instance commComonoid (X : Interface S) : IsCommComonObj X where
  comul_comm := by
    change copy X ≫ (swapIso X X).hom = copy X
    simp only [copy, swapIso, portIso, wire_comp]
    apply wire_congr
    funext v; cases v <;> rfl

@[simp] theorem tensorHom_eq {X Y X' Y' : Interface S} (f : X ⟶ Y) (g : X' ⟶ Y') :
    f ⊗ₘ g = tensor f g := rfl

@[simp] theorem whiskerLeft_eq (X : Interface S) {Y Z : Interface S} (f : Y ⟶ Z) :
    X ◁ f = tensor (𝟙 X) f := rfl

@[simp] theorem whiskerRight_eq {X Y : Interface S} (f : X ⟶ Y) (Z : Interface S) :
    f ▷ Z = tensor f (𝟙 Z) := rfl

@[simp] theorem associator_eq (X Y Z : Interface S) : α_ X Y Z = assocIso X Y Z := rfl
@[simp] theorem leftUnitor_eq (X : Interface S) : λ_ X = leftIso X := rfl
@[simp] theorem rightUnitor_eq (X : Interface S) : ρ_ X = rightIso X := rfl
@[simp] theorem braiding_eq (X Y : Interface S) : β_ X Y = swapIso X Y := rfl

instance copyDiscard : CopyDiscardCategory (Interface S) where
  copy_tensor := by
    intro X Y
    change copy (X.sum Y) = tensor (copy X) (copy Y) ≫ tensorμ X X Y Y
    simp only [tensorμ, whiskerLeft_eq, whiskerRight_eq, associator_eq, braiding_eq]
    simp only [copy, assocIso, swapIso, portIso, ← wire_id, wire_tensor, wire_comp]
    apply wire_congr
    funext v
    rcases v with (x | y) | (x | y) <;> rfl
  discard_tensor := by
    intro X Y
    change discard (X.sum Y) =
      tensor (discard X) (discard Y) ≫ (leftIso (Interface.empty S)).hom
    simp only [discard, leftIso, portIso, wire_tensor, wire_comp]
    apply wire_congr
    funext v; exact v.elim
  copy_unit := by
    change copy (Interface.empty S) = (leftIso (Interface.empty S)).inv
    simp only [copy, leftIso, portIso]
    apply wire_congr
    funext v; rcases v with v | v <;> exact v.elim
  discard_unit := by
    change discard (Interface.empty S) = 𝟙 (Interface.empty S)
    rw [discard, ← wire_id]
    apply wire_congr
    funext v; exact v.elim

end OpenNet
