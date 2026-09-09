import CategoricalBayesianNetworksProofs.Pushout
import Mathlib.Tactic.FinCases

/-!
# Nonvacuous examples and the boundary of Markov syntax

The `mixed` network has one input, a two-slot mechanism that reads that input
twice, and an independent hidden zero-input mechanism. Its three output
occurrences are the input itself and two copies of the visible mechanism's
output. Composition with `consumer` substitutes the two copied outputs into
two ordered slots without merging mechanisms or dropping the hidden component.

![The concrete mixed network. Slot numbers record two occurrences of the same
input, outputs 1 and 2 copy one variable, output 0 passes the input through, and
the independent nullary mechanism has no output-foot occurrence.](diagrams/mixed.svg)

Generator count descends to structural-isomorphism classes. It proves that
discarding all outputs retains internal mechanisms: these syntax arrows do
not satisfy naturality of discard. This distinguishes the constructed
copy-discard category from its prospective stochastic semantics.
-/

namespace OpenNet
open CategoryTheory
variable {S : Signature} {X Y Z X' Y' : Interface S}

def generatorCount (f : X ⟶ Y) : ℕ :=
  Quotient.liftOn f (fun n => Fintype.card n.Gen)
    (fun _ _ ⟨a⟩ => Fintype.card_congr a.gen)

@[simp] theorem generatorCount_ofNet (f : Net X Y) :
    generatorCount (ofNet f) = Fintype.card f.Gen := rfl

theorem generatorCount_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    generatorCount (f ≫ g) = generatorCount f + generatorCount g := by
  induction f, g using Quotient.inductionOn₂ with | _ f g =>
    exact Fintype.card_sum

theorem generatorCount_tensor (f : X ⟶ Y) (g : X' ⟶ Y') :
    generatorCount (tensor f g) = generatorCount f + generatorCount g := by
  induction f, g using Quotient.inductionOn₂ with | _ f g =>
    exact Fintype.card_sum

@[simp] theorem generatorCount_wire (p : Y.Port → X.Port) (hp) :
    generatorCount (wire p hp) = 0 := rfl

namespace Examples

abbrev signature : Signature where
  Ty := Unit
  Label := ℕ
  inputs n := List.replicate n ()
  result _ := ()

abbrev one : Interface signature := ⟨Unit, inferInstance, fun _ => ()⟩
abbrev three : Interface signature := ⟨Fin 3, inferInstance, fun _ => ()⟩

abbrev mixed : Net one three where
  Gen := Bool
  finite := inferInstance
  label b := if b then 0 else 2
  parents b := if b then [] else [Sum.inl (), Sum.inl ()]
  output y := if y = 0 then Sum.inl () else Sum.inr false
  parents_typed := by intro b; cases b <;> rfl
  output_typed y := by
    change Sum.elim (fun _ => ()) (fun _ => ()) (if y = 0 then _ else _) = ()
    split <;> rfl
  acyclic := by
    refine ⟨fun _ => 0, ?_⟩
    intro g h hh
    cases g <;> simp at hh

abbrev consumer : Net three one where
  Gen := Unit
  finite := inferInstance
  label _ := 3
  parents _ := [Sum.inl 1, Sum.inl 2, Sum.inl 0]
  output _ := Sum.inr ()
  parents_typed _ := rfl
  output_typed _ := rfl
  acyclic := by
    refine ⟨fun _ => 0, ?_⟩
    intro g h hh
    simp at hh

theorem copied_outputs : ¬ Function.Injective mixed.output := by
  intro h
  have e := h (show mixed.output 1 = mixed.output 2 from rfl)
  exact (by decide : (1 : Fin 3) ≠ 2) e

theorem pass_through : mixed.output 0 = Sum.inl () := rfl

theorem hidden_component : ∀ y, mixed.output y ≠ Sum.inr true := by
  intro y
  fin_cases y <;> decide

theorem repeated_slots :
    mixed.parents false = [Sum.inl (), Sum.inl ()] := rfl

theorem copied_substitution :
    (mixed.comp consumer).parents (Sum.inr ()) =
      [Sum.inr (Sum.inl false), Sum.inr (Sum.inl false), Sum.inl ()] := rfl

theorem hidden_survives :
    generatorCount (ofNet mixed ≫ ofNet consumer) = 3 := rfl

theorem mixed_associativity :
    (ofNet mixed ≫ ofNet consumer) ≫ copy one =
      ofNet mixed ≫ (ofNet consumer ≫ copy one) := Category.assoc _ _ _

theorem mixed_identity :
    𝟙 one ≫ ofNet mixed = ofNet mixed ∧ ofNet mixed ≫ 𝟙 three = ofNet mixed :=
  ⟨Category.id_comp _, Category.comp_id _⟩

theorem mixed_tensor_interchange :
    compose (tensor (ofNet mixed) (ofNet mixed)) (tensor (ofNet consumer) (ofNet consumer)) =
      tensor (compose (ofNet mixed) (ofNet consumer)) (compose (ofNet mixed) (ofNet consumer)) :=
  tensor_comp _ _ _ _

theorem discard_not_natural :
    ofNet mixed ≫ discard three ≠ discard one := by
  intro h
  have hc := congrArg generatorCount h
  rw [generatorCount_comp] at hc
  change 2 + 0 = 0 at hc
  exact (by decide : ¬ (2 + 0 = 0)) hc

abbrev hiddenScalar : Net (Interface.empty signature) (Interface.empty signature) where
  Gen := Unit
  finite := inferInstance
  label _ := 0
  parents _ := []
  output := Empty.elim
  parents_typed _ := rfl
  output_typed y := y.elim
  acyclic := ⟨fun _ => 0, fun _ _ h => by cases h⟩

theorem hidden_scalar_not_identity :
    ofNet hiddenScalar ≠ 𝟙 (Interface.empty signature) := by
  intro h
  have hc := congrArg generatorCount h
  change 1 = 0 at hc
  contradiction

theorem hidden_scalar_associativity :
    compose (compose (ofNet hiddenScalar) (ofNet hiddenScalar)) (ofNet hiddenScalar) =
      compose (ofNet hiddenScalar) (compose (ofNet hiddenScalar) (ofNet hiddenScalar)) :=
  Quotient.sound ⟨Net.assoc_iso hiddenScalar hiddenScalar hiddenScalar⟩

end Examples
end OpenNet
