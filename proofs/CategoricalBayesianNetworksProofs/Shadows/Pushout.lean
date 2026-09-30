import CategoricalBayesianNetworksProofs.Pushout

/-!
# SA-Pass shadow module: the composite is the pushout along the shared interface

Claim `cbn.pushout`, from `variable_pushout` (with `gluing_commutes` for the square).
-/

namespace CategoricalBayesianNetworksProofs.Shadows.Pushout

open OpenNet OpenNet.Net

/-- `variable_pushout`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (S : Signature) (X Y Z : Interface S) (f : Net X Y) (g : Net Y Z) (T : Type)
      (u : f.Var → T) (v : g.Var → T), (∀ y, u (f.output y) = v (Sum.inl y)) →
    ∃! m : (f.comp g).Var → T,
      (∀ x, m (left f g x) = u x) ∧ (∀ y, m (right f g y) = v y)

/-- "the pushout": every pair of maps agreeing on the shared interface factors through the
composite's variables. No injectivity of the output leg is assumed. -/
abbrev Shadow1 : Prop :=
  ∀ (S : Signature) (X Y Z : Interface S) (f : Net X Y) (g : Net Y Z) (T : Type)
      (u : f.Var → T) (v : g.Var → T), (∀ y, u (f.output y) = v (Sum.inl y)) →
    ∃ m : (f.comp g).Var → T,
      (∀ x, m (left f g x) = u x) ∧ (∀ y, m (right f g y) = v y)

/-- and the factorisation is unique, which is what makes the composite *the* pushout rather
than merely a cocone: no variables are duplicated and none are left over. -/
abbrev Shadow2 : Prop :=
  ∀ (S : Signature) (X Y Z : Interface S) (f : Net X Y) (g : Net Y Z) (T : Type)
      (m m' : (f.comp g).Var → T),
    (∀ x, m (left f g x) = m' (left f g x)) → (∀ y, m (right f g y) = m' (right f g y)) →
      m = m'

theorem forward1 : Candidate → Shadow1 := by
  intro h S X Y Z f g T u v hc
  obtain ⟨m, hm, _⟩ := h S X Y Z f g T u v hc
  exact ⟨m, hm⟩

theorem forward2 : Candidate → Shadow2 := by
  intro h S X Y Z f g T m m' hl hr
  obtain ⟨n, _, huniq⟩ :=
    h S X Y Z f g T (fun x => m (left f g x)) (fun y => m (right f g y))
      (fun y => congrArg m (gluing_commutes f g y))
  rw [huniq m ⟨fun _ => rfl, fun _ => rfl⟩,
    huniq m' ⟨fun x => (hl x).symm, fun y => (hr y).symm⟩]

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2 S X Y Z f g T u v hc
  obtain ⟨m, hml, hmr⟩ := h1 S X Y Z f g T u v hc
  refine ⟨m, ⟨hml, hmr⟩, ?_⟩
  intro m' hm'
  exact h2 S X Y Z f g T m' m (fun x => (hm'.1 x).trans (hml x).symm)
    (fun y => (hm'.2 y).trans (hmr y).symm)

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated, so a restatement that
drifts from the proved theorem stops compiling. -/
theorem anchor : Candidate := fun _ _ _ _ f g _ u v h =>
  OpenNet.Net.variable_pushout f g u v h

end CategoricalBayesianNetworksProofs.Shadows.Pushout
