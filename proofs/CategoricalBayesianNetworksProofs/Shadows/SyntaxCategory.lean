import CategoricalBayesianNetworksProofs.Category

/-!
# SA-Pass shadow module: the syntax really is a category

Claim `cbn.category`. The candidate is the content of the `CategoryTheory.Category (Interface S)`
instance, restated abstractly for `compose` and `ofNet (Net.identity _)` so that neither checker
can be discharged by citing the instance.
-/

namespace CategoricalBayesianNetworksProofs.Shadows.SyntaxCategory

open OpenNet

/-- The category laws for the structural-isomorphism quotient, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (S : Signature) (X Y Z W : Interface S)
      (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W),
    compose (ofNet (Net.identity X)) f = f ∧ compose f (ofNet (Net.identity Y)) = f ∧
      compose (compose f g) h = compose f (compose g h)

/-- "an actual syntax category": the empty network is a two-sided identity for substitution. -/
abbrev Shadow1 : Prop :=
  ∀ (S : Signature) (X Y : Interface S) (f : Hom X Y),
    compose (ofNet (Net.identity X)) f = f ∧ compose f (ofNet (Net.identity Y)) = f

/-- and substitution is associative, up to structural isomorphism and nothing coarser. -/
abbrev Shadow2 : Prop :=
  ∀ (S : Signature) (X Y Z W : Interface S) (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W),
    compose (compose f g) h = compose f (compose g h)

theorem forward1 : Candidate → Shadow1 := by
  intro hc S X Y f
  obtain ⟨h1, h2, _⟩ := hc S X Y Y Y f (ofNet (Net.identity Y)) (ofNet (Net.identity Y))
  exact ⟨h1, h2⟩

theorem forward2 : Candidate → Shadow2 := by
  intro hc S X Y Z W f g h
  exact (hc S X Y Z W f g h).2.2

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2 S X Y Z W f g h
  exact ⟨(h1 S X Y f).1, (h1 S X Y f).2, h2 S X Y Z W f g h⟩

end CategoricalBayesianNetworksProofs.Shadows.SyntaxCategory
