import CategoricalBayesianNetworksProofs.CopyDiscard

/-!
# General legged networks and representation equivalence

This independent presentation has an arbitrary finite variable set, a finite
mechanism set, an injective target function, an injective input leg whose image
is precisely the complement of the targets, and an unrestricted output leg.
The input/target partition gives a bijection with inputs plus generators.
Transport along that bijection gives the canonical syntax without choosing a
topological order or deleting hidden components.

The theorems prove both round trips up to incidence-preserving isomorphism and
show that isomorphic legged networks yield equal canonical arrows. This is a
mathematical representation theorem, not a checked Julia ACSet parser.
-/

namespace OpenNet
variable {S : Signature} {X Y : Interface S}

structure Legged (X Y : Interface S) where
  Var : Type
  varsFinite : Fintype Var
  Gen : Type
  gensFinite : Fintype Gen
  type : Var → S.Ty
  label : Gen → S.Label
  target : Gen → Var
  target_injective : Function.Injective target
  parents : Gen → List Var
  input : X.Port → Var
  input_injective : Function.Injective input
  output : Y.Port → Var
  disjoint : ∀ x g, input x ≠ target g
  cover : ∀ v, (∃ x, input x = v) ∨ (∃ g, target g = v)
  input_typed : ∀ x, type (input x) = X.type x
  target_typed : ∀ g, type (target g) = S.result (label g)
  parents_typed : ∀ g, (parents g).map type = S.inputs (label g)
  output_typed : ∀ y, type (output y) = Y.type y
  acyclic : ∃ rank : Var → ℕ, ∀ g v, v ∈ parents g → rank v < rank (target g)

attribute [instance] Legged.varsFinite Legged.gensFinite

namespace Legged

theorem partition_bijective (N : Legged X Y) :
    Function.Bijective (Sum.elim N.input N.target) := by
  constructor
  · intro a b h
    cases a with
    | inl x =>
      cases b with
      | inl y => exact congrArg Sum.inl (N.input_injective h)
      | inr g => exact (N.disjoint x g h).elim
    | inr g =>
      cases b with
      | inl x => exact (N.disjoint x g h.symm).elim
      | inr h' => exact congrArg Sum.inr (N.target_injective h)
  · intro v
    rcases N.cover v with ⟨x, hx⟩ | ⟨g, hg⟩
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr g, hg⟩

noncomputable def varsEquiv (N : Legged X Y) : X.Port ⊕ N.Gen ≃ N.Var :=
  Equiv.ofBijective (Sum.elim N.input N.target) N.partition_bijective

@[simp] theorem varsEquiv_input (N : Legged X Y) (x : X.Port) :
    N.varsEquiv (Sum.inl x) = N.input x := rfl

@[simp] theorem varsEquiv_target (N : Legged X Y) (g : N.Gen) :
    N.varsEquiv (Sum.inr g) = N.target g := rfl

theorem varsEquiv_typed (N : Legged X Y) (v : X.Port ⊕ N.Gen) :
    N.type (N.varsEquiv v) = Sum.elim X.type (S.result ∘ N.label) v := by
  cases v with
  | inl x => exact N.input_typed x
  | inr g => exact N.target_typed g

theorem decode_typed (N : Legged X Y) (v : N.Var) :
    Sum.elim X.type (S.result ∘ N.label) (N.varsEquiv.symm v) = N.type v := by
  rw [← N.varsEquiv_typed, Equiv.apply_symm_apply]

noncomputable def normalise (N : Legged X Y) : Net X Y where
  Gen := N.Gen
  finite := inferInstance
  label := N.label
  parents g := (N.parents g).map N.varsEquiv.symm
  output := N.varsEquiv.symm ∘ N.output
  parents_typed := by
    intro g
    rw [List.map_map]
    exact (congrArg (fun k => (N.parents g).map k) (funext N.decode_typed)).trans
      (N.parents_typed g)
  output_typed y := (N.decode_typed _).trans (N.output_typed y)
  acyclic := by
    obtain ⟨r, hr⟩ := N.acyclic
    refine ⟨r ∘ N.target, ?_⟩
    intro g h hh
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hh
    have ve : v = N.target h := by
      have := congrArg N.varsEquiv he
      simpa using this
    subst v
    exact hr g (N.target h) hv

structure Iso (N M : Legged X Y) where
  vars : N.Var ≃ M.Var
  gens : N.Gen ≃ M.Gen
  type : ∀ v, M.type (vars v) = N.type v
  label : ∀ g, M.label (gens g) = N.label g
  input : ∀ x, M.input x = vars (N.input x)
  target : ∀ g, M.target (gens g) = vars (N.target g)
  parents : ∀ g, M.parents (gens g) = (N.parents g).map vars
  output : ∀ y, M.output y = vars (N.output y)

def Iso.refl (N : Legged X Y) : Iso N N where
  vars := Equiv.refl _
  gens := Equiv.refl _
  type _ := rfl
  label _ := rfl
  input _ := rfl
  target _ := rfl
  parents _ := by simp
  output _ := rfl

def Iso.trans {N M K : Legged X Y} (a : Iso N M) (b : Iso M K) : Iso N K where
  vars := a.vars.trans b.vars
  gens := a.gens.trans b.gens
  type v := (b.type _).trans (a.type v)
  label g := (b.label _).trans (a.label g)
  input x := by rw [b.input, a.input]; rfl
  target g := by
    change K.target (b.gens (a.gens g)) = _
    rw [b.target, a.target]
    rfl
  parents g := by
    change K.parents (b.gens (a.gens g)) = _
    rw [b.parents, a.parents, List.map_map]
    rfl
  output y := by rw [b.output, a.output]; rfl

def Iso.symm {N M : Legged X Y} (a : Iso N M) : Iso M N where
  vars := a.vars.symm
  gens := a.gens.symm
  type v := by simpa using (a.type (a.vars.symm v)).symm
  label g := by simpa using (a.label (a.gens.symm g)).symm
  input x := by rw [a.input, Equiv.symm_apply_apply]
  target g := by
    have h := congrArg a.vars.symm (a.target (a.gens.symm g))
    simpa using h.symm
  parents g := by
    have h := congrArg (List.map a.vars.symm) (a.parents (a.gens.symm g))
    simpa using h.symm
  output y := by rw [a.output, Equiv.symm_apply_apply]

theorem Iso.decode {N M : Legged X Y} (a : Iso N M) (v : N.Var) :
    M.varsEquiv.symm (a.vars v) = Sum.map id a.gens (N.varsEquiv.symm v) := by
  have step (w : X.Port ⊕ N.Gen) :
      M.varsEquiv (Sum.map id a.gens w) = a.vars (N.varsEquiv w) := by
    cases w with
    | inl x => exact a.input x
    | inr g => exact a.target g
  apply M.varsEquiv.injective
  rw [Equiv.apply_symm_apply, step, Equiv.apply_symm_apply]

noncomputable def Iso.normalise {N M : Legged X Y} (a : Iso N M) :
    Net.Iso N.normalise M.normalise where
  gen := a.gens
  label := a.label
  parents g := by
    change (M.parents (a.gens g)).map _ = ((N.parents g).map _).map _
    rw [a.parents, List.map_map, List.map_map]
    exact congrArg (fun k => (N.parents g).map k) (funext a.decode)
  output y := by
    change M.varsEquiv.symm (M.output y) = _
    rw [a.output]
    exact a.decode _

theorem normalise_respects_iso {N M : Legged X Y} (a : Iso N M) :
    ofNet N.normalise = ofNet M.normalise :=
  Quotient.sound ⟨a.normalise⟩

end Legged

namespace Net

def toLegged (f : Net X Y) : Legged X Y where
  Var := f.Var
  varsFinite := inferInstance
  Gen := f.Gen
  gensFinite := inferInstance
  type := f.varType
  label := f.label
  target := Sum.inr
  target_injective := Sum.inr_injective
  parents := f.parents
  input := Sum.inl
  input_injective := Sum.inl_injective
  output := f.output
  disjoint := fun _ _ => Sum.inl_ne_inr
  cover v := by
    cases v with
    | inl x => exact Or.inl ⟨x, rfl⟩
    | inr g => exact Or.inr ⟨g, rfl⟩
  input_typed _ := rfl
  target_typed _ := rfl
  parents_typed := f.parents_typed
  output_typed := f.output_typed
  acyclic := by
    obtain ⟨r, hr⟩ := f.acyclic
    refine ⟨Sum.elim (fun _ => 0) (fun g => r g + 1), ?_⟩
    intro g v hv
    cases v with
    | inl x => exact Nat.zero_lt_succ _
    | inr h => exact Nat.add_lt_add_right (hr g h hv) 1

theorem toLegged_decode (f : Net X Y) (v : f.Var) :
    f.toLegged.varsEquiv.symm v = v := by
  apply f.toLegged.varsEquiv.injective
  rw [Equiv.apply_symm_apply]
  cases v <;> rfl

noncomputable def normalise_roundtrip (f : Net X Y) : Iso f.toLegged.normalise f where
  gen := Equiv.refl _
  label _ := rfl
  parents g := by
    change f.parents g = ((f.parents g).map _).map _
    simp only [List.map_map]
    have h : Sum.map id (Equiv.refl f.Gen) ∘ f.toLegged.varsEquiv.symm = id := by
      funext v
      rw [Function.comp_apply, toLegged_decode]
      cases v <;> rfl
    exact ((congrArg (fun k => (f.parents g).map k) h).trans (List.map_id _)).symm
  output y := by
    change f.output y = Sum.map id (Equiv.refl f.Gen) (f.toLegged.varsEquiv.symm (f.output y))
    rw [toLegged_decode]
    cases f.output y <;> rfl

def Iso.toLegged {f g : Net X Y} (a : Iso f g) : Legged.Iso f.toLegged g.toLegged where
  vars := Equiv.sumCongr (Equiv.refl X.Port) a.gen
  gens := a.gen
  type v := by
    cases v with
    | inl x => rfl
    | inr b => exact congrArg S.result (a.label b)
  label := a.label
  input _ := rfl
  target _ := rfl
  parents := a.parents
  output := a.output

end Net

namespace Legged

noncomputable def representation_iso (N : Legged X Y) : Iso N.normalise.toLegged N where
  vars := N.varsEquiv
  gens := Equiv.refl _
  type := N.varsEquiv_typed
  label _ := rfl
  input _ := rfl
  target _ := rfl
  parents g := by
    change N.parents g = ((N.parents g).map N.varsEquiv.symm).map N.varsEquiv
    simp
  output y := by
    change N.output y = N.varsEquiv (N.varsEquiv.symm (N.output y))
    simp

/-- Canonical-arrow equality is exactly general legged structural isomorphism. -/
theorem representation_faithful (N M : Legged X Y) :
    ofNet N.normalise = ofNet M.normalise ↔ Nonempty (Iso N M) := by
  constructor
  · intro h
    obtain ⟨a⟩ := (ofNet_eq_iff _ _).mp h
    exact ⟨N.representation_iso.symm.trans (a.toLegged.trans M.representation_iso)⟩
  · rintro ⟨a⟩
    exact normalise_respects_iso a

end Legged
end OpenNet
