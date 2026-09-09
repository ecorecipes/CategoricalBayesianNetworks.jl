import CategoricalBayesianNetworksProofs.Legged

/-!
# Substitution really is gluing

The composite's variable set is the pushout of the arbitrary output leg of the
first network and the injective input leg of the second. The universal property
is proved for every target type, including non-injective output legs. Generators
are disjointly unioned; their labels, targets and ordered parent occurrences are
transported by the pushout maps. No generators are identified, and no hidden
component is deleted.
-/

namespace OpenNet.Net
variable {S : Signature} {X Y Z : Interface S}

theorem gluing_commutes (f : Net X Y) (g : Net Y Z) (y : Y.Port) :
    left f g (f.output y) = right f g (Sum.inl y) := rfl

def descend {T : Type} (f : Net X Y) (g : Net Y Z)
    (u : f.Var → T) (v : g.Var → T) : (f.comp g).Var → T :=
  Sum.elim (u ∘ Sum.inl) (Sum.elim (u ∘ Sum.inr) (v ∘ Sum.inr))

theorem descend_left {T : Type} (f : Net X Y) (g : Net Y Z)
    (u : f.Var → T) (v : g.Var → T) (x : f.Var) :
    descend f g u v (left f g x) = u x := by cases x <;> rfl

theorem descend_right {T : Type} (f : Net X Y) (g : Net Y Z)
    (u : f.Var → T) (v : g.Var → T)
    (compatible : ∀ y, u (f.output y) = v (Sum.inl y)) (x : g.Var) :
    descend f g u v (right f g x) = v x := by
  cases x with
  | inl y => exact (descend_left f g u v _).trans (compatible y)
  | inr b => rfl

/-- The complete variable pushout universal property, with uniqueness. -/
theorem variable_pushout {T : Type} (f : Net X Y) (g : Net Y Z)
    (u : f.Var → T) (v : g.Var → T)
    (compatible : ∀ y, u (f.output y) = v (Sum.inl y)) :
    ∃! m : (f.comp g).Var → T,
      (∀ x, m (left f g x) = u x) ∧ (∀ y, m (right f g y) = v y) := by
  refine ⟨descend f g u v, ⟨descend_left f g u v, descend_right f g u v compatible⟩, ?_⟩
  intro m hm
  funext x
  rcases x with x | (a | b)
  · exact hm.1 (Sum.inl x)
  · exact hm.1 (Sum.inr a)
  · exact hm.2 (Sum.inr b)

/-- Every ordered input occurrence is transported, including repeated parents. -/
theorem gluing_parents (f : Net X Y) (g : Net Y Z) :
    (∀ a, (f.comp g).parents (Sum.inl a) = (f.parents a).map (left f g)) ∧
    (∀ b, (f.comp g).parents (Sum.inr b) = (g.parents b).map (right f g)) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem gluing_targets (f : Net X Y) (g : Net Y Z) :
    (∀ a, (f.comp g).toLegged.target (Sum.inl a) = left f g (f.toLegged.target a)) ∧
    (∀ b, (f.comp g).toLegged.target (Sum.inr b) = right f g (g.toLegged.target b)) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem gluing_labels (f : Net X Y) (g : Net Y Z) :
    (∀ a, (f.comp g).label (Sum.inl a) = f.label a) ∧
    (∀ b, (f.comp g).label (Sum.inr b) = g.label b) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem gluing_target_injective (f : Net X Y) (g : Net Y Z) :
    Function.Injective (f.comp g).toLegged.target :=
  (f.comp g).toLegged.target_injective

/-- An attributed ordered-incidence map of apices, without boundary constraints. -/
@[ext] structure ApexMap {A B : Interface S} (f : Net X Y) (h : Net A B) where
  vars : f.Var → h.Var
  gens : f.Gen → h.Gen
  typed : ∀ v, h.varType (vars v) = f.varType v
  labels : ∀ a, h.label (gens a) = f.label a
  targets : ∀ a, vars (Sum.inr a) = Sum.inr (gens a)
  parents : ∀ a, (f.parents a).map vars = h.parents (gens a)

def descendApex {A B : Interface S} (f : Net X Y) (g : Net Y Z) (h : Net A B)
    (u : ApexMap f h) (v : ApexMap g h)
    (compatible : ∀ y, u.vars (f.output y) = v.vars (Sum.inl y)) :
    ApexMap (f.comp g) h where
  vars := descend f g u.vars v.vars
  gens := Sum.elim u.gens v.gens
  typed x := by
    rcases x with x | (a | b)
    · exact u.typed (Sum.inl x)
    · exact u.typed (Sum.inr a)
    · exact v.typed (Sum.inr b)
  labels a := by
    cases a with
    | inl a => exact u.labels a
    | inr b => exact v.labels b
  targets a := by
    cases a with
    | inl a => exact u.targets a
    | inr b => exact v.targets b
  parents a := by
    cases a with
    | inl a =>
      change ((f.parents a).map (left f g)).map _ = _
      rw [List.map_map]
      exact (congrArg (fun k => (f.parents a).map k)
        (funext (descend_left f g u.vars v.vars))).trans (u.parents a)
    | inr b =>
      change ((g.parents b).map (right f g)).map _ = _
      rw [List.map_map]
      exact (congrArg (fun k => (g.parents b).map k)
        (funext (descend_right f g u.vars v.vars compatible))).trans (v.parents b)

/-- The pushout also preserves all labels, types, targets and ordered input slots. -/
theorem apex_pushout {A B : Interface S} (f : Net X Y) (g : Net Y Z) (h : Net A B)
    (u : ApexMap f h) (v : ApexMap g h)
    (compatible : ∀ y, u.vars (f.output y) = v.vars (Sum.inl y)) :
    ∃! m : ApexMap (f.comp g) h,
      (∀ x, m.vars (left f g x) = u.vars x) ∧
      (∀ y, m.vars (right f g y) = v.vars y) ∧
      (∀ a, m.gens (Sum.inl a) = u.gens a) ∧
      (∀ b, m.gens (Sum.inr b) = v.gens b) := by
  refine ⟨descendApex f g h u v compatible,
    ⟨descend_left f g u.vars v.vars, descend_right f g u.vars v.vars compatible,
      fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro m hm
  apply ApexMap.ext
  · funext x
    rcases x with x | (a | b)
    · exact hm.1 (Sum.inl x)
    · exact hm.1 (Sum.inr a)
    · exact hm.2.1 (Sum.inr b)
  · funext a
    cases a with
    | inl a => exact hm.2.2.1 a
    | inr b => exact hm.2.2.2 b

end OpenNet.Net
