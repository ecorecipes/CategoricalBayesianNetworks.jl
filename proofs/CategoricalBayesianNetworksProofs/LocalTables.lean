import CategoricalBayesianNetworksProofs.RawCertificate
import CategoricalBayesianNetworksProofs.ApexEnumeration

/-!
# Ordered local CPT tables for checked attributed records

Each input occurrence has its own coordinate in a finite product. A local table
takes the parent tuple first and the child state last, exactly the user-facing
CPT convention. Its interpretation is proved to be the typed local kernel
used by the general stochastic functor.

The universal raw-attribute signature includes malformed empty state lists.
For those unused types only, `dimension` is one rather than zero. Acceptance
requires nonempty state rows, and `dimension_checked` proves the dimension is
exactly the declared state count on every checked variable. This explicit total
extension makes normalized table assignments to the universal signature
nonvacuous without changing any accepted network's state space.
-/

namespace OpenNet.RawCertificate

def dimension (t : VariableAttrs) : ℕ := max 1 t.states.length

def StateTuple : List VariableAttrs → Type
  | [] => Unit
  | t :: ts => Fin (dimension t) × StateTuple ts

@[reducible] def tupleFinite : (ts : List VariableAttrs) → Fintype (StateTuple ts)
  | [] => (inferInstance : Fintype Unit)
  | t :: ts => by
    letI := tupleFinite ts
    exact (inferInstance : Fintype (Fin (dimension t) × StateTuple ts))

instance (ts : List VariableAttrs) : Fintype (StateTuple ts) := tupleFinite ts

abbrev StateValue := Sigma (fun t : VariableAttrs => Fin (dimension t))

def valuesTuple : (p : List StateValue) → StateTuple (p.map Sigma.fst)
  | [] => ()
  | v :: vs => (v.2, valuesTuple vs)

def typedTuple (l : LabelAttrs) (p : List StateValue) (hp : p.map Sigma.fst = l.inputs) :
    StateTuple l.inputs :=
  cast (congrArg StateTuple hp) (valuesTuple p)

structure LocalTables where
  entry : (l : LabelAttrs) → StateTuple l.inputs → Fin (dimension l.result) → ℝ
  nonneg : ∀ l p s, 0 ≤ entry l p s
  normalized : ∀ l p, ∑ s, entry l p s = 1

namespace LocalTables

def zeroState (t : VariableAttrs) : Fin (dimension t) :=
  ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 t.states.length)⟩

/-- A normalized table family exists on the entire raw signature. -/
def point : LocalTables where
  entry l _ s := if s = zeroState l.result then 1 else 0
  nonneg := by intro l p s; split <;> simp
  normalized := by intro l p; simp

def weight (T : LocalTables) (l : LabelAttrs) (p : List StateValue) (s : StateValue) : ℝ :=
  if hp : p.map Sigma.fst = l.inputs then
    if hs : s.1 = l.result then
      T.entry l (typedTuple l p hp) (cast (congrArg (fun t => Fin (dimension t)) hs) s.2)
    else 0
  else 0

def interpretation (T : LocalTables) : Interpretation signature where
  states t := Fin (dimension t)
  finite _ := inferInstance
  weight := T.weight
  nonneg := by
    intro l p s
    unfold weight
    split_ifs
    · exact T.nonneg _ _ _
    · exact le_refl _
    · exact le_refl _
  normalized := by
    intro l p hp
    simpa only [weight, dif_pos hp, dif_pos rfl, cast_eq] using T.normalized l (typedTuple l p hp)

theorem typed_entry (T : LocalTables) (l : LabelAttrs) (p : List StateValue)
    (hp : p.map Sigma.fst = l.inputs) (s : Fin (dimension l.result)) :
    T.interpretation.weight l p ⟨l.result, s⟩ = T.entry l (typedTuple l p hp) s := by
  simp [interpretation, weight, hp]

theorem checked_table_normalized (T : LocalTables) (N : Network) (h : N.check = true)
    (x : T.interpretation.Boundary N.dom) :
    ∑ y, T.interpretation.enumeratedTable (N.normalize h) y x = 1 :=
  T.interpretation.enumerated_table_normalized _ _

theorem tables_nonvacuous : Nonempty LocalTables := ⟨point⟩

end LocalTables

theorem dimension_checked (N : Network) (h : N.check = true) (v : Fin N.variableCount) :
    dimension (N.attrs v) = (N.states v).length := by
  have hn := ((N.check_sound h).1 v).2.2
  have hpos : 0 < (N.states v).length := List.length_pos_iff.mpr hn
  change max 1 ((N.states v).map StateRow.name).length = _
  rw [List.length_map, max_eq_right hpos]

end OpenNet.RawCertificate
