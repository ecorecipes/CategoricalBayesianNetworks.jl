import CategoricalBayesianNetworksProofs.Legged
import CategoricalBayesianNetworksProofs.InterpretationFunctor

/-!
# Ordered attributed finite-record certificates

This is a concrete data interface, not a theorem about a Julia parser.
Variable and mechanism identities are finite indices. Each owner carries its
finite rows with the original positive position attributes. Normalization sorts
the actual rows by position; validation checks precisely positions 1 through
the row count, nonempty distinct named states, both attributed feet, the
input/target partition, and a supplied acyclic rank certificate.

References retain their tagged payloads. Boundary maps remain arbitrary on the
output side. Repeated input-variable occurrences are retained as separate rows
at distinct positions. The checker is an executable finite decision procedure;
acceptance is proved to construct a valid general-legged network and hence an
arrow of the accepted structural category.
-/

namespace OpenNet.RawCertificate

inductive Reference where
  | noRef
  | named (id : String)
  | pointMass (state : String)
  | policy (decision : String)
  deriving DecidableEq, Repr

structure StateRow where
  name : String
  position : ℕ
  deriving DecidableEq, Repr

structure InputRow (n : ℕ) where
  varId : Fin n
  position : ℕ
  deriving DecidableEq, Repr

structure VariableAttrs where
  name : String
  spaceRef : Reference
  states : List String
  deriving DecidableEq, Repr

structure VariableData where
  name : String
  spaceRef : Reference
  stateRows : List StateRow
  rank : ℕ
  deriving DecidableEq, Repr

structure MechanismData (n : ℕ) where
  name : String
  kernelRef : Reference
  target : Fin n
  inputRows : List (InputRow n)
  deriving DecidableEq, Repr

structure BoundaryRow (n : ℕ) where
  varId : Fin n
  attrs : VariableAttrs
  deriving DecidableEq, Repr

structure LabelAttrs where
  name : String
  kernelRef : Reference
  inputs : List VariableAttrs
  result : VariableAttrs
  deriving DecidableEq, Repr

abbrev signature : Signature :=
  ⟨VariableAttrs, LabelAttrs, LabelAttrs.inputs, LabelAttrs.result⟩

def orderRows {A : Type} (position : A → ℕ) (rows : List A) : List A :=
  rows.insertionSort (fun a b => position a ≤ position b)

theorem orderRows_perm {A : Type} (position : A → ℕ) (rows : List A) :
    (orderRows position rows).Perm rows := List.perm_insertionSort _ _

structure Network where
  variableCount : ℕ
  variableData : Fin variableCount → VariableData
  mechanisms : List (MechanismData variableCount)
  inputs : List (BoundaryRow variableCount)
  outputs : List (BoundaryRow variableCount)

namespace Network

def states (N : Network) (v : Fin N.variableCount) : List StateRow :=
  orderRows StateRow.position (N.variableData v).stateRows

def attrs (N : Network) (v : Fin N.variableCount) : VariableAttrs :=
  ⟨(N.variableData v).name, (N.variableData v).spaceRef, (N.states v).map StateRow.name⟩

def mechanism (N : Network) (g : Fin N.mechanisms.length) : MechanismData N.variableCount :=
  N.mechanisms[g]

def rows (N : Network) (g : Fin N.mechanisms.length) : List (InputRow N.variableCount) :=
  orderRows InputRow.position (N.mechanism g).inputRows

def parents (N : Network) (g : Fin N.mechanisms.length) : List (Fin N.variableCount) :=
  (N.rows g).map InputRow.varId

def label (N : Network) (g : Fin N.mechanisms.length) : LabelAttrs :=
  ⟨(N.mechanism g).name, (N.mechanism g).kernelRef,
    (N.parents g).map N.attrs, N.attrs (N.mechanism g).target⟩

def dom (N : Network) : Interface signature :=
  ⟨Fin N.inputs.length, inferInstance, fun i => N.inputs[i].attrs⟩

def cod (N : Network) : Interface signature :=
  ⟨Fin N.outputs.length, inferInstance, fun i => N.outputs[i].attrs⟩

def input (N : Network) (i : Fin N.inputs.length) : Fin N.variableCount :=
  N.inputs[i].varId

def output (N : Network) (i : Fin N.outputs.length) : Fin N.variableCount :=
  N.outputs[i].varId

def target (N : Network) (g : Fin N.mechanisms.length) : Fin N.variableCount :=
  (N.mechanism g).target

def Valid (N : Network) : Prop :=
  (∀ v, (N.states v).map StateRow.position = List.range' 1 (N.states v).length ∧
    ((N.states v).map StateRow.name).Nodup ∧ N.states v ≠ []) ∧
  (∀ g, (N.rows g).map InputRow.position = List.range' 1 (N.rows g).length) ∧
  Function.Injective N.target ∧
  Function.Injective N.input ∧
  (∀ i g, N.input i ≠ N.target g) ∧
  (∀ v, (∃ i, N.input i = v) ∨ ∃ g, N.target g = v) ∧
  (∀ i, N.attrs (N.input i) = N.inputs[i].attrs) ∧
  (∀ i, N.attrs (N.output i) = N.outputs[i].attrs) ∧
  (∀ g v, v ∈ N.parents g → (N.variableData v).rank < (N.variableData (N.target g)).rank)

instance validDecidable (N : Network) : Decidable N.Valid := by
  unfold Valid Function.Injective
  infer_instance

def check (N : Network) : Bool := decide N.Valid

theorem check_iff (N : Network) : N.check = true ↔ N.Valid :=
  decide_eq_true_iff

theorem check_sound (N : Network) (h : N.check = true) : N.Valid := N.check_iff.mp h

def toLegged (N : Network) (h : N.Valid) : Legged N.dom N.cod where
  Var := Fin N.variableCount
  varsFinite := inferInstance
  Gen := Fin N.mechanisms.length
  gensFinite := inferInstance
  type := N.attrs
  label := N.label
  target := N.target
  target_injective := h.2.2.1
  parents := N.parents
  input := N.input
  input_injective := h.2.2.2.1
  output := N.output
  disjoint := h.2.2.2.2.1
  cover := h.2.2.2.2.2.1
  input_typed := h.2.2.2.2.2.2.1
  target_typed _ := rfl
  parents_typed _ := rfl
  output_typed := h.2.2.2.2.2.2.2.1
  acyclic := ⟨fun v => (N.variableData v).rank, h.2.2.2.2.2.2.2.2⟩

noncomputable def normalize (N : Network) (h : N.check = true) : Net N.dom N.cod :=
  (N.toLegged (N.check_sound h)).normalise

theorem state_positions (N : Network) (h : N.check = true) (v : Fin N.variableCount) :
    (N.states v).map StateRow.position = List.range' 1 (N.states v).length :=
  (N.check_sound h).1 v |>.1

theorem input_positions (N : Network) (h : N.check = true) (g : Fin N.mechanisms.length) :
    (N.rows g).map InputRow.position = List.range' 1 (N.rows g).length :=
  (N.check_sound h).2.1 g

theorem row_occurrences (N : Network) (g : Fin N.mechanisms.length) :
    (N.parents g).length = (N.mechanism g).inputRows.length := by
  unfold parents rows
  rw [List.length_map]
  exact (orderRows_perm _ _).length_eq

theorem variable_reference (N : Network) (v : Fin N.variableCount) :
    (N.attrs v).spaceRef = (N.variableData v).spaceRef := rfl

theorem mechanism_reference (N : Network) (h : N.check = true)
    (g : Fin N.mechanisms.length) :
    ((N.normalize h).label g).kernelRef = (N.mechanism g).kernelRef := rfl

theorem mechanism_name (N : Network) (h : N.check = true)
    (g : Fin N.mechanisms.length) :
    ((N.normalize h).label g).name = (N.mechanism g).name := rfl

noncomputable def normalized_representation (N : Network) (h : N.check = true) :
    Legged.Iso (N.normalize h).toLegged (N.toLegged (N.check_sound h)) :=
  (N.toLegged (N.check_sound h)).representation_iso

theorem normalized_acyclic (N : Network) (h : N.check = true) (a : (N.normalize h).Gen) :
    ¬ Relation.TransGen (fun u v => Sum.inr u ∈ (N.normalize h).parents v) a a :=
  (N.normalize h).no_directed_cycle a

/-- Normalized certificate semantics is invariant under full attributed renumbering. -/
theorem certificate_semantics_iso (N M : Network)
    (hN : N.check = true) (hM : M.check = true)
    (hdom : N.dom = M.dom) (hcod : N.cod = M.cod)
    (a : Net.Iso (hdom ▸ hcod ▸ N.normalize hN) (M.normalize hM))
    (I : Interpretation signature) :
    I.kernel (hdom ▸ hcod ▸ N.normalize hN) = I.kernel (M.normalize hM) :=
  I.kernel_iso a

end Network
end OpenNet.RawCertificate
