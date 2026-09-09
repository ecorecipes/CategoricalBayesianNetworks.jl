import CategoricalBayesianNetworksProofs.InterpretationFunctor

/-!
# Exact output-first finite-table enumeration

The reference table enumerates *all* apex assignments, multiplies the ordered
local factors, and accumulates into the boundary output/input tuple selected
by the two legs. It therefore mirrors an exact-arithmetic Cartesian-index
enumeration, including repeated output axes and passed-through inputs.
The theorem below equates this independently stated enumeration with the
internal-assignment kernel used by the functor.
-/

noncomputable section
namespace OpenNet.Interpretation
variable {S : Signature} (I : Interpretation S) {X Y : Interface S}

def apexWeight (f : Net X Y) (z : I.Assignment f.varType) : ℝ :=
  ∏ a, I.weight (f.label a) ((f.parents a).map z.value) (z (Sum.inr a))

def apexInput (f : Net X Y) (z : I.Assignment f.varType) : I.Boundary X :=
  Assignment.reindex I z Sum.inl (fun _ => rfl)

def apexOutput (f : Net X Y) (z : I.Assignment f.varType) : I.Boundary Y :=
  Assignment.reindex I z f.output f.output_typed

/-- Output axes first, input axes last, as in `FiniteKernel.table`. -/
def enumeratedTable (f : Net X Y) (y : I.Boundary Y) (x : I.Boundary X) : ℝ := by
  classical
  exact ∑ z : I.Assignment f.varType,
    if I.apexInput f z = x ∧ I.apexOutput f z = y then I.apexWeight f z else 0

theorem enumerated_table_correct (f : Net X Y) (y : I.Boundary Y) (x : I.Boundary X) :
    I.enumeratedTable f y x = I.kernel f x y := by
  classical
  unfold enumeratedTable
  erw [← (Assignment.sumEquiv I X.type (S.result ∘ f.label)).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ a : I.Boundary X, ∑ b : I.Internal f,
    if a = x ∧ I.read f a b = y then I.joint f a b else 0) = _
  rw [Finset.sum_eq_single x]
  · simp only [true_and, kernel]
    apply Finset.sum_congr rfl
    intro z _
    simp only [eq_comm]
  · intro a _ ha
    simp [ha]
  · simp

theorem copied_output_zero (f : Net X Y) (x : I.Boundary X) (y : I.Boundary Y)
    (a b : Y.Port) (same : f.output a = f.output b) (different : y a ≠ y b) :
    I.kernel f x y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro z _
  apply if_neg
  intro h
  apply different
  rw [h]
  exact congrArg (I.valuation f x z) same

theorem pass_through_zero (f : Net X Y) (x : I.Boundary X) (y : I.Boundary Y)
    (a : Y.Port) (b : X.Port) (through : f.output a = Sum.inl b)
    (different : y a ≠ x b) : I.kernel f x y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro z _
  apply if_neg
  intro h
  apply different
  rw [h]
  change I.valuation f x z (f.output a) = x b
  rw [through]
  rfl

theorem enumerated_table_normalized (f : Net X Y) (x : I.Boundary X) :
    ∑ y, I.enumeratedTable f y x = 1 := by
  simp only [I.enumerated_table_correct]
  exact I.kernel_normalized f x

end OpenNet.Interpretation
