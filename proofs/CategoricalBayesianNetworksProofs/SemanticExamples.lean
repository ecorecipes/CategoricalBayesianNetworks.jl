import CategoricalBayesianNetworksProofs.InterpretationFunctor
import CategoricalBayesianNetworksProofs.Examples
import Mathlib.Tactic.NormNum

/-!
# Two-state numerical examples with copying and hidden randomness

The visible two-input mechanism computes parity of its ordered input
occurrences. Reading the same Boolean input twice therefore returns false.
The independent hidden mechanism is genuinely stochastic: false has mass 1/3
and true has mass 2/3. Its mass sums to one but its syntactic generator remains.

The evaluated three-output kernel passes the input through, emits the visible
false value twice, assigns zero to inconsistent copied outputs, and is exactly
normalized. All entries below are exact real arithmetic, not floating point.

![The concrete numerical interpretation. The retained hidden generator has
nontrivial local probabilities, but contributes total mass one after
summation. Inconsistent copies or a changed pass-through value have mass
zero.](diagrams/stochastic.svg)
-/

noncomputable section
namespace OpenNet.SemanticExamples
open Interpretation
open CategoryTheory
open scoped BigOperators

def parity (p : List (Sigma (fun _ : Unit => Bool))) : Bool :=
  p.foldl (fun b v => Bool.xor b v.2) false

def booleanWeight (n : ℕ) (p : List (Sigma (fun _ : Unit => Bool)))
    (s : Sigma (fun _ : Unit => Bool)) : ℝ :=
  if n = 0 then (if s.2 then 2 / 3 else 1 / 3)
  else if s.2 = parity p then 1 else 0

abbrev booleanModel : Interpretation Examples.signature where
  states _ := Bool
  finite _ := inferInstance
  weight := booleanWeight
  nonneg := by
    intro n p s
    unfold booleanWeight
    split_ifs <;> norm_num
  normalized := by
    intro n p _
    change (∑ s : Bool, booleanWeight n p ⟨(), s⟩) = 1
    by_cases hn : n = 0
    · norm_num [booleanWeight, hn, Fintype.sum_bool]
    · cases hp : parity p <;> norm_num [booleanWeight, hn, hp, Fintype.sum_bool]

def input (x : Bool) : booleanModel.Boundary Examples.one :=
  Assignment.ofPi booleanModel (fun _ => x)

def output (a b c : Bool) : booleanModel.Boundary Examples.three :=
  Assignment.ofPi booleanModel (fun i => if i = 0 then a else if i = 1 then b else c)

def internal (a b : Bool) : booleanModel.Internal Examples.mixed :=
  Assignment.ofPi booleanModel (fun i => if i then b else a)

def internalEquiv : booleanModel.Internal Examples.mixed ≃ Bool × Bool where
  toFun z := ((z false).2, (z true).2)
  invFun z := internal z.1 z.2
  left_inv z := by
    apply Assignment.ext
    funext b
    cases b <;> apply Sigma.ext (Subsingleton.elim _ _) <;> rfl
  right_inv z := by cases z; rfl

theorem output_injective (a b c a' b' c' : Bool) :
    output a b c = output a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact congrArg (fun z => (z (0 : Fin 3)).2) h
    · exact congrArg (fun z => (z (1 : Fin 3)).2) h
    · exact congrArg (fun z => (z (2 : Fin 3)).2) h
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem mixed_read (x a b : Bool) :
    booleanModel.read Examples.mixed (input x) (internal a b) = output x a a := by
  apply Assignment.ext
  funext i
  fin_cases i <;> rfl

theorem mixed_joint (x a b : Bool) :
    booleanModel.joint Examples.mixed (input x) (internal a b) =
      (if a = false then 1 else 0) * (if b then (2 : ℝ) / 3 else 1 / 3) := by
  unfold Interpretation.joint
  erw [Fintype.prod_bool]
  cases x <;> cases a <;> cases b <;>
    norm_num [Interpretation.parents,
      Interpretation.valuation, Assignment.join, Assignment.ofPi, input, internal,
      booleanWeight, parity]

theorem mixed_kernel (x a b c : Bool) :
    booleanModel.kernel Examples.mixed (input x) (output a b c) =
      if a = x ∧ b = false ∧ c = false then 1 else 0 := by
  classical
  unfold Interpretation.kernel
  erw [← internalEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  change (if output a b c = booleanModel.read _ _ (internal true true) then
      booleanModel.joint _ _ (internal true true) else 0) +
    (if output a b c = booleanModel.read _ _ (internal true false) then
      booleanModel.joint _ _ (internal true false) else 0) +
    ((if output a b c = booleanModel.read _ _ (internal false true) then
      booleanModel.joint _ _ (internal false true) else 0) +
     (if output a b c = booleanModel.read _ _ (internal false false) then
      booleanModel.joint _ _ (internal false false) else 0)) = _
  simp only [mixed_read, mixed_joint, output_injective]
  cases x <;> cases a <;> cases b <;> cases c <;> norm_num

theorem copied_inconsistency_zero :
    booleanModel.kernel Examples.mixed (input true) (output true false true) = 0 := by
  rw [mixed_kernel]
  simp

theorem pass_through_zero :
    booleanModel.kernel Examples.mixed (input true) (output false false false) = 0 := by
  rw [mixed_kernel]
  simp

theorem visible_mass_one :
    booleanModel.kernel Examples.mixed (input true) (output true false false) = 1 := by
  rw [mixed_kernel]
  simp

theorem hidden_random_mass :
    booleanModel.joint Examples.mixed (input true) (internal false false) = 1 / 3 ∧
    booleanModel.joint Examples.mixed (input true) (internal false true) = 2 / 3 := by
  simp [mixed_joint]

theorem hidden_semantic_erasure :
    booleanModel.functor.map (ofNet Examples.mixed ≫ OpenNet.discard Examples.three) =
      booleanModel.functor.map (OpenNet.discard Examples.one) :=
  booleanModel.semantic_discard _

theorem hidden_scalar_mass
    (x y : booleanModel.Boundary (Interface.empty Examples.signature)) :
    booleanModel.kernel Examples.hiddenScalar x y = 1 := by
  letI : Unique (booleanModel.Boundary (Interface.empty Examples.signature)) := by
    change Unique (booleanModel.Assignment (Empty.elim : Empty → Unit))
    infer_instance
  have h := booleanModel.kernel_normalized Examples.hiddenScalar x
  have hy : y = default := Subsingleton.elim _ _
  simpa only [Finset.univ_unique, Finset.sum_singleton, hy] using h

end OpenNet.SemanticExamples
