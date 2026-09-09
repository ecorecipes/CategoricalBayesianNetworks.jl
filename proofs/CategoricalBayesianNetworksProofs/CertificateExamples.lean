import CategoricalBayesianNetworksProofs.RawCertificate
import CategoricalBayesianNetworksProofs.SemanticExamples

/-!
# Concrete certificate acceptance and rejection

The accepted example has unordered two-state records, unordered repeated parent
slots, nontrivial space/kernel references, pass-through, copied output rows, and
a hidden generator. The finite checker accepts it without any manually supplied
validity proof. Duplicate input positions, bad rank certificates, and a changed
output-foot space reference are rejected.
-/

namespace OpenNet.RawCertificate

def boolAttrs (name ref : String) : VariableAttrs :=
  ⟨name, .named ref, ["false", "true"]⟩

abbrev certificate : Network where
  variableCount := 3
  variableData v :=
    if v = 0 then ⟨"x", .named "bool:x", [⟨"true", 2⟩, ⟨"false", 1⟩], 0⟩
    else if v = 1 then ⟨"visible", .named "bool:visible", [⟨"false", 1⟩, ⟨"true", 2⟩], 1⟩
    else ⟨"hidden", .named "bool:hidden", [⟨"true", 2⟩, ⟨"false", 1⟩], 0⟩
  mechanisms := [
    ⟨"parity", .named "kernel:parity", 1, [⟨0, 2⟩, ⟨0, 1⟩]⟩,
    ⟨"prior", .named "kernel:prior", 2, []⟩]
  inputs := [⟨0, boolAttrs "x" "bool:x"⟩]
  outputs := [⟨0, boolAttrs "x" "bool:x"⟩,
    ⟨1, boolAttrs "visible" "bool:visible"⟩,
    ⟨1, boolAttrs "visible" "bool:visible"⟩]

theorem certificate_accepted : certificate.check = true := by decide

theorem ordered_repeated_parents : certificate.parents 0 = [0, 0] := by decide

theorem ordered_named_states :
    (certificate.attrs 0).states = ["false", "true"] := by decide

theorem references_survive :
    ((certificate.normalize certificate_accepted).label (0 : Fin 2)).kernelRef =
      .named "kernel:parity" := rfl

def badPositions : Network :=
  { certificate with mechanisms := [
      ⟨"parity", .named "kernel:parity", 1, [⟨0, 1⟩, ⟨0, 1⟩]⟩,
      ⟨"prior", .named "kernel:prior", 2, []⟩] }

def badRank : Network :=
  { certificate with variableData := fun v =>
      { certificate.variableData v with rank := 0 } }

def badReference : Network :=
  { certificate with outputs := [⟨1, boolAttrs "visible" "wrong-space-ref"⟩] }

theorem duplicate_position_rejected : badPositions.check = false := by decide
theorem bad_rank_rejected : badRank.check = false := by decide
theorem bad_reference_rejected : badReference.check = false := by decide

end OpenNet.RawCertificate
