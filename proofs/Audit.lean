import CategoricalBayesianNetworksProofs
import Mathlib.Util.AssertNoSorry

assert_no_sorry OpenNet.category
assert_no_sorry OpenNet.monoidal
assert_no_sorry OpenNet.symmetric
assert_no_sorry OpenNet.copyDiscard
assert_no_sorry OpenNet.Net.compose_acyclic
assert_no_sorry OpenNet.Net.tensor_acyclic
assert_no_sorry OpenNet.Net.apex_pushout
assert_no_sorry OpenNet.Legged.representation_faithful
assert_no_sorry OpenNet.Examples.discard_not_natural
assert_no_sorry OpenNet.Interpretation.kernel_iso
assert_no_sorry OpenNet.Interpretation.kernel_comp
assert_no_sorry OpenNet.Interpretation.kernel_tensor
assert_no_sorry OpenNet.Interpretation.generated_nonempty
assert_no_sorry OpenNet.Interpretation.kernel_stochastic
assert_no_sorry OpenNet.Interpretation.functor
assert_no_sorry OpenNet.Interpretation.monoidalFunctor
assert_no_sorry OpenNet.Interpretation.braidedFunctor
assert_no_sorry OpenNet.Interpretation.semantic_discard
assert_no_sorry OpenNet.Interpretation.enumerated_table_correct
assert_no_sorry OpenNet.RawCertificate.Network.check_sound
assert_no_sorry OpenNet.RawCertificate.LocalTables.interpretation
assert_no_sorry OpenNet.CertificateSyntax.parse
assert_no_sorry OpenNet.RawCertificate.JSON.read_sound
assert_no_sorry OpenNet.RawCertificate.JSON.read_preserves_decoded
assert_no_sorry OpenNet.RawCertificate.JSON.reference_roundtrip
assert_no_sorry OpenNet.RawCertificate.JSON.index_value

#print axioms OpenNet.Net.no_directed_cycle
#print axioms OpenNet.Net.compose_acyclic
#print axioms OpenNet.Net.tensor_acyclic
#print axioms OpenNet.Net.Iso.refl
#print axioms OpenNet.Net.Iso.symm
#print axioms OpenNet.Net.Iso.trans
#print axioms OpenNet.Net.Iso.comp
#print axioms OpenNet.Net.Iso.tensor
#print axioms OpenNet.Net.id_comp_iso
#print axioms OpenNet.Net.comp_id_iso
#print axioms OpenNet.Net.assoc_iso
#print axioms OpenNet.Net.interchange_iso
#print axioms OpenNet.ofNet_eq_iff
#print axioms OpenNet.category
#print axioms OpenNet.tensor_comp
#print axioms OpenNet.wire_comp
#print axioms OpenNet.wire_tensor
#print axioms OpenNet.Net.slide
#print axioms OpenNet.wire_slide
#print axioms OpenNet.assoc_natural
#print axioms OpenNet.left_natural
#print axioms OpenNet.right_natural
#print axioms OpenNet.swap_natural
#print axioms OpenNet.monoidal
#print axioms OpenNet.symmetric
#print axioms OpenNet.comonoid
#print axioms OpenNet.commComonoid
#print axioms OpenNet.copyDiscard
#print axioms OpenNet.Legged.partition_bijective
#print axioms OpenNet.Legged.normalise
#print axioms OpenNet.Legged.Iso.normalise
#print axioms OpenNet.Legged.normalise_respects_iso
#print axioms OpenNet.Net.toLegged
#print axioms OpenNet.Net.normalise_roundtrip
#print axioms OpenNet.Legged.representation_iso
#print axioms OpenNet.Legged.representation_faithful
#print axioms OpenNet.Net.gluing_commutes
#print axioms OpenNet.Net.variable_pushout
#print axioms OpenNet.Net.gluing_parents
#print axioms OpenNet.Net.gluing_targets
#print axioms OpenNet.Net.gluing_labels
#print axioms OpenNet.Net.gluing_target_injective
#print axioms OpenNet.Net.descendApex
#print axioms OpenNet.Net.apex_pushout
#print axioms OpenNet.generatorCount
#print axioms OpenNet.generatorCount_comp
#print axioms OpenNet.generatorCount_tensor
#print axioms OpenNet.Examples.copied_outputs
#print axioms OpenNet.Examples.pass_through
#print axioms OpenNet.Examples.hidden_component
#print axioms OpenNet.Examples.repeated_slots
#print axioms OpenNet.Examples.copied_substitution
#print axioms OpenNet.Examples.hidden_survives
#print axioms OpenNet.Examples.mixed_associativity
#print axioms OpenNet.Examples.mixed_identity
#print axioms OpenNet.Examples.mixed_tensor_interchange
#print axioms OpenNet.Examples.discard_not_natural
#print axioms OpenNet.Examples.hidden_scalar_not_identity
#print axioms OpenNet.Examples.hidden_scalar_associativity

#print axioms OpenNet.Interpretation.Assignment.piEquiv
#print axioms OpenNet.Interpretation.Assignment.sumEquiv
#print axioms OpenNet.Interpretation.Assignment.renameEquiv
#print axioms OpenNet.Interpretation.parents_typed
#print axioms OpenNet.Interpretation.joint_nonneg
#print axioms OpenNet.Interpretation.kernel_nonneg
#print axioms OpenNet.Interpretation.joint_iso
#print axioms OpenNet.Interpretation.read_iso
#print axioms OpenNet.Interpretation.kernel_iso
#print axioms OpenNet.Interpretation.joint_comp
#print axioms OpenNet.Interpretation.read_comp
#print axioms OpenNet.Interpretation.kernel_comp
#print axioms OpenNet.Interpretation.generated_nonempty
#print axioms OpenNet.Interpretation.internal_local
#print axioms OpenNet.Interpretation.internal_normalized
#print axioms OpenNet.Interpretation.internalOrder
#print axioms OpenNet.Interpretation.joint_normalized
#print axioms OpenNet.Interpretation.kernel_normalized
#print axioms OpenNet.Interpretation.kernel_stochastic
#print axioms OpenNet.Interpretation.kernel_wire
#print axioms OpenNet.Interpretation.joint_tensor
#print axioms OpenNet.Interpretation.read_tensor
#print axioms OpenNet.Interpretation.kernel_tensor
#print axioms OpenNet.Interpretation.functor
#print axioms OpenNet.Interpretation.map_ofNet
#print axioms OpenNet.Interpretation.map_wire
#print axioms OpenNet.Interpretation.tensor_natural
#print axioms OpenNet.Interpretation.monoidalCore
#print axioms OpenNet.Interpretation.monoidalFunctor
#print axioms OpenNet.Interpretation.braidedFunctor
#print axioms OpenNet.Interpretation.map_copy
#print axioms OpenNet.Interpretation.map_discard
#print axioms OpenNet.Interpretation.semantic_discard
#print axioms OpenNet.Interpretation.enumerated_table_correct
#print axioms OpenNet.Interpretation.enumerated_table_normalized
#print axioms OpenNet.Interpretation.copied_output_zero
#print axioms OpenNet.Interpretation.pass_through_zero
#print axioms OpenNet.RawCertificate.orderRows_perm
#print axioms OpenNet.RawCertificate.Network.check_iff
#print axioms OpenNet.RawCertificate.Network.check_sound
#print axioms OpenNet.RawCertificate.Network.toLegged
#print axioms OpenNet.RawCertificate.Network.state_positions
#print axioms OpenNet.RawCertificate.Network.input_positions
#print axioms OpenNet.RawCertificate.Network.row_occurrences
#print axioms OpenNet.RawCertificate.Network.variable_reference
#print axioms OpenNet.RawCertificate.Network.mechanism_reference
#print axioms OpenNet.RawCertificate.Network.mechanism_name
#print axioms OpenNet.RawCertificate.Network.normalized_representation
#print axioms OpenNet.RawCertificate.Network.normalized_acyclic
#print axioms OpenNet.RawCertificate.Network.certificate_semantics_iso
#print axioms OpenNet.RawCertificate.LocalTables.interpretation
#print axioms OpenNet.RawCertificate.LocalTables.typed_entry
#print axioms OpenNet.RawCertificate.LocalTables.checked_table_normalized
#print axioms OpenNet.RawCertificate.LocalTables.tables_nonvacuous
#print axioms OpenNet.RawCertificate.dimension_checked
#print axioms OpenNet.RawCertificate.certificate_accepted
#print axioms OpenNet.RawCertificate.ordered_repeated_parents
#print axioms OpenNet.RawCertificate.ordered_named_states
#print axioms OpenNet.RawCertificate.references_survive
#print axioms OpenNet.RawCertificate.duplicate_position_rejected
#print axioms OpenNet.RawCertificate.bad_rank_rejected
#print axioms OpenNet.RawCertificate.bad_reference_rejected
#print axioms OpenNet.SemanticExamples.booleanModel
#print axioms OpenNet.SemanticExamples.mixed_read
#print axioms OpenNet.SemanticExamples.mixed_joint
#print axioms OpenNet.SemanticExamples.mixed_kernel
#print axioms OpenNet.SemanticExamples.copied_inconsistency_zero
#print axioms OpenNet.SemanticExamples.pass_through_zero
#print axioms OpenNet.SemanticExamples.visible_mass_one
#print axioms OpenNet.SemanticExamples.hidden_random_mass
#print axioms OpenNet.SemanticExamples.hidden_semantic_erasure
#print axioms OpenNet.SemanticExamples.hidden_scalar_mass

#print axioms OpenNet.CertificateSyntax.parse
#print axioms OpenNet.RawCertificate.JSON.network
#print axioms OpenNet.RawCertificate.JSON.read
#print axioms OpenNet.RawCertificate.JSON.natural_roundtrip
#print axioms OpenNet.RawCertificate.JSON.index_roundtrip
#print axioms OpenNet.RawCertificate.JSON.index_value
#print axioms OpenNet.RawCertificate.JSON.validate_preserves
#print axioms OpenNet.RawCertificate.JSON.read_preserves_decoded
#print axioms OpenNet.RawCertificate.JSON.read_sound
#print axioms OpenNet.RawCertificate.JSON.checkedNet
#print axioms OpenNet.RawCertificate.JSON.reference_roundtrip
#print axioms OpenNet.RawCertificate.JSON.stateRow_roundtrip
