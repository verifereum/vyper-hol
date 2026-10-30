# ABI encoder contract index

This index flags every definition, inductive relation and theorem statement added
by the encoder consolidation relative to `45266883`. Existing declarations retain
their original statements and attributes. Links lead to the defining source;
the index does not replace those contracts.

## Definitions and inductive relations

### abiEncoderEffectProbe

- [effect_probe_start_def](abiEncoderEffectProbeScript.sml#L21)
- [effect_probe_end_def](abiEncoderEffectProbeScript.sml#L27)

### abiEncoderExactWriteProbe

- [encoder_exact_writes_def](abiEncoderExactWriteProbeScript.sml#L8)

### abiEncoderExitPhi

- [abi_encoder_exit_nonempty_def](abiEncoderExitPhiScript.sml#L7)
- [abi_encoder_empty_preserving_def](abiEncoderExitPhiScript.sml#L12)

### abiEncoderExtendSim

- [abi_encoder_extend_sim_def](abiEncoderExtendSimScript.sml#L7)

### abiEncoderLabelAliasProbe

- [alias_base_def](abiEncoderLabelAliasProbeScript.sml#L8)
- [alias_compile_def](abiEncoderLabelAliasProbeScript.sml#L14)
- [alias_old_def](abiEncoderLabelAliasProbeScript.sml#L19)
- [alias_start_def](abiEncoderLabelAliasProbeScript.sml#L23)
- [alias_end_def](abiEncoderLabelAliasProbeScript.sml#L27)
- [alias_function_def](abiEncoderLabelAliasProbeScript.sml#L31)
- [alias_entry_block_def](abiEncoderLabelAliasProbeScript.sml#L62)

### abiEncoderMemberPhaseRaw

- [abi_encoder_member_phase_raw_def](abiEncoderMemberPhaseRawScript.sml#L11)

### abiEncoderMemberSourceContract

- [abi_encoder_member_core_pre_def](abiEncoderMemberSourceContractScript.sml#L9)
- [abi_encoder_member_core_post_def](abiEncoderMemberSourceContractScript.sml#L21)
- [abi_encoder_member_cursor_saved_def](abiEncoderMemberSourceContractScript.sml#L84)
- [abi_encoder_member_dynamic_pre_def](abiEncoderMemberSourceContractScript.sml#L96)
- [abi_encoder_member_dynamic_post_def](abiEncoderMemberSourceContractScript.sml#L102)

### abiEncoderMemberSpineCompat

- [abi_encoder_spine_shared_pre_def](abiEncoderMemberSpineCompatScript.sml#L19)
- [abi_encoder_spine_shared_post_def](abiEncoderMemberSpineCompatScript.sml#L32)

### abiEncoderMemberSpine

- [abi_encoder_spine_call_def](abiEncoderMemberSpineScript.sml#L8)
- [abi_encoder_spine_child_def](abiEncoderMemberSpineScript.sml#L14)
- [abi_encoder_member_spine_def](abiEncoderMemberSpineScript.sml#L30)
- [abi_encoder_spine_core_code_def](abiEncoderMemberSpineScript.sml#L93)
- [abi_encoder_spine_cursor_input_def](abiEncoderMemberSpineScript.sml#L129)
- [abi_encoder_spine_child_input_def](abiEncoderMemberSpineScript.sml#L240)
- [abi_encoder_spine_child_output_def](abiEncoderMemberSpineScript.sml#L266)
- [abi_encoder_spine_code_def](abiEncoderMemberSpineScript.sml#L301)
- [abi_encoder_spine_cons_layout_def](abiEncoderMemberSpineScript.sml#L312)

### abiEncoderObserverCode

- [abi_word_observer_def](abiEncoderObserverCodeScript.sml#L10)
- [abi_word_region_def](abiEncoderObserverCodeScript.sml#L19)
- [abi_header_observer_def](abiEncoderObserverCodeScript.sml#L115)
- [abi_header_region_def](abiEncoderObserverCodeScript.sml#L126)

### abiEncoderObserver

- [stop_view_def](abiEncoderObserverScript.sml#L7)
- [abi_observer_step_def](abiEncoderObserverScript.sml#L52)
- [local_prefix](abiEncoderObserverScript.sml#L68) (inductive relation)
- [prefix_code_agrees_def](abiEncoderObserverScript.sml#L112)
- [observer_closed_def](abiEncoderObserverScript.sml#L158)
- [observer_region_closed_def](abiEncoderObserverScript.sml#L303)
- [region_code_agrees_def](abiEncoderObserverScript.sml#L310)
- [observer_region_safe_def](abiEncoderObserverScript.sml#L484)

### abiEncoderOpenInput

- [abi_encoder_structural_valid](abiEncoderOpenInputScript.sml#L8) (inductive relation)
- [abi_encoder_open_input](abiEncoderOpenInputScript.sml#L23) (inductive relation)
- [abi_encoder_layout_valid_def](abiEncoderOpenInputScript.sml#L144)

### abiEncoderRegisteredEffect

- [abi_encoder_registered_effect_def](abiEncoderRegisteredEffectScript.sml#L7)

### abiEncoderSharedArrayIndex

- [abi_encoder_shared_array_index_def](abiEncoderSharedArrayIndexScript.sml#L10)

### abiEncoderSharedContract

- [abi_encoder_shared_input_def](abiEncoderSharedContractScript.sml#L10)
- [abi_encoder_shared_endpoint_def](abiEncoderSharedContractScript.sml#L24)
- [abi_encoder_shared_def](abiEncoderSharedContractScript.sml#L38)

### abiEncoderSharedMemberContract

- [abi_encoder_shared_member_dynamic_pre_def](abiEncoderSharedMemberContractScript.sml#L23)
- [abi_encoder_shared_member_dynamic_post_def](abiEncoderSharedMemberContractScript.sml#L29)
- [abi_encoder_shared_members_child_pre_def](abiEncoderSharedMemberContractScript.sml#L98)
- [abi_encoder_shared_members_child_post_def](abiEncoderSharedMemberContractScript.sml#L104)

### abiEncoderSharedMembersIndex

- [abi_encoder_shared_members_inv_def](abiEncoderSharedMembersIndexScript.sml#L10)
- [abi_encoder_shared_members_index_def](abiEncoderSharedMembersIndexScript.sml#L28)

### abiEncoderSharedMembersInput

- [abi_encoder_shared_members_pre_def](abiEncoderSharedMembersInputScript.sml#L9)

### abiEncoderSharedMembersInterpret

- [abi_encoder_shared_members_entry_def](abiEncoderSharedMembersInterpretScript.sml#L10)

### abiEncoderSourceAggregate

- [source_rep_def](abiEncoderSourceAggregateScript.sml#L52)
- [source_reps_def](abiEncoderSourceAggregateScript.sml#L64)

### abiEncoderSourceMembersIndex

- [abi_encoder_source_members_index_def](abiEncoderSourceMembersIndexScript.sml#L8)

### abiEncoderSourceMembersInterpret

- [abi_encoder_source_members_child_pre_def](abiEncoderSourceMembersInterpretScript.sml#L8)
- [abi_encoder_source_members_child_post_def](abiEncoderSourceMembersInterpretScript.sml#L14)
- [abi_encoder_source_members_entry_def](abiEncoderSourceMembersInterpretScript.sml#L47)

### abiEncoderVarTransport

- [abi_encoder_ignored_inputs_def](abiEncoderVarTransportScript.sml#L42)

### abiScratchMemberContract

- [abi_scratch_member_core_pre_def](abiScratchMemberContractScript.sml#L9)
- [abi_scratch_member_core_post_def](abiScratchMemberContractScript.sml#L22)
- [abi_scratch_member_cursor_saved_def](abiScratchMemberContractScript.sml#L84)
- [abi_scratch_member_dynamic_pre_def](abiScratchMemberContractScript.sml#L96)
- [abi_scratch_member_dynamic_post_def](abiScratchMemberContractScript.sml#L104)

### abiScratchMembersIndex

- [abi_scratch_members_index_def](abiScratchMembersIndexScript.sml#L8)

### abiScratchMembersInterpret

- [abi_scratch_members_child_pre_def](abiScratchMembersInterpretScript.sml#L8)
- [abi_scratch_members_child_post_def](abiScratchMembersInterpretScript.sml#L14)
- [abi_scratch_members_entry_def](abiScratchMembersInterpretScript.sml#L47)

## Theorem statements

These are new helper contracts and compatibility corollaries. Existing APIs
such as the two recursive encoder closures and the external-return theorems
are preserved; their replacement proof bodies are not restatements.

### abiDecoderVarSequence

- [abi_decoder_pure1_inputs](abiDecoderVarSequenceScript.sml#L24)
- [abi_decoder_pure2_inputs](abiDecoderVarSequenceScript.sml#L31)
- [abi_decoder_read1_inputs](abiDecoderVarSequenceScript.sml#L38)
- [abi_decoder_write2_inputs](abiDecoderVarSequenceScript.sml#L45)
- [abi_decoder_inline_inputs](abiDecoderVarSequenceScript.sml#L52)

### abiEncoderAggregateProbe

- [encoder_array_requires_positive_slots](abiEncoderAggregateProbeScript.sml#L9)
- [encoder_empty_tuple_array_rejected](abiEncoderAggregateProbeScript.sml#L17)
- [encoder_tuple_abi_type_probe](abiEncoderAggregateProbeScript.sml#L23)
- [encoder_zero_tuple_evaluate_members](abiEncoderAggregateProbeScript.sml#L30)
- [encoder_zero_tuple_slot_members](abiEncoderAggregateProbeScript.sml#L38)
- [encoder_zero_tuple_value_members](abiEncoderAggregateProbeScript.sml#L45)
- [encoder_zero_tuple_convert_members](abiEncoderAggregateProbeScript.sml#L52)
- [encoder_zero_tuple_abi_members](abiEncoderAggregateProbeScript.sml#L60)
- [encoder_zero_tuple_source_diagnostic](abiEncoderAggregateProbeScript.sml#L68)
- [encoder_zero_tuple_abi_cardinality_diagnostic](abiEncoderAggregateProbeScript.sml#L84)
- [encoder_zero_tuple_memory_members](abiEncoderAggregateProbeScript.sml#L93)
- [encoder_zero_tuple_memory_diagnostic](abiEncoderAggregateProbeScript.sml#L100)
- [encoder_zero_tuple_input_unavailable](abiEncoderAggregateProbeScript.sml#L107)
- [encoder_zero_tuple_static_members](abiEncoderAggregateProbeScript.sml#L116)
- [encoder_zero_tuple_plan](abiEncoderAggregateProbeScript.sml#L122)
- [encoder_zero_tuple_pre](abiEncoderAggregateProbeScript.sml#L134)
- [encoder_zero_tuple_typed_members](abiEncoderAggregateProbeScript.sml#L145)
- [encoder_zero_tuple_flat_encoding](abiEncoderAggregateProbeScript.sml#L151)
- [encoder_zero_tuple_encoding](abiEncoderAggregateProbeScript.sml#L158)
- [encoder_zero_tuple_giant_diagnostic](abiEncoderAggregateProbeScript.sml#L168)
- [encoder_zero_copy_representative](abiEncoderAggregateProbeScript.sml#L180)
- [encoder_zero_copy_encoding_correspondence](abiEncoderAggregateProbeScript.sml#L187)
- [encoder_dynamic_tuple_evaluate_members](abiEncoderAggregateProbeScript.sml#L195)
- [encoder_dynamic_tuple_value_members](abiEncoderAggregateProbeScript.sml#L206)
- [encoder_dynamic_tuple_convert_members](abiEncoderAggregateProbeScript.sml#L214)
- [encoder_dynamic_tuple_abi_members](abiEncoderAggregateProbeScript.sml#L223)
- [encoder_dynamic_tuple_slot_members](abiEncoderAggregateProbeScript.sml#L231)
- [encoder_dynamic_tuple_source_diagnostic](abiEncoderAggregateProbeScript.sml#L238)
- [encoder_dynamic_tuple_abi_cardinality_diagnostic](abiEncoderAggregateProbeScript.sml#L256)
- [encoder_dynamic_tuple_zero_prefix_span](abiEncoderAggregateProbeScript.sml#L266)
- [encoder_complex_input_cardinality_bound](abiEncoderAggregateProbeScript.sml#L291)
- [encoder_dynamic_tuple_no_same_shape_representative](abiEncoderAggregateProbeScript.sml#L299)

### abiEncoderArraySourceSpine

- [abi_encoder_array_prepare_raw_transport](abiEncoderArraySourceSpineScript.sml#L10)

### abiEncoderArraySpine

- [abi_encoder_array_tail_raw_control](abiEncoderArraySpineScript.sml#L9)
- [abi_encoder_array_spine_dynamic_run](abiEncoderArraySpineScript.sml#L34)

### abiEncoderChildContext

- [abi_encoder_static_child_structural_context](abiEncoderChildContextScript.sml#L46)

### abiEncoderChildSourcePhase

- [abi_encoder_child_static_place_raw_transport](abiEncoderChildSourcePhaseScript.sml#L8)

### abiEncoderCompositionCompat

- [abi_encoder_child_sequence_compose](abiEncoderCompositionCompatScript.sml#L9)
- [abi_encoder_weak_child_sequence](abiEncoderCompositionCompatScript.sml#L32)
- [abi_encoder_rich_child_sequence](abiEncoderCompositionCompatScript.sml#L52)
- [abi_encoder_scratch_call_sequence](abiEncoderCompositionCompatScript.sml#L74)
- [abi_encoder_correct_call_sequence](abiEncoderCompositionCompatScript.sml#L110)
- [abi_encoder_shared_call_sequence](abiEncoderCompositionCompatScript.sml#L142)
- [abi_encoder_array_child_compat](abiEncoderCompositionCompatScript.sml#L176)

### abiEncoderEffectProbe

- [alias_entry_phi_prefix_zero](abiEncoderEffectProbeScript.sml#L8)
- [alias_function_end_phi_prefix_zero](abiEncoderEffectProbeScript.sml#L14)
- [effect_probe_evolution](abiEncoderEffectProbeScript.sml#L31)
- [effect_probe_registered_and_reserve](abiEncoderEffectProbeScript.sml#L38)
- [effect_probe_physical_frame](abiEncoderEffectProbeScript.sml#L45)
- [effect_probe_reserve_unregistered](abiEncoderEffectProbeScript.sml#L56)
- [effect_probe_no_public_frame](abiEncoderEffectProbeScript.sml#L67)
- [effect_probe_initial_scratch](abiEncoderEffectProbeScript.sml#L79)

### abiEncoderEntry

- [abi_encoder_prune_limit_fresh](abiEncoderEntryScript.sml#L7)
- [abi_encoder_pruned_entry](abiEncoderEntryScript.sml#L16)

### abiEncoderEnvelopeAdapter

- [abi_encoder_envelope_disjoint](abiEncoderEnvelopeAdapterScript.sml#L9)
- [abi_encoder_pre_shared](abiEncoderEnvelopeAdapterScript.sml#L26)
- [abi_encoder_scratch_frame_envelope](abiEncoderEnvelopeAdapterScript.sml#L38)
- [abi_encoder_scratch_effect_envelope](abiEncoderEnvelopeAdapterScript.sml#L55)
- [abi_encoder_shared_correct](abiEncoderEnvelopeAdapterScript.sml#L78)

### abiEncoderExactWriteProbe

- [encoder_exact_registered_mstore](abiEncoderExactWriteProbeScript.sml#L16)
- [encoder_exact_registered_step](abiEncoderExactWriteProbeScript.sml#L27)
- [encoder_exact_writes_trans](abiEncoderExactWriteProbeScript.sml#L43)
- [encoder_exact_writes_subwindow](abiEncoderExactWriteProbeScript.sml#L56)
- [encoder_exact_output_mstore](abiEncoderExactWriteProbeScript.sml#L64)
- [encoder_dynamic_iteration_bounds](abiEncoderExactWriteProbeScript.sml#L76)
- [encoder_dynamic_iteration_exact](abiEncoderExactWriteProbeScript.sml#L91)
- [encoder_dynamic_iteration_stores](abiEncoderExactWriteProbeScript.sml#L130)
- [encoder_registered_cell_initialization_and_repeat](abiEncoderExactWriteProbeScript.sml#L150)
- [encoder_dynamic_iteration_word_addresses](abiEncoderExactWriteProbeScript.sml#L160)
- [encoder_dynamic_input_head_size](abiEncoderExactWriteProbeScript.sml#L171)

### abiEncoderExitPhi

- [abi_encoder_exit_nonempty_bind](abiEncoderExitPhiScript.sml#L18)
- [abi_encoder_exit_nonempty_ignore](abiEncoderExitPhiScript.sml#L26)
- [abi_encoder_exit_nonempty_emit](abiEncoderExitPhiScript.sml#L33)
- [abi_encoder_nonempty_preserving](abiEncoderExitPhiScript.sml#L42)
- [abi_encoder_empty_preserving_bind](abiEncoderExitPhiScript.sml#L49)
- [abi_encoder_empty_preserving_ignore](abiEncoderExitPhiScript.sml#L57)
- [abi_encoder_empty_preserving_return](abiEncoderExitPhiScript.sml#L65)
- [abi_encoder_empty_preserving_prims](abiEncoderExitPhiScript.sml#L95)
- [abi_encoder_empty_preserving_alloc](abiEncoderExitPhiScript.sml#L132)
- [abi_encoder_empty_preserving_static](abiEncoderExitPhiScript.sml#L138)
- [abi_encoder_empty_preserving_mutual](abiEncoderExitPhiScript.sml#L144)
- [abi_encoder_core_exit_nonempty](abiEncoderExitPhiScript.sml#L162)
- [abi_encoder_nonempty_prefix_phi](abiEncoderExitPhiScript.sml#L170)
- [abi_encoder_core_containing_exit_phi](abiEncoderExitPhiScript.sml#L181)

### abiEncoderExtendControl

- [abi_encoder_observer_step_extend_sim](abiEncoderExtendControlScript.sml#L9)
- [abi_encoder_branch_phis_extend_sim](abiEncoderExtendControlScript.sml#L20)
- [abi_encoder_vars_extend_jump](abiEncoderExtendControlScript.sml#L37)
- [abi_encoder_loop_entry_extend_sim](abiEncoderExtendControlScript.sml#L45)
- [abi_encoder_array_loop_entry_extend_sim](abiEncoderExtendControlScript.sml#L62)
- [abi_encoder_extend_finite_iteration](abiEncoderExtendControlScript.sml#L76)
- [abi_encoder_array_header_extend_sim](abiEncoderExtendControlScript.sml#L101)
- [abi_encoder_array_loop_header_extend_sim](abiEncoderExtendControlScript.sml#L131)

### abiEncoderExtendSim

- [abi_encoder_extend_sim_sim](abiEncoderExtendSimScript.sml#L14)
- [abi_encoder_extend_sim_refl](abiEncoderExtendSimScript.sml#L20)
- [abi_encoder_extend_sim_trans](abiEncoderExtendSimScript.sml#L27)
- [abi_encoder_sequence_extend](abiEncoderExtendSimScript.sml#L38)
- [abi_encoder_run_sequence_extend_sim](abiEncoderExtendSimScript.sml#L54)

### abiEncoderFragmentBridge

- [enc_frame_assemble](abiEncoderFragmentBridgeScript.sml#L8)
- [enc_scratch_stop_view](abiEncoderFragmentBridgeScript.sml#L29)
- [enc_frame_stop_view](abiEncoderFragmentBridgeScript.sml#L38)
- [enc_scratch_vars_extend](abiEncoderFragmentBridgeScript.sml#L50)

### abiEncoderFragmentFrame

- [abi_encoder_budget_registered_frame](abiEncoderFragmentFrameScript.sml#L9)
- [abi_encoder_restored_frame](abiEncoderFragmentFrameScript.sml#L25)

### abiEncoderFragment

- [compile_abi_encode_to_buf_frag](abiEncoderFragmentScript.sml#L18)

### abiEncoderInterfaceProbe

- [encoder_alloca_store_probe](abiEncoderInterfaceProbeScript.sml#L9)
- [encoder_word_prefix_restore_probe](abiEncoderInterfaceProbeScript.sml#L35)

### abiEncoderLabelAliasProbe

- [alias_entry_exit_equal](abiEncoderLabelAliasProbeScript.sml#L38)
- [alias_containing_function](abiEncoderLabelAliasProbeScript.sml#L46)
- [alias_first_cut_trivial](abiEncoderLabelAliasProbeScript.sml#L52)
- [alias_entry_emitted](abiEncoderLabelAliasProbeScript.sml#L66)
- [alias_no_stop_observer](abiEncoderLabelAliasProbeScript.sml#L75)
- [alias_compile_equation](abiEncoderLabelAliasProbeScript.sml#L88)

### abiEncoderLeafGlobals

- [abi_encoder_leaf_step_globals](abiEncoderLeafGlobalsScript.sml#L8)
- [abi_encoder_leaf_sequence_globals](abiEncoderLeafGlobalsScript.sml#L20)
- [abi_encoder_word_global_code](abiEncoderLeafGlobalsScript.sml#L35)
- [abi_encoder_copy_global_code](abiEncoderLeafGlobalsScript.sml#L47)
- [abi_encoder_bytes_global_code](abiEncoderLeafGlobalsScript.sml#L59)

### abiEncoderLeafSafety

- [local_prefix_nonterminator_inv](abiEncoderLeafSafetyScript.sml#L9)
- [local_prefix_at_cut](abiEncoderLeafSafetyScript.sml#L25)
- [abi_word_prefix_fetch](abiEncoderLeafSafetyScript.sml#L31)
- [word_load_step_inv](abiEncoderLeafSafetyScript.sml#L49)
- [word_live_destination_update](abiEncoderLeafSafetyScript.sml#L58)
- [abi_word_prefix_state](abiEncoderLeafSafetyScript.sml#L69)
- [abi_word_prefix_exact_writes](abiEncoderLeafSafetyScript.sml#L109)
- [abi_word_prefix_allocations](abiEncoderLeafSafetyScript.sml#L125)
- [abi_word_prefix_public_state](abiEncoderLeafSafetyScript.sml#L137)

### abiEncoderMemberPhaseEffect

- [abi_encoder_member_binary_registered](abiEncoderMemberPhaseEffectScript.sml#L9)
- [abi_encoder_member_load_registered](abiEncoderMemberPhaseEffectScript.sml#L24)
- [abi_encoder_member_step_globals](abiEncoderMemberPhaseEffectScript.sml#L40)
- [abi_encoder_member_phase_globals](abiEncoderMemberPhaseEffectScript.sml#L51)
- [abi_encoder_member_suffix_opcodes](abiEncoderMemberPhaseEffectScript.sml#L71)
- [abi_encoder_member_cursor_registered](abiEncoderMemberPhaseEffectScript.sml#L83)
- [abi_encoder_member_prefix_opcodes](abiEncoderMemberPhaseEffectScript.sml#L112)
- [abi_encoder_member_prefix_registered](abiEncoderMemberPhaseEffectScript.sml#L124)

### abiEncoderMemberPhaseExec

- [abi_scratch_members_prepare_raw_transport](abiEncoderMemberPhaseExecScript.sml#L18)
- [abi_scratch_member_static_place_raw_transport](abiEncoderMemberPhaseExecScript.sml#L66)
- [abi_scratch_complex_finish_raw_transport](abiEncoderMemberPhaseExecScript.sml#L92)
- [abi_scratch_members_prepare_raw_compat](abiEncoderMemberPhaseExecScript.sml#L123)

### abiEncoderMemberPhaseRaw

- [abi_encoder_member_binary_raw](abiEncoderMemberPhaseRawScript.sml#L17)
- [abi_encoder_member_binary_transport](abiEncoderMemberPhaseRawScript.sml#L29)
- [abi_encoder_member_load_raw](abiEncoderMemberPhaseRawScript.sml#L47)
- [abi_encoder_member_load_transport](abiEncoderMemberPhaseRawScript.sml#L59)
- [abi_encoder_member_cursor_raw](abiEncoderMemberPhaseRawScript.sml#L77)
- [abi_encoder_member_cursor_transport](abiEncoderMemberPhaseRawScript.sml#L92)
- [abi_encoder_member_tail_raw](abiEncoderMemberPhaseRawScript.sml#L114)
- [abi_encoder_member_tail_transport](abiEncoderMemberPhaseRawScript.sml#L129)
- [abi_encoder_member_phase_extend_sim](abiEncoderMemberPhaseRawScript.sml#L146)
- [abi_encoder_member_binary_raw_sim](abiEncoderMemberPhaseRawScript.sml#L158)
- [abi_encoder_member_prefix_raw](abiEncoderMemberPhaseRawScript.sml#L179)
- [abi_encoder_member_prefix_transport](abiEncoderMemberPhaseRawScript.sml#L194)
- [abi_encoder_member_prefix_control](abiEncoderMemberPhaseRawScript.sml#L212)
- [abi_encoder_member_cursor_bytes](abiEncoderMemberPhaseRawScript.sml#L238)

### abiEncoderMemberSourceAdapter

- [abi_encoder_static_child_spine_reach](abiEncoderMemberSourceAdapterScript.sml#L14)
- [abi_encoder_source_suffix_raw_post](abiEncoderMemberSourceAdapterScript.sml#L45)
- [abi_encoder_source_suffix_raw_sim](abiEncoderMemberSourceAdapterScript.sml#L59)
- [abi_encoder_source_suffix_raw_control](abiEncoderMemberSourceAdapterScript.sml#L73)
- [abi_encoder_source_dynamic_finish_transport](abiEncoderMemberSourceAdapterScript.sml#L96)
- [abi_encoder_source_dynamic_prepare_transport](abiEncoderMemberSourceAdapterScript.sml#L142)
- [abi_encoder_source_dynamic_core_run](abiEncoderMemberSourceAdapterScript.sml#L182)
- [abi_encoder_member_source_dynamic_input](abiEncoderMemberSourceAdapterScript.sml#L221)
- [abi_encoder_member_source_dynamic_output](abiEncoderMemberSourceAdapterScript.sml#L274)
- [abi_encoder_dynamic_child_spine_reach](abiEncoderMemberSourceAdapterScript.sml#L351)

### abiEncoderMemberSourceContract

- [abi_encoder_member_source_core_run](abiEncoderMemberSourceContractScript.sml#L32)
- [abi_encoder_member_source_child_run](abiEncoderMemberSourceContractScript.sml#L45)
- [abi_encoder_member_source_core_saved](abiEncoderMemberSourceContractScript.sml#L60)
- [abi_encoder_member_source_dynamic_run](abiEncoderMemberSourceContractScript.sml#L109)
- [abi_encoder_member_source_dynamic_saved](abiEncoderMemberSourceContractScript.sml#L121)
- [abi_encoder_member_source_dynamic_child_run](abiEncoderMemberSourceContractScript.sml#L135)

### abiEncoderMemberSourceInterpret

- [abi_encoder_member_source_static_input](abiEncoderMemberSourceInterpretScript.sml#L10)
- [abi_encoder_member_source_static_output](abiEncoderMemberSourceInterpretScript.sml#L46)

### abiEncoderMemberSourcePhase

- [abi_encoder_members_prepare_raw_transport](abiEncoderMemberSourcePhaseScript.sml#L13)
- [abi_encoder_member_static_place_raw_transport](abiEncoderMemberSourcePhaseScript.sml#L59)
- [abi_encoder_complex_finish_raw_transport](abiEncoderMemberSourcePhaseScript.sml#L71)
- [abi_encoder_members_prepare_raw_compat](abiEncoderMemberSourcePhaseScript.sml#L100)

### abiEncoderMemberSpineCompat

- [abi_encoder_spine_shared_core_run](abiEncoderMemberSpineCompatScript.sml#L39)
- [abi_encoder_spine_shared_input_address](abiEncoderMemberSpineCompatScript.sml#L51)
- [abi_encoder_spine_static_shared_pre](abiEncoderMemberSpineCompatScript.sml#L82)
- [abi_encoder_spine_static_shared_transport](abiEncoderMemberSpineCompatScript.sml#L114)
- [abi_encoder_spine_dynamic_shared_pre](abiEncoderMemberSpineCompatScript.sml#L163)
- [abi_encoder_spine_cursor_post](abiEncoderMemberSpineCompatScript.sml#L197)
- [abi_encoder_spine_prefix_extend_sim](abiEncoderMemberSpineCompatScript.sml#L211)
- [abi_encoder_spine_suffix_extend_sim](abiEncoderMemberSpineCompatScript.sml#L224)
- [abi_encoder_spine_dynamic_shared_sim](abiEncoderMemberSpineCompatScript.sml#L237)
- [abi_encoder_spine_shared_registered_window](abiEncoderMemberSpineCompatScript.sml#L261)
- [abi_encoder_spine_dynamic_shared_effects](abiEncoderMemberSpineCompatScript.sml#L279)

### abiEncoderMemberSpine

- [abi_encoder_spine_child_compile](abiEncoderMemberSpineScript.sml#L43)
- [abi_encoder_member_spine_compile](abiEncoderMemberSpineScript.sml#L54)
- [abi_encoder_spine_child_mono](abiEncoderMemberSpineScript.sml#L69)
- [abi_encoder_member_spine_mono](abiEncoderMemberSpineScript.sml#L78)
- [abi_encoder_spine_static_run](abiEncoderMemberSpineScript.sml#L104)
- [abi_encoder_spine_cursor_run](abiEncoderMemberSpineScript.sml#L139)
- [abi_encoder_spine_dynamic_run](abiEncoderMemberSpineScript.sml#L150)
- [abi_encoder_member_spine_fold](abiEncoderMemberSpineScript.sml#L185)
- [abi_encoder_spine_cons_code](abiEncoderMemberSpineScript.sml#L211)
- [abi_encoder_spine_child_generate](abiEncoderMemberSpineScript.sml#L282)
- [abi_encoder_spine_cons_layout](abiEncoderMemberSpineScript.sml#L331)
- [abi_encoder_member_spine_generate](abiEncoderMemberSpineScript.sml#L351)

### abiEncoderMembersCorrect

- [abi_encoder_members_correct_from_spine](abiEncoderMembersCorrectScript.sml#L22) (local)

### abiEncoderMembersEndpoint

- [abi_encoder_members_static_endpoint](abiEncoderMembersEndpointScript.sml#L11)
- [abi_encoder_members_dynamic_endpoint](abiEncoderMembersEndpointScript.sml#L61)
- [abi_encoder_members_origin_transport](abiEncoderMembersEndpointScript.sml#L117)

### abiEncoderObserverCode

- [abi_word_observer_safe](abiEncoderObserverCodeScript.sml#L23)
- [abi_word_observer_closed](abiEncoderObserverCodeScript.sml#L36)
- [abi_word_compiler_shape](abiEncoderObserverCodeScript.sml#L49)
- [abi_word_observer_has_code](abiEncoderObserverCodeScript.sml#L65)
- [abi_word_phi_prefix_suffix](abiEncoderObserverCodeScript.sml#L77) (local)
- [abi_word_observer_agrees](abiEncoderObserverCodeScript.sml#L95)
- [abi_header_observer_safe](abiEncoderObserverCodeScript.sml#L132)
- [abi_header_observer_closed](abiEncoderObserverCodeScript.sml#L146)
- [abi_header_observer_agrees](abiEncoderObserverCodeScript.sml#L161)

### abiEncoderObserver

- [stop_view_fields](abiEncoderObserverScript.sml#L11)
- [stop_view_operand](abiEncoderObserverScript.sml#L22)
- [run_from_stop_view](abiEncoderObserverScript.sml#L29)
- [abi_decode_sim_stop_run](abiEncoderObserverScript.sml#L39)
- [abi_observer_step_sim](abiEncoderObserverScript.sml#L76)
- [local_prefix_sim](abiEncoderObserverScript.sml#L90)
- [eval_phis_prefix](abiEncoderObserverScript.sml#L102)
- [abi_observer_step_transfer](abiEncoderObserverScript.sml#L128)
- [local_prefix_transfer](abiEncoderObserverScript.sml#L145)
- [observer_run_prefix_aux](abiEncoderObserverScript.sml#L171)
- [observer_run_prefix](abiEncoderObserverScript.sml#L249)
- [observer_same_block_probe](abiEncoderObserverScript.sml#L260)
- [observer_jump_phi_probe](abiEncoderObserverScript.sml#L277)
- [abi_observer_step_region_transfer](abiEncoderObserverScript.sml#L327)
- [local_prefix_region_transfer](abiEncoderObserverScript.sml#L347)
- [observer_run_prefix_transfer](abiEncoderObserverScript.sml#L363)
- [observer_same_block_region_closed](abiEncoderObserverScript.sml#L375)
- [observer_same_block_region_agrees](abiEncoderObserverScript.sml#L388)
- [observer_same_block_suffix_transfer](abiEncoderObserverScript.sml#L403)
- [observer_jump_phi_region_closed](abiEncoderObserverScript.sml#L420)
- [observer_jump_phi_region_agrees](abiEncoderObserverScript.sml#L438)
- [observer_jump_phi_suffix_transfer](abiEncoderObserverScript.sml#L459)
- [observer_setfmp_halted_probe](abiEncoderObserverScript.sml#L498)
- [observer_same_block_not_closed](abiEncoderObserverScript.sml#L505)
- [observer_same_block_region_safe](abiEncoderObserverScript.sml#L520)
- [observer_jump_phi_region_safe](abiEncoderObserverScript.sml#L533)
- [observer_old_prefix_region_safe](abiEncoderObserverScript.sml#L549)
- [observer_old_prefix_region_closed](abiEncoderObserverScript.sml#L562)
- [observer_old_stop_or_invoke_not_closed](abiEncoderObserverScript.sml#L575)
- [observer_old_stop_prefix_probe](abiEncoderObserverScript.sml#L591)
- [observer_old_invoke_prefix_probe](abiEncoderObserverScript.sml#L608)
- [observer_region_run_prefix_aux](abiEncoderObserverScript.sml#L625)
- [observer_region_run_prefix](abiEncoderObserverScript.sml#L718)
- [observer_region_run_prefix_transfer](abiEncoderObserverScript.sml#L730)

### abiEncoderOpenInputFrame

- [abi_encoder_open_input_mem_agree](abiEncoderOpenInputFrameScript.sml#L7)
- [abi_encoder_open_input_empty_memory](abiEncoderOpenInputFrameScript.sml#L48)
- [abi_encoder_zero_aware_separation](abiEncoderOpenInputFrameScript.sml#L56)

### abiEncoderOpenInput

- [abi_encoder_input_open](abiEncoderOpenInputScript.sml#L63)
- [abi_encoder_open_input_capacity](abiEncoderOpenInputScript.sml#L72)
- [abi_encoder_open_input_valid](abiEncoderOpenInputScript.sml#L87)
- [abi_encoder_open_complex_iff](abiEncoderOpenInputScript.sml#L103)
- [abi_encoder_open_complex_nil](abiEncoderOpenInputScript.sml#L116)
- [abi_encoder_open_complex_cons](abiEncoderOpenInputScript.sml#L124)
- [abi_encoder_open_enc_tuple_length](abiEncoderOpenInputScript.sml#L149)
- [abi_encoder_open_tuple_length](abiEncoderOpenInputScript.sml#L166)
- [abi_encoder_open_static_tuple_size](abiEncoderOpenInputScript.sml#L175)
- [abi_encoder_open_replicate_static](abiEncoderOpenInputScript.sml#L185)
- [abi_encoder_open_replicate_dynamic](abiEncoderOpenInputScript.sml#L191)
- [abi_encoder_structural_valid_layout](abiEncoderOpenInputScript.sml#L197)
- [abi_encoder_open_heads_length](abiEncoderOpenInputScript.sml#L219)
- [abi_encoder_structural_list_layout](abiEncoderOpenInputScript.sml#L229)
- [abi_encoder_open_members_layout](abiEncoderOpenInputScript.sml#L236)
- [abi_encoder_open_complex_cons_intro](abiEncoderOpenInputScript.sml#L270)
- [abi_encoder_open_zero_prefix](abiEncoderOpenInputScript.sml#L288)
- [abi_encoder_open_giant_zero_prefix](abiEncoderOpenInputScript.sml#L311)

### abiEncoderOpenPrefix

- [abi_encoder_open_prefix_tail_advance](abiEncoderOpenPrefixScript.sml#L5)
- [abi_encoder_open_prefix_head_advance](abiEncoderOpenPrefixScript.sml#L15)

### abiEncoderPrefixSafety

- [abi_observer_step_functional](abiEncoderPrefixSafetyScript.sml#L6)
- [local_prefix_endpoint_unique](abiEncoderPrefixSafetyScript.sml#L13)

### abiEncoderPrimitiveEffect

- [abi_encoder_registered_effect_mstore](abiEncoderPrimitiveEffectScript.sml#L8)
- [abi_encoder_registered_slot_store](abiEncoderPrimitiveEffectScript.sml#L26)
- [abi_encoder_output_store](abiEncoderPrimitiveEffectScript.sml#L34)
- [abi_encoder_primitive_alloca_inv](abiEncoderPrimitiveEffectScript.sml#L42)
- [abi_encoder_registered_output_copy](abiEncoderPrimitiveEffectScript.sml#L51)
- [abi_encoder_register_alloca_inv](abiEncoderPrimitiveEffectScript.sml#L63)
- [abi_encoder_registered_allocation](abiEncoderPrimitiveEffectScript.sml#L78)
- [abi_encoder_registered_update_var](abiEncoderPrimitiveEffectScript.sml#L88)
- [abi_encoder_registered_inst_idx](abiEncoderPrimitiveEffectScript.sml#L94)
- [abi_encoder_inst_idx_alloca_inv](abiEncoderPrimitiveEffectScript.sml#L100)

### abiEncoderRegisteredEffect

- [abi_encoder_registered_effect_refl](abiEncoderRegisteredEffectScript.sml#L19)
- [abi_encoder_registered_effect_allocated](abiEncoderRegisteredEffectScript.sml#L25)
- [abi_encoder_registered_effect_trans](abiEncoderRegisteredEffectScript.sml#L32)
- [abi_encoder_registered_effect_enlarge](abiEncoderRegisteredEffectScript.sml#L41)

### abiEncoderRegisteredFrame

- [abi_encoder_registered_effect_frame](abiEncoderRegisteredFrameScript.sml#L6)

### abiEncoderResourceAdapter

- [abi_encoder_zero_source_separation_diagnostic](abiEncoderResourceAdapterScript.sml#L11)
- [abi_encoder_zero_source_value_diagnostic](abiEncoderResourceAdapterScript.sml#L25)
- [abi_encoder_zero_source_pre_diagnostic](abiEncoderResourceAdapterScript.sml#L45)
- [abi_encoder_pre_memory_bounds](abiEncoderResourceAdapterScript.sml#L56)
- [abi_encoder_zero_source_open_diagnostic](abiEncoderResourceAdapterScript.sml#L64)
- [abi_encoder_zero_source_open_transport](abiEncoderResourceAdapterScript.sml#L76)
- [abi_encoder_fragment_ids](abiEncoderResourceAdapterScript.sml#L84)
- [abi_encoder_fragment_missing](abiEncoderResourceAdapterScript.sml#L90)
- [abi_encoder_scratch_budget](abiEncoderResourceAdapterScript.sml#L98)
- [abi_encoder_scratch_footprint](abiEncoderResourceAdapterScript.sml#L117)
- [abi_encoder_pre_operand_live](abiEncoderResourceAdapterScript.sml#L131)
- [abi_encoder_pre_prune_eval](abiEncoderResourceAdapterScript.sml#L140)
- [abi_encoder_prune_scratch](abiEncoderResourceAdapterScript.sml#L148)
- [abi_encoder_prune_pre](abiEncoderResourceAdapterScript.sml#L156)
- [abi_encoder_budget_scratch](abiEncoderResourceAdapterScript.sml#L165)
- [abi_encoder_prune_entry](abiEncoderResourceAdapterScript.sml#L177)

### abiEncoderScratchTransport

- [abi_encoder_child_scratch_allocations](abiEncoderScratchTransportScript.sml#L6)
- [abi_encoder_address_scratch_disjoint](abiEncoderScratchTransportScript.sml#L13)

### abiEncoderSharedArrayAddress

- [abi_encoder_array_address_opcodes](abiEncoderSharedArrayAddressScript.sml#L10) (local)
- [abi_encoder_array_address_step_globals](abiEncoderSharedArrayAddressScript.sml#L23) (local)
- [abi_encoder_array_address_raw_globals](abiEncoderSharedArrayAddressScript.sml#L34)
- [abi_encoder_shared_array_address_reach](abiEncoderSharedArrayAddressScript.sml#L53)

### abiEncoderSharedArrayBackedge

- [abi_encoder_array_backedge_extend_state](abiEncoderSharedArrayBackedgeScript.sml#L14)
- [abi_encoder_array_backedge_extend_sim](abiEncoderSharedArrayBackedgeScript.sml#L27)
- [abi_encoder_array_backedge_registered](abiEncoderSharedArrayBackedgeScript.sml#L52)
- [abi_encoder_shared_array_backedge_reach](abiEncoderSharedArrayBackedgeScript.sml#L70)
- [abi_encoder_shared_input_registered_write](abiEncoderSharedArrayBackedgeScript.sml#L105)
- [abi_encoder_shared_array_backedge_memory](abiEncoderSharedArrayBackedgeScript.sml#L128)

### abiEncoderSharedArrayBody

- [abi_encoder_shared_array_body_address](abiEncoderSharedArrayBodyScript.sml#L18)
- [abi_encoder_shared_array_body_child_input](abiEncoderSharedArrayBodyScript.sml#L87) (local)
- [abi_encoder_shared_array_dynamic_body_run_retained](abiEncoderSharedArrayBodyScript.sml#L122) (local)
- [abi_encoder_shared_array_dynamic_body_run](abiEncoderSharedArrayBodyScript.sml#L281) (local)
- [abi_encoder_shared_array_dynamic_body](abiEncoderSharedArrayBodyScript.sml#L351)
- [abi_encoder_shared_array_static_body](abiEncoderSharedArrayBodyScript.sml#L595)

### abiEncoderSharedArrayComplete

- [abi_encoder_shared_array_exit_run](abiEncoderSharedArrayCompleteScript.sml#L12)
- [abi_encoder_shared_array_index_exit_run](abiEncoderSharedArrayCompleteScript.sml#L63)
- [abi_encoder_shared_array_index_complete](abiEncoderSharedArrayCompleteScript.sml#L116)

### abiEncoderSharedArrayCountPrepare

- [abi_encoder_shared_array_count_prepare](abiEncoderSharedArrayCountPrepareScript.sml#L11)

### abiEncoderSharedArrayCount

- [abi_encoder_array_count_raw_transport](abiEncoderSharedArrayCountScript.sml#L14)
- [abi_encoder_array_count_opcodes](abiEncoderSharedArrayCountScript.sml#L33)
- [abi_encoder_array_count_registered](abiEncoderSharedArrayCountScript.sml#L45)
- [abi_encoder_array_count_extend](abiEncoderSharedArrayCountScript.sml#L66)
- [abi_encoder_shared_array_count_effect](abiEncoderSharedArrayCountScript.sml#L80)
- [abi_encoder_shared_array_count_input_facts](abiEncoderSharedArrayCountScript.sml#L100)
- [abi_encoder_shared_array_count_input](abiEncoderSharedArrayCountScript.sml#L116)

### abiEncoderSharedArrayDynamicInit

- [abi_encoder_shared_array_dynamic_init](abiEncoderSharedArrayDynamicInitScript.sml#L10)

### abiEncoderSharedArrayDynamicLoop

- [abi_encoder_shared_array_dynamic_loop](abiEncoderSharedArrayDynamicLoopScript.sml#L10)

### abiEncoderSharedArrayEntry

- [abi_encoder_array_jump_extend_state](abiEncoderSharedArrayEntryScript.sml#L13)
- [abi_encoder_array_loop_entry_extend](abiEncoderSharedArrayEntryScript.sml#L21)
- [abi_encoder_shared_array_loop_enter](abiEncoderSharedArrayEntryScript.sml#L37)

### abiEncoderSharedArrayExit

- [abi_encoder_phase_current_bb](abiEncoderSharedArrayExitScript.sml#L12) (local)
- [abi_encoder_array_static_exit_raw_transport](abiEncoderSharedArrayExitScript.sml#L26)
- [abi_encoder_array_dynamic_exit_raw_transport](abiEncoderSharedArrayExitScript.sml#L44)
- [abi_encoder_array_exit_opcodes](abiEncoderSharedArrayExitScript.sml#L63)
- [abi_encoder_array_exit_extend](abiEncoderSharedArrayExitScript.sml#L78)
- [abi_encoder_array_exit_readonly](abiEncoderSharedArrayExitScript.sml#L94)
- [abi_encoder_array_exit_registered](abiEncoderSharedArrayExitScript.sml#L119)
- [abi_encoder_array_exit_effect](abiEncoderSharedArrayExitScript.sml#L131)
- [abi_encoder_shared_array_exit_source](abiEncoderSharedArrayExitScript.sml#L150)

### abiEncoderSharedArrayFinishProtected

- [abi_encoder_shared_array_finish_protected](abiEncoderSharedArrayFinishProtectedScript.sml#L9)

### abiEncoderSharedArrayFinishRun

- [abi_encoder_shared_array_finish_run](abiEncoderSharedArrayFinishRunScript.sml#L10)

### abiEncoderSharedArrayFinish

- [abi_encoder_array_finish_raw_transport](abiEncoderSharedArrayFinishScript.sml#L11)
- [abi_encoder_array_finish_opcodes](abiEncoderSharedArrayFinishScript.sml#L30)
- [abi_encoder_array_finish_registered](abiEncoderSharedArrayFinishScript.sml#L42)
- [abi_encoder_array_finish_extend](abiEncoderSharedArrayFinishScript.sml#L67)
- [abi_encoder_shared_array_finish_effect](abiEncoderSharedArrayFinishScript.sml#L77)
- [abi_encoder_array_finish_preserves_output](abiEncoderSharedArrayFinishScript.sml#L104)

### abiEncoderSharedArrayHeader

- [abi_encoder_array_header_extend_state](abiEncoderSharedArrayHeaderScript.sml#L13)
- [abi_encoder_array_header_extend_sim](abiEncoderSharedArrayHeaderScript.sml#L29)
- [abi_encoder_array_header_registered](abiEncoderSharedArrayHeaderScript.sml#L60)
- [abi_encoder_shared_input_address](abiEncoderSharedArrayHeaderScript.sml#L69)
- [abi_encoder_shared_array_index_address](abiEncoderSharedArrayHeaderScript.sml#L81)
- [abi_encoder_shared_array_header_index](abiEncoderSharedArrayHeaderScript.sml#L114)

### abiEncoderSharedArrayIndexInit

- [abi_encoder_shared_array_index_prepare](abiEncoderSharedArrayIndexInitScript.sml#L13)

### abiEncoderSharedArrayIndex

- [abi_encoder_shared_array_index_initial](abiEncoderSharedArrayIndexScript.sml#L28)
- [abi_encoder_shared_array_index_facts](abiEncoderSharedArrayIndexScript.sml#L48)
- [abi_encoder_shared_array_index_advance](abiEncoderSharedArrayIndexScript.sml#L62)
- [abi_encoder_shared_array_index_exit_facts](abiEncoderSharedArrayIndexScript.sml#L94)
- [abi_encoder_shared_array_index_layout](abiEncoderSharedArrayIndexScript.sml#L116)
- [abi_encoder_shared_array_index_selected_input](abiEncoderSharedArrayIndexScript.sml#L129)

### abiEncoderSharedArrayInitFrame

- [abi_encoder_shared_array_prefix_scratch](abiEncoderSharedArrayInitFrameScript.sml#L8)

### abiEncoderSharedArrayInit

- [abi_encoder_cursor_update_inv](abiEncoderSharedArrayInitScript.sml#L13) (local)
- [abi_encoder_cursor_alloca_observations](abiEncoderSharedArrayInitScript.sml#L19)
- [abi_encoder_complex_prefix_raw_observations](abiEncoderSharedArrayInitScript.sml#L31)
- [abi_encoder_complex_prefix_raw_transport](abiEncoderSharedArrayInitScript.sml#L51)
- [abi_encoder_complex_prefix_raw_allocated](abiEncoderSharedArrayInitScript.sml#L66)
- [abi_encoder_complex_prefix_raw_registered](abiEncoderSharedArrayInitScript.sml#L84)
- [abi_encoder_complex_prefix_raw_extend](abiEncoderSharedArrayInitScript.sml#L109)

### abiEncoderSharedArrayInput

- [abi_encoder_open_array_iff](abiEncoderSharedArrayInputScript.sml#L11)
- [abi_encoder_shared_array_input_facts](abiEncoderSharedArrayInputScript.sml#L22)
- [abi_encoder_shared_array_selected_input](abiEncoderSharedArrayInputScript.sml#L39)
- [abi_encoder_open_array_length](abiEncoderSharedArrayInputScript.sml#L64)
- [abi_encoder_open_array_prefix_complete](abiEncoderSharedArrayInputScript.sml#L73)
- [abi_encoder_open_array_prefix_output_frame](abiEncoderSharedArrayInputScript.sml#L94)

### abiEncoderSharedArrayLoop

- [abi_encoder_shared_array_loop_header](abiEncoderSharedArrayLoopScript.sml#L10)
- [abi_encoder_shared_array_loop_round_finish](abiEncoderSharedArrayLoopScript.sml#L38)
- [abi_encoder_shared_array_loop_static_step](abiEncoderSharedArrayLoopScript.sml#L82)
- [abi_encoder_shared_array_loop_dynamic_step](abiEncoderSharedArrayLoopScript.sml#L143)
- [abi_encoder_shared_array_loop_finite](abiEncoderSharedArrayLoopScript.sml#L206)
- [abi_encoder_shared_array_loop_run](abiEncoderSharedArrayLoopScript.sml#L237)

### abiEncoderSharedArrayOuter

- [abi_encoder_shared_array_outer](abiEncoderSharedArrayOuterScript.sml#L10)

### abiEncoderSharedArrayOwner

- [abi_encoder_shared_array_static_body_owner](abiEncoderSharedArrayOwnerScript.sml#L10)
- [abi_encoder_shared_array_dynamic_body_owner](abiEncoderSharedArrayOwnerScript.sml#L69)
- [abi_encoder_shared_array_owner_effects](abiEncoderSharedArrayOwnerScript.sml#L128)

### abiEncoderSharedArrayParent

- [abi_encoder_shared_array_parent_prepare](abiEncoderSharedArrayParentScript.sml#L11)

### abiEncoderSharedArrayPrepare

- [abi_encoder_complex_prefix_raw_reach](abiEncoderSharedArrayPrepareScript.sml#L11)
- [abi_encoder_shared_cursor_prepare](abiEncoderSharedArrayPrepareScript.sml#L39)

### abiEncoderSharedArrayRound

- [abi_encoder_shared_array_round_finish](abiEncoderSharedArrayRoundScript.sml#L11)

### abiEncoderSharedArrayRun

- [abi_encoder_shared_array_prepared_run](abiEncoderSharedArrayRunScript.sml#L10)
- [abi_encoder_shared_array_prepared_complete](abiEncoderSharedArrayRunScript.sml#L50)

### abiEncoderSharedArray

- [abi_encoder_shared_array](abiEncoderSharedArrayScript.sml#L8)

### abiEncoderSharedArraySelectedLoop

- [abi_encoder_shared_array_selected_loop](abiEncoderSharedArraySelectedLoopScript.sml#L9)

### abiEncoderSharedArraySpine

- [abi_encoder_array_spine_shared_pre](abiEncoderSharedArraySpineScript.sml#L13)
- [abi_encoder_array_spine_cursor_saved](abiEncoderSharedArraySpineScript.sml#L44)
- [abi_encoder_array_spine_shared_run](abiEncoderSharedArraySpineScript.sml#L73)
- [abi_encoder_array_spine_tail_opcodes](abiEncoderSharedArraySpineScript.sml#L109)
- [abi_encoder_array_spine_tail_registered](abiEncoderSharedArraySpineScript.sml#L121)
- [abi_encoder_array_spine_tail_extend_sim](abiEncoderSharedArraySpineScript.sml#L142)
- [abi_encoder_array_spine_shared_effects](abiEncoderSharedArraySpineScript.sml#L154)
- [abi_encoder_array_spine_shared_sim](abiEncoderSharedArraySpineScript.sml#L205)

### abiEncoderSharedArrayStaticLoop

- [abi_encoder_shared_array_static_loop](abiEncoderSharedArrayStaticLoopScript.sml#L10)

### abiEncoderSharedArrayStep

- [abi_encoder_open_array_prefix_lengths](abiEncoderSharedArrayStepScript.sml#L9) (local)
- [abi_encoder_open_array_prefix_old_frame](abiEncoderSharedArrayStepScript.sml#L27) (local)
- [abi_encoder_open_array_static_step](abiEncoderSharedArrayStepScript.sml#L43)
- [abi_encoder_open_array_dynamic_step](abiEncoderSharedArrayStepScript.sml#L68)

### abiEncoderSharedArrayTailInit

- [abi_encoder_array_tail_init_raw_observations](abiEncoderSharedArrayTailInitScript.sml#L14)
- [abi_encoder_array_tail_init_raw_allocated](abiEncoderSharedArrayTailInitScript.sml#L35)
- [abi_encoder_array_tail_init_raw_transport](abiEncoderSharedArrayTailInitScript.sml#L54)
- [abi_encoder_array_tail_init_raw_extend](abiEncoderSharedArrayTailInitScript.sml#L69)
- [abi_encoder_array_tail_init_raw_registered](abiEncoderSharedArrayTailInitScript.sml#L79)
- [abi_encoder_array_tail_init_raw_reach](abiEncoderSharedArrayTailInitScript.sml#L101)
- [abi_encoder_shared_array_tail_prepare](abiEncoderSharedArrayTailInitScript.sml#L121)

### abiEncoderSharedArrayTail

- [abi_encoder_shared_array_tail_reach](abiEncoderSharedArrayTailScript.sml#L11)
- [abi_encoder_shared_array_tail_observations](abiEncoderSharedArrayTailScript.sml#L69)

### abiEncoderSharedComplex

- [abi_encoder_shared_complex_head_length](abiEncoderSharedComplexScript.sml#L11)
- [abi_encoder_shared_complex_prepare](abiEncoderSharedComplexScript.sml#L25)
- [abi_encoder_shared_complex_load_finish](abiEncoderSharedComplexScript.sml#L57)
- [abi_encoder_shared_complex_static_length](abiEncoderSharedComplexScript.sml#L92)
- [abi_encoder_shared_complex_static_run](abiEncoderSharedComplexScript.sml#L118)
- [abi_encoder_shared_complex_static](abiEncoderSharedComplexScript.sml#L145)
- [abi_encoder_shared_complex_slot_bound](abiEncoderSharedComplexScript.sml#L178) (local)
- [abi_encoder_shared_complex_effect_sequence](abiEncoderSharedComplexScript.sml#L194) (local)
- [abi_encoder_shared_complex_members_finish](abiEncoderSharedComplexScript.sml#L221)
- [abi_encoder_shared_complex_dynamic](abiEncoderSharedComplexScript.sml#L264)
- [abi_encoder_shared_complex](abiEncoderSharedComplexScript.sml#L305)

### abiEncoderSharedContract

- [abi_scratch_input_shared](abiEncoderSharedContractScript.sml#L55)
- [abi_encoder_shared_input_typed](abiEncoderSharedContractScript.sml#L64)
- [abi_encoder_shared_endpoint_bytes](abiEncoderSharedContractScript.sml#L73)
- [abi_encoder_shared_endpoint_output](abiEncoderSharedContractScript.sml#L80)
- [abi_encoder_shared_endpoint_scratch](abiEncoderSharedContractScript.sml#L87)
- [abi_encoder_shared_endpoint_registered](abiEncoderSharedContractScript.sml#L95)
- [abi_encoder_shared_endpoint_alloca_inv](abiEncoderSharedContractScript.sml#L103)
- [abi_encoder_shared_endpoint_block](abiEncoderSharedContractScript.sml#L110)
- [abi_encoder_shared_endpoint_index](abiEncoderSharedContractScript.sml#L117)
- [abi_encoder_shared_endpoint_nonhalted](abiEncoderSharedContractScript.sml#L124)
- [abi_encoder_shared_endpoint_extend_sim](abiEncoderSharedContractScript.sml#L131)
- [abi_encoder_shared_endpoint_sim](abiEncoderSharedContractScript.sml#L138)
- [abi_encoder_shared_run](abiEncoderSharedContractScript.sml#L146)
- [abi_encoder_shared_scratch](abiEncoderSharedContractScript.sml#L165)
- [abi_encoder_shared_input_inst_idx](abiEncoderSharedContractScript.sml#L178)
- [abi_encoder_shared_endpoint_end_index](abiEncoderSharedContractScript.sml#L188)
- [abi_encoder_shared_endpoint_intro](abiEncoderSharedContractScript.sml#L202)

### abiEncoderSharedInputEffect

- [abi_encoder_shared_input_effect](abiEncoderSharedInputEffectScript.sml#L8)
- [abi_encoder_shared_input_mono](abiEncoderSharedInputEffectScript.sml#L40)

### abiEncoderSharedLeafSequence

- [abi_encoder_sequence_post_registered](abiEncoderSharedLeafSequenceScript.sml#L9)
- [abi_encoder_sequence_post_alloca_inv](abiEncoderSharedLeafSequenceScript.sml#L20)
- [abi_encoder_shared_leaf_sequence](abiEncoderSharedLeafSequenceScript.sml#L29)

### abiEncoderSharedLeaves

- [abi_encoder_open_word_typed](abiEncoderSharedLeavesScript.sml#L12)
- [abi_encoder_open_copy_typed](abiEncoderSharedLeavesScript.sml#L19)
- [abi_encoder_open_bytes_typed](abiEncoderSharedLeavesScript.sml#L26)
- [abi_encoder_shared_word](abiEncoderSharedLeavesScript.sml#L34)
- [abi_encoder_shared_copy](abiEncoderSharedLeavesScript.sml#L56)
- [abi_encoder_shared_bytes](abiEncoderSharedLeavesScript.sml#L82)
- [abi_encoder_shared_empty](abiEncoderSharedLeavesScript.sml#L114)

### abiEncoderSharedMemberContract

- [abi_encoder_shared_member_core_run](abiEncoderSharedMemberContractScript.sml#L9)
- [abi_encoder_shared_member_dynamic_run](abiEncoderSharedMemberContractScript.sml#L36)
- [abi_encoder_shared_member_dynamic_saved](abiEncoderSharedMemberContractScript.sml#L49)
- [abi_encoder_shared_member_dynamic_cursor_input](abiEncoderSharedMemberContractScript.sml#L74)
- [abi_encoder_shared_members_child_dispatch](abiEncoderSharedMemberContractScript.sml#L110)
- [abi_encoder_shared_members_child_run](abiEncoderSharedMemberContractScript.sml#L124)

### abiEncoderSharedMembersCorrect

- [abi_encoder_shared_members_root_pre](abiEncoderSharedMembersCorrectScript.sml#L12)
- [abi_encoder_shared_members_initial_inv](abiEncoderSharedMembersCorrectScript.sml#L47)
- [abi_encoder_open_tuple_prefix_complete](abiEncoderSharedMembersCorrectScript.sml#L65)
- [abi_encoder_shared_members_final_output](abiEncoderSharedMembersCorrectScript.sml#L82)
- [abi_encoder_shared_members_correct](abiEncoderSharedMembersCorrectScript.sml#L105)

### abiEncoderSharedMembersEndpoint

- [abi_encoder_shared_members_static_endpoint](abiEncoderSharedMembersEndpointScript.sml#L13)
- [abi_encoder_shared_members_static_exit](abiEncoderSharedMembersEndpointScript.sml#L88)
- [abi_encoder_shared_members_dynamic_endpoint](abiEncoderSharedMembersEndpointScript.sml#L133)
- [abi_encoder_shared_members_dynamic_exit](abiEncoderSharedMembersEndpointScript.sml#L195)

### abiEncoderSharedMembersIndex

- [abi_encoder_shared_members_index_initial](abiEncoderSharedMembersIndexScript.sml#L46)
- [abi_encoder_shared_members_index_source](abiEncoderSharedMembersIndexScript.sml#L62)
- [abi_encoder_shared_members_index_empty](abiEncoderSharedMembersIndexScript.sml#L77)
- [abi_encoder_shared_members_inv_layout](abiEncoderSharedMembersIndexScript.sml#L96)
- [abi_encoder_shared_members_after_child](abiEncoderSharedMembersIndexScript.sml#L116)
- [abi_encoder_shared_members_origin_transport](abiEncoderSharedMembersIndexScript.sml#L152)
- [abi_encoder_shared_members_index_advance](abiEncoderSharedMembersIndexScript.sml#L191)

### abiEncoderSharedMembersInput

- [abi_encoder_shared_members_pre_mono](abiEncoderSharedMembersInputScript.sml#L23)
- [abi_encoder_shared_members_pre_address](abiEncoderSharedMembersInputScript.sml#L33)
- [abi_encoder_shared_members_pre_shape](abiEncoderSharedMembersInputScript.sml#L50)
- [abi_encoder_shared_members_pre_empty](abiEncoderSharedMembersInputScript.sml#L64)
- [abi_encoder_shared_open_input_frame](abiEncoderSharedMembersInputScript.sml#L70)
- [abi_encoder_shared_members_pre_effect](abiEncoderSharedMembersInputScript.sml#L81)
- [abi_encoder_shared_members_pre_cons](abiEncoderSharedMembersInputScript.sml#L113)
- [abi_encoder_shared_members_child_buffer](abiEncoderSharedMembersInputScript.sml#L137)

### abiEncoderSharedMembersInterpret

- [abi_encoder_shared_members_entry_input](abiEncoderSharedMembersInterpretScript.sml#L35)
- [abi_encoder_shared_members_entry_exit](abiEncoderSharedMembersInterpretScript.sml#L69)
- [abi_encoder_shared_members_index_cons_shape](abiEncoderSharedMembersInterpretScript.sml#L102)
- [abi_encoder_shared_members_layout_bound](abiEncoderSharedMembersInterpretScript.sml#L115) (local)
- [abi_encoder_shared_members_entry_prepare](abiEncoderSharedMembersInterpretScript.sml#L126)
- [abi_encoder_shared_members_empty_post](abiEncoderSharedMembersInterpretScript.sml#L168)
- [abi_encoder_shared_members_generate](abiEncoderSharedMembersInterpretScript.sml#L188)

### abiEncoderSharedMembersOutput

- [abi_encoder_shared_member_static_output](abiEncoderSharedMembersOutputScript.sml#L14)
- [abi_encoder_shared_member_dynamic_output](abiEncoderSharedMembersOutputScript.sml#L41)

### abiEncoderSharedMembersPrepare

- [abi_encoder_shared_members_prepare_raw_transport](abiEncoderSharedMembersPrepareScript.sml#L12)
- [abi_encoder_shared_members_prepare_extend](abiEncoderSharedMembersPrepareScript.sml#L55)
- [abi_encoder_shared_members_index_prepare](abiEncoderSharedMembersPrepareScript.sml#L69)

### abiEncoderSharedMembersRequest

- [abi_encoder_shared_member_static_input](abiEncoderSharedMembersRequestScript.sml#L11)
- [abi_encoder_shared_members_static_request](abiEncoderSharedMembersRequestScript.sml#L44)
- [abi_encoder_shared_member_dynamic_input](abiEncoderSharedMembersRequestScript.sml#L73)
- [abi_encoder_shared_members_dynamic_request](abiEncoderSharedMembersRequestScript.sml#L130)

### abiEncoderSharedOwner

- [abi_encoder_shared_input_owner](abiEncoderSharedOwnerScript.sml#L7)
- [abi_encoder_cursor_owner](abiEncoderSharedOwnerScript.sml#L17)

### abiEncoderSharedRecursive

- [abi_encoder_shared_admissible_mutual](abiEncoderSharedRecursiveScript.sml#L7)
- [abi_encoder_shared_admissible](abiEncoderSharedRecursiveScript.sml#L20)
- [abi_encoder_shared_translation](abiEncoderSharedRecursiveScript.sml#L26)

### abiEncoderSharedSuffix

- [abi_encoder_shared_suffix_observations](abiEncoderSharedSuffixScript.sml#L9)

### abiEncoderSourceAggregate

- [abi_encoder_enc_tuple_cong](abiEncoderSourceAggregateScript.sml#L7)
- [abi_encoder_head_lengths_cong](abiEncoderSourceAggregateScript.sml#L23)
- [abi_encoder_tuple_encoding_cong](abiEncoderSourceAggregateScript.sml#L38)
- [source_rep_metadata](abiEncoderSourceAggregateScript.sml#L76)
- [source_rep_transport](abiEncoderSourceAggregateScript.sml#L84)
- [source_reps_nil](abiEncoderSourceAggregateScript.sml#L94)
- [source_reps_index](abiEncoderSourceAggregateScript.sml#L100)
- [source_reps_cons](abiEncoderSourceAggregateScript.sml#L110)
- [abi_encoder_dynamic_empty_input](abiEncoderSourceAggregateScript.sml#L120)
- [abi_encoder_dynamic_empty_classification](abiEncoderSourceAggregateScript.sml#L128)
- [source_reps_lengths](abiEncoderSourceAggregateScript.sml#L135)
- [source_reps_span](abiEncoderSourceAggregateScript.sml#L142)
- [source_reps_full_span](abiEncoderSourceAggregateScript.sml#L158)
- [source_reps_members](abiEncoderSourceAggregateScript.sml#L168)
- [abi_encoder_source_complex_input](abiEncoderSourceAggregateScript.sml#L212)
- [abi_encoder_tuple_type_encoding](abiEncoderSourceAggregateScript.sml#L226)
- [abi_encoder_tuple_type_encoding_cong](abiEncoderSourceAggregateScript.sml#L233)
- [abi_encoder_dynamic_array_encoding_cong](abiEncoderSourceAggregateScript.sml#L250)
- [source_rep_static_copy](abiEncoderSourceAggregateScript.sml#L263)
- [source_translation_list](abiEncoderSourceAggregateScript.sml#L274)
- [source_reps_abi_metadata](abiEncoderSourceAggregateScript.sml#L280)
- [source_reps_any_dynamic](abiEncoderSourceAggregateScript.sml#L295)
- [static_tuple_sum](abiEncoderSourceAggregateScript.sml#L304) (local)
- [source_reps_tuple_head](abiEncoderSourceAggregateScript.sml#L310)

### abiEncoderSourceBridge

- [abi_enc_plan_static_leaf](abiEncoderSourceBridgeScript.sml#L8)
- [abi_enc_plan_admissible](abiEncoderSourceBridgeScript.sml#L18)
- [enc_pre_source_end_bound](abiEncoderSourceBridgeScript.sml#L27)
- [enc_pre_source_capacity_bound](abiEncoderSourceBridgeScript.sml#L34)

### abiEncoderSourceInvoke

- [abi_encoder_source_shared_input](abiEncoderSourceInvokeScript.sml#L9)
- [abi_encoder_source_shared_run](abiEncoderSourceInvokeScript.sml#L43)

### abiEncoderSourceMembersEntry

- [abi_encoder_source_members_index_prepare](abiEncoderSourceMembersEntryScript.sml#L12)
- [abi_encoder_source_members_static_request](abiEncoderSourceMembersEntryScript.sml#L47)
- [abi_encoder_source_members_dynamic_request](abiEncoderSourceMembersEntryScript.sml#L74)
- [abi_encoder_source_members_static_exit](abiEncoderSourceMembersEntryScript.sml#L112)
- [abi_encoder_source_members_dynamic_exit](abiEncoderSourceMembersEntryScript.sml#L146)
- [abi_encoder_source_members_index_cons_shape](abiEncoderSourceMembersEntryScript.sml#L183)

### abiEncoderSourceMembersIndex

- [abi_encoder_source_members_index_initial](abiEncoderSourceMembersIndexScript.sml#L24)
- [abi_encoder_source_members_index_source](abiEncoderSourceMembersIndexScript.sml#L39)
- [abi_encoder_source_members_index_empty](abiEncoderSourceMembersIndexScript.sml#L54)
- [abi_encoder_source_members_index_advance](abiEncoderSourceMembersIndexScript.sml#L73)

### abiEncoderSourceMembersInterpret

- [abi_encoder_source_members_child_dispatch](abiEncoderSourceMembersInterpretScript.sml#L19)
- [abi_encoder_source_members_child_run](abiEncoderSourceMembersInterpretScript.sml#L33)
- [abi_encoder_source_members_entry_input](abiEncoderSourceMembersInterpretScript.sml#L71)
- [abi_encoder_source_members_entry_exit](abiEncoderSourceMembersInterpretScript.sml#L98)
- [abi_encoder_source_members_layout_bound](abiEncoderSourceMembersInterpretScript.sml#L129) (local)
- [abi_encoder_source_members_entry_prepare](abiEncoderSourceMembersInterpretScript.sml#L140)
- [abi_encoder_source_members_empty_post](abiEncoderSourceMembersInterpretScript.sml#L176)
- [abi_encoder_source_members_generate](abiEncoderSourceMembersInterpretScript.sml#L195)

### abiEncoderSourcePrimitive

- [abi_encoder_copy32_word](abiEncoderSourcePrimitiveScript.sml#L6)
- [abi_encoder_word_source_shape](abiEncoderSourcePrimitiveScript.sml#L14)
- [source_rep_primitive](abiEncoderSourcePrimitiveScript.sml#L30)

### abiEncoderSourceProducer

- [abi_encoder_uniform_source](abiEncoderSourceProducerScript.sml#L7)
- [abi_encoder_source_window](abiEncoderSourceProducerScript.sml#L242)

### abiEncoderSourceTransport

- [abi_encoder_same_conversion](abiEncoderSourceTransportScript.sml#L7)
- [abi_encoder_elems_memory](abiEncoderSourceTransportScript.sml#L18)
- [abi_encoder_dense_source](abiEncoderSourceTransportScript.sml#L30)
- [abi_encoder_list_conversion](abiEncoderSourceTransportScript.sml#L44)
- [abi_encoder_tuple_memory](abiEncoderSourceTransportScript.sml#L53)
- [abi_encoder_tuple_source](abiEncoderSourceTransportScript.sml#L67)
- [abi_encoder_sparse_conversion](abiEncoderSourceTransportScript.sml#L83)
- [abi_encoder_sparse_source](abiEncoderSourceTransportScript.sml#L100)
- [abi_encoder_dynamic_source](abiEncoderSourceTransportScript.sml#L127)
- [abi_encoder_tuple_parent](abiEncoderSourceTransportScript.sml#L149)
- [abi_encoder_struct_parent](abiEncoderSourceTransportScript.sml#L176)
- [abi_encoder_sparse_zero_probe](abiEncoderSourceTransportScript.sml#L208)
- [abi_encoder_sparse_absent_probe](abiEncoderSourceTransportScript.sml#L215)

### abiEncoderSourceWindow

- [abi_encoder_uniform_block_representative](abiEncoderSourceWindowScript.sml#L8)
- [abi_encoder_uniform_aligned_representative](abiEncoderSourceWindowScript.sml#L33)
- [abi_encoder_uniform_static_source](abiEncoderSourceWindowScript.sml#L45)
- [abi_encoder_open_bytes_source](abiEncoderSourceWindowScript.sml#L67)
- [abi_encoder_open_string_source](abiEncoderSourceWindowScript.sml#L85)

### abiEncoderStaticRepresentative

- [abi_encoder_zero_copy_representative](abiEncoderStaticRepresentativeScript.sml#L6)
- [abi_encoder_static_zero_source_representative](abiEncoderStaticRepresentativeScript.sml#L16)
- [abi_encoder_fixed_omitted_default_window](abiEncoderStaticRepresentativeScript.sml#L32)
- [abi_encoder_bytes32_representative](abiEncoderStaticRepresentativeScript.sml#L41)
- [abi_encoder_static_pair_encoding](abiEncoderStaticRepresentativeScript.sml#L51)
- [abi_encoder_pair_typing](abiEncoderStaticRepresentativeScript.sml#L58)
- [abi_encoder_static_length_alignment_mutual](abiEncoderStaticRepresentativeScript.sml#L65)
- [abi_encoder_static_length_alignment](abiEncoderStaticRepresentativeScript.sml#L78)
- [abi_encoder_static_source_alignment](abiEncoderStaticRepresentativeScript.sml#L84)

### abiEncoderVarRestore

- [abi_encoder_vars_extend_fields](abiEncoderVarRestoreScript.sml#L8)
- [abi_encoder_shared_restore](abiEncoderVarRestoreScript.sml#L24)
- [abi_encoder_restored_operand](abiEncoderVarRestoreScript.sml#L59)

### abiEncoderVarTransport

- [abi_encoder_vars_extend_prev](abiEncoderVarTransportScript.sml#L7)
- [abi_encoder_one_phi_extend](abiEncoderVarTransportScript.sml#L16)
- [abi_encoder_phis_extend](abiEncoderVarTransportScript.sml#L25)
- [abi_encoder_eval_operands_inputs](abiEncoderVarTransportScript.sml#L49)
- [abi_encoder_pure3_inputs](abiEncoderVarTransportScript.sml#L58)
- [abi_encoder_extract_labels_inputs](abiEncoderVarTransportScript.sml#L65)
- [abi_encoder_log_inputs](abiEncoderVarTransportScript.sml#L76) (local)
- [abi_encoder_step_inputs_defined](abiEncoderVarTransportScript.sml#L95)
- [abi_encoder_step_extend_inputs](abiEncoderVarTransportScript.sml#L127) (local)
- [abi_encoder_vars_extend_frame](abiEncoderVarTransportScript.sml#L142) (local)
- [abi_encoder_step_extend_ignored](abiEncoderVarTransportScript.sml#L153) (local)
- [abi_encoder_step_extend](abiEncoderVarTransportScript.sml#L167)
- [abi_encoder_vars_extend_control](abiEncoderVarTransportScript.sml#L178)
- [abi_encoder_vars_extend_idx](abiEncoderVarTransportScript.sml#L187)
- [abi_encoder_observer_step_extend](abiEncoderVarTransportScript.sml#L195)
- [abi_encoder_local_prefix_extend](abiEncoderVarTransportScript.sml#L217)

### abiEncoderZeroFrame

- [abi_encoder_mem_bytes_singletons](abiEncoderZeroFrameScript.sml#L7)
- [abi_encoder_footprint_frame_zero_slice](abiEncoderZeroFrameScript.sml#L19)

### abiScratchArraySpine

- [abi_scratch_array_prepare_raw_transport](abiScratchArraySpineScript.sml#L11)

### abiScratchMemberAdapter

- [abi_scratch_spine_frame_after_address](abiScratchMemberAdapterScript.sml#L14)
- [abi_scratch_static_child_spine_reach](abiScratchMemberAdapterScript.sml#L33)
- [abi_scratch_dynamic_finish_raw_transport](abiScratchMemberAdapterScript.sml#L119)
- [abi_scratch_dynamic_prepare_raw_transport](abiScratchMemberAdapterScript.sml#L170)
- [abi_scratch_dynamic_child_spine_reach](abiScratchMemberAdapterScript.sml#L213)

### abiScratchMemberContract

- [abi_scratch_member_core_run](abiScratchMemberContractScript.sml#L33)
- [abi_scratch_member_child_run](abiScratchMemberContractScript.sml#L46)
- [abi_scratch_member_core_saved](abiScratchMemberContractScript.sml#L59)
- [abi_scratch_member_dynamic_run](abiScratchMemberContractScript.sml#L111)
- [abi_scratch_member_dynamic_saved](abiScratchMemberContractScript.sml#L123)
- [abi_scratch_member_dynamic_child_run](abiScratchMemberContractScript.sml#L138)
- [abi_scratch_member_dynamic_cursor_input](abiScratchMemberContractScript.sml#L151)

### abiScratchMemberInterpret

- [abi_scratch_member_static_input](abiScratchMemberInterpretScript.sml#L13)
- [abi_scratch_member_static_output](abiScratchMemberInterpretScript.sml#L49)
- [abi_scratch_member_dynamic_input](abiScratchMemberInterpretScript.sml#L99)
- [abi_scratch_member_dynamic_output_detailed](abiScratchMemberInterpretScript.sml#L153)
- [abi_scratch_member_dynamic_output](abiScratchMemberInterpretScript.sml#L237)

### abiScratchMembersCorrect

- [abi_scratch_members_correct_instance](abiScratchMembersCorrectScript.sml#L49) (local)

### abiScratchMembersEndpoint

- [abi_scratch_members_static_endpoint](abiScratchMembersEndpointScript.sml#L12)
- [abi_scratch_members_dynamic_endpoint](abiScratchMembersEndpointScript.sml#L71)

### abiScratchMembersEntry

- [abi_scratch_members_index_prepare](abiScratchMembersEntryScript.sml#L10)
- [abi_scratch_members_static_request](abiScratchMembersEntryScript.sml#L46)
- [abi_scratch_members_dynamic_request](abiScratchMembersEntryScript.sml#L74)
- [abi_scratch_members_static_exit](abiScratchMembersEntryScript.sml#L112)
- [abi_scratch_members_dynamic_exit](abiScratchMembersEntryScript.sml#L147)

### abiScratchMembersIndex

- [abi_scratch_members_index_initial](abiScratchMembersIndexScript.sml#L24)
- [abi_scratch_members_index_source](abiScratchMembersIndexScript.sml#L39)
- [abi_scratch_members_index_empty](abiScratchMembersIndexScript.sml#L54)
- [abi_scratch_members_origin_transport](abiScratchMembersIndexScript.sml#L73)
- [abi_scratch_members_index_advance](abiScratchMembersIndexScript.sml#L102)

### abiScratchMembersInterpret

- [abi_scratch_members_child_dispatch](abiScratchMembersInterpretScript.sml#L20)
- [abi_scratch_members_child_run](abiScratchMembersInterpretScript.sml#L33)
- [abi_scratch_members_entry_input](abiScratchMembersInterpretScript.sml#L71)
- [abi_scratch_members_entry_exit](abiScratchMembersInterpretScript.sml#L98)
- [abi_scratch_members_index_cons_shape](abiScratchMembersInterpretScript.sml#L128)
- [abi_scratch_members_layout_bound](abiScratchMembersInterpretScript.sml#L149) (local)
- [abi_scratch_members_entry_prepare](abiScratchMembersInterpretScript.sml#L160)
- [abi_scratch_members_empty_post](abiScratchMembersInterpretScript.sml#L196)
- [abi_scratch_members_generate](abiScratchMembersInterpretScript.sml#L215)
