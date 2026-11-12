(* Observation boundaries for replay with stale, unused temporary bindings. *)
Theory abiDecodePtrReentryObservations
Ancestors
  abiDecoderVarSequence abiDecoderVarExtend o1ContractCfgNorm
  ptrDiscipline contextCodegenRel codegenRel execEquivParamDefs
  venomState venomInst list

Theorem abi_decode_ptr_reentry_eval:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s ==>
  !op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule abi_decoder_vars_extend_inputs >>
  disch_then drule >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  Cases >> simp[eval_operand_def]
QED

Theorem abi_decode_ptr_reentry_frame:
  abi_decoder_vars_extend extras s t ==>
  s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx /\
  s.vs_fmp = t.vs_fmp /\ s.vs_call_entry_fmp = t.vs_call_entry_fmp
Proof
  strip_tac >> drule abi_decoder_vars_extend_restore >>
  disch_then (mp_tac o AP_TERM ``\u:venom_state.
    (u.vs_current_bb,u.vs_inst_idx,u.vs_fmp,u.vs_call_entry_fmp)``) >> simp[]
QED

Theorem abi_decode_ptr_reentry_read_ranges:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s ==>
  source_memory_read_ranges inst s = source_memory_read_ranges inst t
Proof
  strip_tac >> irule supply_read_ranges_cong >>
  metis_tac[abi_decode_ptr_reentry_eval]
QED

Theorem abi_decode_ptr_reentry_write_ranges:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s ==>
  source_memory_write_ranges inst s = source_memory_write_ranges inst t
Proof
  strip_tac >> irule supply_write_ranges_cong >>
  metis_tac[abi_decode_ptr_reentry_frame, abi_decode_ptr_reentry_eval]
QED

Theorem abi_decode_ptr_reentry_revert:
  abi_decoder_vars_extend extras s t ==>
  (in_revert_forward fn s <=> in_revert_forward fn t) /\
  (about_to_revert fn inst s <=> about_to_revert fn inst t)
Proof
  strip_tac >> drule abi_decode_ptr_reentry_frame >> strip_tac >>
  simp[in_revert_forward_def, about_to_revert_def, active_inst_def]
QED

Theorem abi_decode_ptr_reentry_new_site:
  abi_decoder_vars_extend extras s t /\ abi_decoder_vars_extend more u v ==>
  new_site_bytes s u = new_site_bytes t v
Proof
  strip_tac >>
  imp_res_tac abi_decoder_vars_extend_observations >>
  imp_res_tac abi_decode_ptr_reentry_frame >> simp[new_site_bytes_def]
QED

Theorem abi_decode_ptr_reentry_index:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras (s with vs_inst_idx := k) (t with vs_inst_idx := k)
Proof
  simp[abi_decoder_vars_extend_def, Excl "vsr_complete_mask_equality"] >>
  strip_tac >> conj_tac
QED
