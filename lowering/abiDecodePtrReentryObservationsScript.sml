(* The extra variable bindings do not affect the decoder's live inputs. *)
Theory abiDecodePtrReentryObservations
Ancestors
  abiDecoderVarSequence abiDecoderVarExtend o1ContractCfgNorm
  abiDecodePtrMemberFrame abiDecoderReentry bodyPtrDefs
  ptrDiscipline contextCodegenRel venomState venomInst list

Theorem abi_decode_ptr_reentry_eval:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s ==>
  !op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule abi_decoder_vars_extend_inputs >> disch_then drule >> strip_tac >>
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

Theorem abi_decode_ptr_prune_covers:
  abi_decoder_operand_live next (Var p) ==>
  (ptr_covers G tn p (abi_decoder_prune_vars next s) sz <=>
   ptr_covers G tn p s sz)
Proof
  strip_tac >>
  drule abi_decoder_prune_eval >> simp[eval_operand_def, ptr_covers_def]
QED

Theorem abi_decode_ptr_window_prune:
  abi_decoder_operand_live next (Var p) ==>
  (abi_decode_ptr_window G tn (abi_decoder_prune_vars next s) p b n <=>
   abi_decode_ptr_window G tn s p b n)
Proof
  strip_tac >> drule abi_decoder_prune_eval >>
  simp[eval_operand_def, abi_decode_ptr_window_def, abi_decode_ptr_prune_covers,
       abi_decoder_prune_vars_def]
QED
