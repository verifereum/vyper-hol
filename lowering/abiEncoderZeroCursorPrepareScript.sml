(* Actual zero-cursor allocation preserves a complete buffered source and protected scratch. *)
Theory abiEncoderZeroCursorPrepare
Ancestors
  abiEncoderComplexPrefixEffect abiEncoderComplexPrefixReach abiEncoderComplexPrefix
  abiEncoderBufferFrame abiEncoderChildInputs abiEncoderArrayMemory abiEncoderMembersDefs
  abiDecoderEffect abiDecoderAllocation abiDecoderReentry abiDecoderContract
  fragExec compileEnv emitHelperProps valueEncoding venomState words list arithmetic pred_set

Theorem abi_encoder_zero_cursor_prepare:
  abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (cursor_op,prepared) /\
  fn_has_code st prepared func /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  prepared.cs_next_id <= hi /\ hi <= last /\ prepared.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_encoder_buffer_pre ei at av prepared src dst sb source_cap d output_size b cap ready /\
    abi_encoder_cursor T cursor_op st.cs_next_id slot first st.cs_next_id prepared 0 ready /\
    abi_decode_frame slot 32 initial ready /\
    abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial ready /\
    ready.vs_current_bb = prepared.cs_current_bb /\ ready.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  drule_all abi_encoder_complex_prefix_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o List.last o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  `abi_decoder_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial ready` by
    (mp_tac (Q.INST [`infos` |-> `[]:(abi_enc_info # num # num # bool) list`, `dyn_ptr` |-> `cursor_op`,
      `site` |-> `st.cs_next_id`, `next` |-> `st.cs_next_var`,
      `outsz` |-> `output_size:num`, `actual` |-> `ready:venom_state`]
      abi_encoder_complex_prefix_effect) >>
     impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> asm_simp_tac bool_ss []) >>
  `abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap ready` by
    (drule_all abi_encoder_buffer_pre_effect >> asm_simp_tac bool_ss []) >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `abi_encoder_buffer_pre ei at av prepared src dst sb source_cap d output_size b cap ready` by
    (drule_all abi_encoder_buffer_pre_mono >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ ready`
    (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS) o
      PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  `abi_decoder_operand_live prepared.cs_next_var cursor_op` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  `abi_encoder_cursor T cursor_op st.cs_next_id slot first st.cs_next_id prepared 0 ready` by
    (asm_simp_tac (srw_ss()) [abi_encoder_cursor_def] >> decide_tac) >>
  qexistsl_tac [`ready`, `slot`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ZERO_CURSOR_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder zero cursor preparation not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderZeroCursorPrepare");
