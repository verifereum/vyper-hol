(* Actual noncanonical Bytes/String execution closes the recursive child API. *)
Theory abiDecoderValidBytesCorrect
Ancestors
  abiDecoderValidContract abiDecoderValidBytesInput abiValidBytesReentry
  abiDecoderValidBytes abiDecoderBytesTyped abiDecoderBytes abiDecoderCorrectWord
  abiDecoderEffect abiDecoderContract abiDecoderTypedContract abiDecoderReentry abiDecoderTypedCompose
  abiDecoderLoop abiDecoderFrame abiEncoderSequenceReach abiEncoder
  fragExec instIdxIndep compileEnv emitHelperProps valueEncoding
  vyperABI vyperValue venomState venomExecSemantics words list

Theorem abi_decoder_valid_bytes_reach:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_valid_bytes_pre n at bs payload st src dst opc hi sb d
    (abi_decoder_prune_vars st.cs_next_var initial) /\ fn_has_code st st' func /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d actual.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d actual.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_decoder_valid_bytes_reentry >> strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_valid_bytes_pre_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule abi_decoder_inst_extends_prefix >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial reached` >> qexists_tac `reached` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_valid_pre_output_separated:
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst opc hi sb d b cap initial ==>
  d + type_memory_bytes ce ty <= b \/ b + cap <= d
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def, abi_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_valid_correct_bytestring:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) ==>
  abi_decoder_valid_correct ce env sf ty tv
Proof
  disch_then assume_tac >> simp_tac bool_ss [abi_decoder_valid_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_bytes_input >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_decoder_valid_bytes_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `val_in_memory tv v d actual.vs_memory` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  drule abi_decoder_valid_pre_output_separated >> disch_then assume_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`, `next` |-> `start.cs_next_var`,
    `sz` |-> `type_memory_bytes ce ty`] abi_decoder_scratch_free_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >>
  qpat_assum `type_memory_bytes ce ty = abi_decode_bytes_copy_size n`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_BYTES_CORRECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid recursive bytes decoder not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidBytesCorrect");
