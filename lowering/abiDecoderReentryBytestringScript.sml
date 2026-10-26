(* Bytestring children execute with stale local SSA bindings under enclosing freshness. *)
Theory abiDecoderReentryBytestring
Ancestors
  abiDecoderBytesFrame abiDecoderBytestring abiDecoderBytesTyped abiDecoderString
  abiDecoderReentrySequence abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderFrame
  abiEncoder exprLowering emitHelperProps exprLoweringProps compileEnv valueEncoding
  vyperABI vyperTyping vyperValue contractABI
  venomExecSemantics venomState venomInst fragExec instIdxIndep words list rich_list arithmetic

Theorem abi_decoder_typed_bytestring_sequence_frame:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecBytestring n) av v
    st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post tv v st' d (type_memory_bytes ce ty) b cap s t /\
    abi_decode_frame d (type_memory_bytes ce ty) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_bytestring_cases >> disch_then (qspec_then `n` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >> gvs[Excl "enc_def"] >>
  qpat_assum `abi_decoder_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_pre_def]) >>
  Cases_on `av` >>
  gvs[abi_decoder_metadata_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    has_type_def, abi_to_vyper_def, AllCaseEqs(), Excl "enc_def"] >>
  fs[type_to_abi_dec_info_def] >>
  FIRST [drule_all abi_decoder_typed_bytes_sequence_frame >>
      simp[GSYM (cj 1 abi_decoder_bytes_copy_size)],
    drule_all abi_decoder_typed_string_sequence_frame >> simp[]]
QED

Theorem abi_decoder_bytestring_reentry_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecBytestring n) av v
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    abi_decode_frame d (type_memory_bytes ce ty) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule_all abi_decoder_typed_bytestring_sequence_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK actual` >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [abi_decoder_prune_vars_def]
QED

Theorem abi_decoder_bytestring_reentry_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecBytestring n) av v
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\actual. val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
        eval_operand op actual = SOME w) /\
      abi_decode_frame d (type_memory_bytes ce ty) initial actual /\
      actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
      actual.vs_halted = initial.vs_halted) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_bytestring_reentry_sequence >> strip_tac >>
  qexists_tac `actual` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx, Excl "enc_def"] >>
  first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_REENTRY_BYTESTRING_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI bytestring reentry not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderReentryBytestring");
