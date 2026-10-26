(* Primitive child decoders may run repeatedly with stale local bindings.
   Their frame excludes scratch slots and their allocator state is unchanged. *)
Theory abiDecoderReentryPrimitive
Ancestors
  abiDecoderReentrySequence abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend
  abiDecoderPrimitive abiDecoderPrimitiveClamp abiDecoderClampedWord abiDecoderClamp
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderFrame
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper valueEncoding
  venomExecSemantics venomState venomInst fragExec instIdxIndep
  words list rich_list arithmetic

Theorem abi_decoder_word_reentry_code:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def,
      abi_decode_source_opcode_def]
QED

Theorem abi_decoder_typed_word_sequence_frame:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post tv v st' d 32 b cap s t /\ abi_decode_frame d 32 s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all abi_decoder_typed_primitive_word_sequence >> strip_tac >>
  drule abi_decoder_primitive_source >> strip_tac >>
  drule_all abi_decoder_primitive_clamp >> strip_tac >>
  `abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
   eval_operand dst s = SOME (n2w d) /\ fresh_vars_wrt st s /\ d < dimword (:256)` by
    (qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [abi_decoder_recursive_pre_def, abi_decoder_pre_def,
       abi_decoder_ranges_def] >> rpt strip_tac >> asm_simp_tac bool_ss [] >> decide_tac) >>
  drule_all abi_decoder_clamped_word_copied_window >> strip_tac >> gvs[]
QED

Theorem abi_decoder_primitive_reentry_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    abi_decode_frame d 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule_all abi_decoder_typed_word_sequence_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK actual` >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [abi_decoder_prune_vars_def]
QED

Theorem abi_decoder_primitive_reentry_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\actual. val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
      abi_decode_frame d 32 initial actual /\
      actual.vs_allocas = initial.vs_allocas /\
      actual.vs_alloca_next = initial.vs_alloca_next /\
      actual.vs_halted = initial.vs_halted) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_primitive_reentry_sequence >> strip_tac >>
  qexists_tac `actual` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED
