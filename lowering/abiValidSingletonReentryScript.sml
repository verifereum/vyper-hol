Theory abiValidSingletonReentry
Ancestors
  abiDecoderSingletonSetup abiDecoderComplexGuard abiDecoderComplexHead abiDecoderGuard
  abiDecoderMemberSetup abiDecoderMemberCode abiDecoderDynamic abiDecoderAppend
  abiDecoderCounters abiDecoderTypedCompose abiDecoderContract abiDecoderReentry abiDecoderCode
  abiDecoderReentryPointer abiDecoderVarSequence abiEncoder fragExec compileEnv emitHelper
  emitHelperProps exprLoweringProps venomState venomExecSemantics venomInst words list rich_list
  arithmetic abiValidSingletonSetup abiDecoderVarExtend abiDecoderDynamicLoopSetup
  abiDecoderReservation abiEncoderSequence instIdxIndep pair

(* Code and live-register facts for the actual dynamic singleton prefix. *)
Theorem abi_valid_singleton_setup_trace:
  abi_decode_singleton_setup dst src opc hi st = (ops,ready) ==>
  ?middle. abi_decode_complex_head_guard src hi 32 st = ((),middle) /\
    abi_decode_member_setup dst src opc hi T 0 0 middle = (ops,ready)
Proof
  simp_tac bool_ss [abi_decode_singleton_setup_def, abi_decode_member_setup_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `abi_decode_complex_head_guard src hi 32 st = ((),middle)` >>
  qexists_tac `middle` >> asm_simp_tac bool_ss []
QED

Theorem abi_valid_singleton_setup_code:
  abi_decode_singleton_setup dst src opc hi st = (ops,ready) /\ abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st ready)
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  gvs[abi_decode_singleton_setup_def, abi_decode_complex_head_guard_def,
    abi_decode_le_guard_def, compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def]
QED

Theorem abi_valid_singleton_setup_live:
  abi_decode_singleton_setup dst src opc hi st = (ops,ready) ==>
  st.cs_next_var <= ready.cs_next_var /\
  abi_decoder_operand_live ready.cs_next_var (FST ops) /\
  abi_decoder_operand_live ready.cs_next_var (SND ops)
Proof
  strip_tac >> drule abi_valid_singleton_setup_trace >> strip_tac >>
  rename1 `abi_decode_complex_head_guard src hi 32 st = ((),head_st)` >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  asm_simp_tac bool_ss [] >> Cases_on `hi = Lit 0w` >> gvs[]
QED

Theorem abi_valid_dynamic_singleton_trace:
  compile_abi_decode_to_buf dst src opc hi (DecComplex T [(di,32,mem_sz)]) st = ((),final) /\
  dec_info_needs_offset di ==>
  ?ops middle. abi_decode_singleton_setup dst src opc hi st = (ops,middle) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) opc hi di middle = ((),final)
Proof
  strip_tac >> qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_dynamic_singleton_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_singleton_setup dst src opc hi st = (ops,middle)` >>
  qexistsl_tac [`ops`, `middle`] >> gvs[]
QED

Theorem abi_valid_singleton_setup_shape:
  abi_decode_singleton_setup dst src opc hi st = (ops,ready) /\ abi_decode_source_opcode opc ==>
  ready.cs_blocks = st.cs_blocks /\ ready.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts ready.cs_current_insts /\
  st.cs_next_id <= ready.cs_next_id /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode) (emitted_insts st ready)
Proof
  Cases_on `ops` >> strip_tac >> drule_all abi_decode_singleton_setup_shape >> simp[]
QED

Theorem abi_valid_singleton_child_code:
  abi_decode_singleton_setup dst src opc hi st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi di middle = ((),final) /\
  abi_decode_source_opcode opc /\ fn_has_code st final func ==>
  fn_has_code st middle func /\ fn_has_code middle final func /\
  cs_extends st middle /\ cs_extends middle final /\ middle.cs_blocks = st.cs_blocks /\
  st.cs_next_id <= middle.cs_next_id /\ middle.cs_next_id <= final.cs_next_id /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= final.cs_next_var /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (SND ops)
Proof
  strip_tac >> drule_all abi_valid_singleton_setup_shape >> strip_tac >>
  drule abi_valid_singleton_setup_live >> strip_tac >>
  `cs_extends st middle` by
    (irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  drule cs_extends_abi_decode >> strip_tac >>
  mp_tac (Q.SPECL [`st`, `middle`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  drule_all abi_decoder_to_buf_code >> simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

(* Re-enter the actual singleton prefix with an arbitrary decoded offset. *)
Theorem abi_valid_singleton_setup_reentry:
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),st') /\
  abi_valid_singleton_setup_pre st src dst opc hi sb d offset
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand child_src actual = SOME (n2w (sb + offset)) /\
    eval_operand child_dst actual = SOME (n2w d) /\
    abi_decoder_operand_live st'.cs_next_var child_src /\
    abi_decoder_operand_live st'.cs_next_var child_dst /\
    fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\ inst_extends st st'
Proof
  strip_tac >> drule_all abi_valid_singleton_setup_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  `abi_decode_source_opcode opc` by fs[abi_valid_singleton_setup_pre_def] >>
  drule_all abi_valid_singleton_setup_code >> strip_tac >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  drule abi_valid_singleton_setup_live >> simp_tac bool_ss [FST, SND] >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  `eval_operand child_src actual = SOME (n2w (sb + offset)) /\
   eval_operand child_dst actual = SOME (n2w d)` by
    metis_tac[abi_decoder_vars_extend_eval] >>
  qexists_tac `actual` >>
  asm_simp_tac (srw_ss()) [abi_decoder_address_frame_def, abi_decoder_prune_vars_def]
QED

Theorem abi_valid_singleton_setup_reach:
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),st') /\
  abi_valid_singleton_setup_pre st src dst opc hi sb d offset
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\ ~initial.vs_halted ==>
  ?actual. actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    eval_operand child_src actual = SOME (n2w (sb + offset)) /\
    eval_operand child_dst actual = SOME (n2w d) /\
    abi_decoder_operand_live st'.cs_next_var child_src /\
    abi_decoder_operand_live st'.cs_next_var child_dst /\
    fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_valid_singleton_setup_reentry >> strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_valid_singleton_setup_pre_def] >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial reached` >>
  qexists_tac `reached` >>
  gvs[abi_decoder_address_frame_def, eval_op_inst_idx, fresh_vars_wrt_def]
QED
