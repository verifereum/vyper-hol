Theory abiEncoderArrayContext
Ancestors
  abiEncoderArrayPhases abiEncoderArrayCode abiDecoderIndexInit abiDecoderLoopEmit abiEncoder
  compileEnv emitHelper list abiDecoderContract context fragExec emitHelperProps
  exprLoweringProps venomInst words rich_list arithmetic abiEncoderArrayPhaseAppend
  abiEncoderAppend abiEncoderCounters abiDecoderReentry

(* Extract the actual initialization, header, body, backedge and exit compiler states. *)
Theorem abi_encode_array_static_loop_trace:
  compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) ==>
  ?ip owner_st labels body_st idx body_end exit_st.
    abi_decode_index_init start = (ip,owner_st) /\
    abi_encode_array_header ip count_op owner_st = (labels,body_st) /\
    abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
    abi_decode_loop_suffix ip idx (FST labels) (SND (SND labels)) body_end = ((),exit_st) /\
    abi_encode_array_static_exit src asz exit_st = (out,final)
Proof
  simp_tac bool_ss [abi_encode_array_static_loop_phases, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_index_init start = (ip,owner_st)` >>
  rename1 `abi_encode_array_header _ _ owner_st = (labels,body_st)` >>
  rename1 `abi_encode_array_static_body _ _ _ _ _ _ body_st = (idx,body_end)` >>
  rename1 `abi_decode_loop_suffix _ _ _ _ body_end = (ignored,exit_st)` >>
  Cases_on `ignored:unit` >>
  qexistsl_tac [`ip`, `owner_st`, `labels`, `body_st`, `idx`, `body_end`, `exit_st`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_dynamic_loop_trace:
  compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final) ==>
  ?ptrs owner_st labels body_st idx body_end exit_st.
    abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\
    abi_encode_array_header (FST ptrs) count_op owner_st = (labels,body_st) /\
    abi_encode_array_dynamic_body (FST ptrs) (SND ptrs) src dst ei asz msz body_st = (idx,body_end) /\
    abi_decode_loop_suffix (FST ptrs) idx (FST labels) (SND (SND labels)) body_end = ((),exit_st) /\
    abi_encode_array_dynamic_exit src (SND ptrs) exit_st = (out,final)
Proof
  simp_tac bool_ss [abi_encode_array_dynamic_loop_phases, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_encode_array_dynamic_init _ _ start = (ptrs,owner_st)` >>
  rename1 `abi_encode_array_header _ _ owner_st = (labels,body_st)` >>
  rename1 `abi_encode_array_dynamic_body _ _ _ _ _ _ _ body_st = (idx,body_end)` >>
  rename1 `abi_decode_loop_suffix _ _ _ _ body_end = (ignored,exit_st)` >>
  Cases_on `ignored:unit` >>
  qexistsl_tac [`ptrs`, `owner_st`, `labels`, `body_st`, `idx`, `body_end`, `exit_st`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_trace:
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz dyn) start = (out,final) ==>
  ?ops loop_st size_op loop_end.
    abi_encode_array_prefix src dst start = (ops,loop_st) /\
    (if dyn then compile_abi_encode_dyn_loop dst src ei asz msz (SND ops) loop_st = (size_op,loop_end)
      else compile_abi_encode_dyn_static_loop dst src ei asz msz (SND ops) loop_st = (size_op,loop_end)) /\
    abi_encode_array_finish (FST ops) size_op loop_end = (out,final)
Proof
  simp_tac bool_ss [abi_encode_array_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_encode_array_prefix _ _ start = (ops,loop_st)` >>
  rename1 `abi_encode_array_finish (FST ops) size_op loop_end = (out,final)` >>
  qexistsl_tac [`size_op`, `loop_end`] >> Cases_on `dyn` >> gvs[]
QED

(* Exact counters and output operands for actual straight-line array phases. *)
Theorem abi_encode_array_dynamic_init_shape:
  abi_encode_array_dynamic_init count_op asz st = (ptrs,owner_st) ==>
  ptrs = (Var (STRING #"%" (toString st.cs_next_var)),
    Var (STRING #"%" (toString (st.cs_next_var+1)))) /\
  owner_st.cs_next_var = st.cs_next_var+3 /\ owner_st.cs_next_id = st.cs_next_id+5 /\
  owner_st.cs_blocks = st.cs_blocks /\ owner_st.cs_current_bb = st.cs_current_bb /\
  inst_extends st owner_st /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st owner_st)
Proof
  simp[abi_encode_array_dynamic_init_def, abi_decode_index_init_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem abi_encode_array_prefix_shape:
  abi_encode_array_prefix src dst st = (ops,loop_st) ==>
  ops = (Var (STRING #"%" (toString st.cs_next_var)),
    Var (STRING #"%" (toString (st.cs_next_var+1)))) /\
  loop_st.cs_next_var = st.cs_next_var+2 /\ loop_st.cs_next_id = st.cs_next_id+4 /\
  loop_st.cs_blocks = st.cs_blocks /\ loop_st.cs_current_bb = st.cs_current_bb /\
  inst_extends st loop_st /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st loop_st)
Proof
  simp[abi_encode_array_prefix_def, abi_decode_index_init_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem abi_encode_array_finish_shape:
  abi_encode_array_finish parent_ptr size_op st = (out,final) ==>
  out = Var (STRING #"%" (toString (st.cs_next_var+2))) /\
  final.cs_next_var = st.cs_next_var+3 /\ final.cs_next_id = st.cs_next_id+4 /\
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)
Proof
  simp[abi_encode_array_finish_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem abi_encode_array_exit_shape:
  (abi_encode_array_static_exit src asz st = (out,final) ==>
    out = Var (STRING #"%" (toString (st.cs_next_var+2))) /\
    final.cs_next_var = st.cs_next_var+3 /\ final.cs_next_id = st.cs_next_id+3 /\
    final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\ inst_extends st final /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)) /\
  (abi_encode_array_dynamic_exit src dyn_ptr st = (out,final) ==>
    out = Var (STRING #"%" (toString (st.cs_next_var+2))) /\
    final.cs_next_var = st.cs_next_var+3 /\ final.cs_next_id = st.cs_next_id+3 /\
    final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\ inst_extends st final /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final))
Proof
  conj_tac >> simp[abi_encode_array_static_exit_def, abi_encode_array_dynamic_exit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

(* Actual outer array phases have containing code, monotone counters and a live loop result. *)
Theorem abi_encode_array_loop_result_live:
  (compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) ==>
    abi_decoder_operand_live final.cs_next_var out) /\
  (compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final) ==>
    abi_decoder_operand_live final.cs_next_var out)
Proof
  conj_tac >> strip_tac >>
  FIRST [drule abi_encode_array_static_loop_trace, drule abi_encode_array_dynamic_loop_trace] >> strip_tac >>
  FIRST [qpat_x_assum `abi_encode_array_static_exit _ _ _ = _` mp_tac,
    qpat_x_assum `abi_encode_array_dynamic_exit _ _ _ = _` mp_tac] >>
  simp_tac bool_ss [abi_encode_array_static_exit_def, abi_encode_array_dynamic_exit_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  qpat_assum `emit_op ADD _ _ = (out,final)`
    (mp_tac o MATCH_MP abi_decoder_operand_live_emit) >> simp[]
QED

Theorem abi_encode_array_loop_bounds:
  (if active then compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final)
    else compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final)) ==>
  cs_extends start final /\ start.cs_next_var <= final.cs_next_var /\
  start.cs_next_id <= final.cs_next_id /\ abi_decoder_operand_live final.cs_next_var out
Proof
  strip_tac >> qabbrev_tac `action = if active then compile_abi_encode_dyn_loop dst src ei asz msz count_op
    else compile_abi_encode_dyn_static_loop dst src ei asz msz count_op` >>
  `action start = (out,final)` by (Cases_on `active` >> gvs[Abbr`action`]) >>
  `cs_appends action /\ abi_encoder_counters_mono action` by
    (Cases_on `active` >> simp[Abbr`action`, cj 4 cs_appends_abi_encode_mutual,
      cs_appends_abi_encode_static_loop, cj 4 abi_encoder_counters_mono_mutual,
      abi_encoder_counters_mono_static_loop]) >>
  drule_all abi_encoder_appends_result >> strip_tac >>
  qpat_assum `abi_encoder_counters_mono action`
    (qspec_then `start` mp_tac o PURE_REWRITE_RULE [abi_encoder_counters_mono_def]) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  Cases_on `active` >> full_simp_tac bool_ss [COND_CLAUSES, Abbr`action`] >>
  FIRST [drule (cj 1 abi_encode_array_loop_result_live), drule (cj 2 abi_encode_array_loop_result_live)] >> simp[]
QED

Theorem abi_encode_array_context:
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz active) start = (out,final) /\
  fn_has_code start final func ==>
  ?ops loop_st size_op loop_end.
    abi_encode_array_prefix src dst start = (ops,loop_st) /\
    (if active then compile_abi_encode_dyn_loop dst src ei asz msz (SND ops) loop_st = (size_op,loop_end)
      else compile_abi_encode_dyn_static_loop dst src ei asz msz (SND ops) loop_st = (size_op,loop_end)) /\
    abi_encode_array_finish (FST ops) size_op loop_end = (out,final) /\
    fn_has_code start loop_st func /\ fn_has_code loop_st loop_end func /\ fn_has_code loop_end final func /\
    loop_st.cs_next_var = start.cs_next_var+2 /\ loop_st.cs_next_id = start.cs_next_id+4 /\
    loop_st.cs_next_var <= loop_end.cs_next_var /\ loop_st.cs_next_id <= loop_end.cs_next_id /\
    final.cs_next_var = loop_end.cs_next_var+3 /\ final.cs_next_id = loop_end.cs_next_id+4 /\
    abi_decoder_operand_live loop_end.cs_next_var size_op
Proof
  strip_tac >> drule abi_encode_array_trace >> strip_tac >>
  drule abi_encode_array_prefix_shape >> strip_tac >> drule abi_encode_array_finish_shape >> strip_tac >>
  drule abi_encode_array_loop_bounds >> strip_tac >>
  `cs_extends start loop_st` by
    (irule cs_extends_same_block >> fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends loop_end final` by
    (irule cs_extends_same_block >> fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends loop_st final` by
    (irule cs_extends_trans >> qexists_tac `loop_end` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`start`, `loop_st`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`loop_st`, `loop_end`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`ops`, `loop_st`, `size_op`, `loop_end`] >> asm_simp_tac bool_ss []
QED
