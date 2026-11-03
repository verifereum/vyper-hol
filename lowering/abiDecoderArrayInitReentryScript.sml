(* Repeated array initialization overwrites its own temporaries and reuses its site. *)
Theory abiDecoderArrayInitReentry
Ancestors
  abiDecoderArrayInitExec abiDecoderArrayLoopInit abiDecoderIndexInit abiDecoderArrayInit
  abiDecoderBytesBound abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderArrayHeader abiDecoderGuard
  abiEncoder abiDecoderGuards abiDecoderContract abiDecoderAllocation abiDecoderReentry
  abiDecoderReentryPointer abiDecoderReentryPointer abiDecoderVarSequence abiDecoderVarExtend
  abiDecoderFrame exprLoweringProps emitHelperProps emitHelper compileEnv context fragExec
  venomState venomInst finite_map words list rich_list arithmetic

Theorem abi_decoder_budget_prune[simp]:
  abi_decoder_budget first last b cap (abi_decoder_prune_vars next s) <=>
  abi_decoder_budget first last b cap s
Proof
  simp[abi_decoder_budget_def, abi_decoder_missing_def, abi_decoder_prune_vars_def]
QED

Theorem abi_decoder_pruned_operand_defined:
  eval_operand op (abi_decoder_prune_vars next initial) = SOME w ==>
  abi_decoder_operand_live next op /\ eval_operand op initial = SOME w
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_prune_vars_def,
       eval_operand_def, lookup_var_def, FLOOKUP_DRESTRICT] >> gvs[AllCaseEqs()]
QED

Theorem abi_decoder_footprint_prune_before[simp]:
  abi_decode_footprint_frame fp (abi_decoder_prune_vars next s) t <=>
  abi_decode_footprint_frame fp s t
Proof
  simp[abi_decode_footprint_frame_def, abi_decoder_prune_vars_def]
QED

Theorem abi_decoder_generated_var_live:
  (next:num) < limit ==>
  abi_decoder_operand_live limit (Var (STRING #"%" (toString next)))
Proof
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  rpt strip_tac >> simp[] >> decide_tac
QED

Theorem abi_decode_array_loop_index_live:
  abi_decode_array_loop_init dst src opc base_op hi maxn abi_sz st = (setup,loop_st) ==>
  abi_decoder_operand_live loop_st.cs_next_var (FST setup)
Proof
  strip_tac >> drule abi_decode_array_loop_init_trace >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >> gvs[] >>
  irule abi_decoder_generated_var_live >> simp[]
QED

Theorem abi_decoder_prune_load[simp]:
  abi_decode_load opc p (abi_decoder_prune_vars next s) = abi_decode_load opc p s /\
  mload addr (abi_decoder_prune_vars next s) = mload addr s
Proof
  simp[abi_decode_load_def, abi_decode_source_def, mload_def, abi_decoder_prune_vars_def]
QED

Theorem abi_decode_array_loop_init_site_bounds:
  abi_decode_array_loop_init dst src opc base_op hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc ==>
  st.cs_next_id <= loop_st.cs_next_id - 2 /\ loop_st.cs_next_id - 2 < loop_st.cs_next_id
Proof
  strip_tac >> drule abi_decode_array_loop_init_trace >> strip_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >> decide_tac
QED

Theorem abi_decode_init_prefix_reentry_code[local]:
  abi_decode_dynarray_position_prefix src opc base_op hi maxn abi_sz st = (addr,st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >> Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  gvs[abi_decode_dynarray_position_prefix_def, abi_decode_bytes_head_def,
      compile_abi_dec_addr_def, abi_decode_count_guard_def,
      abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      emitted_insts_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  gvs[DROP_LENGTH_APPEND, abi_decode_source_opcode_def,
      mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_init_header_reentry_code[local]:
  abi_decode_array_header dst addr opc st = (cnt,st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, abi_decode_source_opcode_def,
      mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_init_index_reentry_code[local]:
  abi_decode_index_init st = (ip,st') ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
  simp[abi_decode_index_init_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_array_loop_init_reentry_code:
  abi_decode_array_loop_init dst src opc base_op hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st loop_st)
Proof
  strip_tac >> drule abi_decode_array_loop_init_trace >> strip_tac >>
  drule_all abi_decode_init_prefix_reentry_code >> strip_tac >>
  drule_all abi_decode_init_header_reentry_code >> strip_tac >>
  drule abi_decode_init_index_reentry_code >> strip_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `emitted_insts st header_st = emitted_insts st guard_st ++ emitted_insts guard_st header_st` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `inst_extends st header_st` by metis_tac[inst_extends_trans] >>
  `emitted_insts st loop_st = emitted_insts st header_st ++ emitted_insts header_st loop_st` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >> simp[]
QED

Theorem abi_decode_array_loop_init_reentry:
  abi_decode_array_loop_init dst src opc base_op hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  eval_operand base_op initial = SOME (n2w B) /\
  abi_decode_load opc (n2w (B+sb):bytes32) initial = n2w n /\ n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  (d + 32 <= b \/ b + cap <= d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual slot. run_inst_seq (emitted_insts st loop_st) initial = OK actual /\
    eval_operand (FST setup) actual = SOME (n2w slot) /\
    eval_operand (SND setup) actual = SOME (n2w n) /\ mload slot actual = 0w /\
    mem_word_at d actual.vs_memory = n2w n /\ b <= slot /\ slot + 32 <= b + cap /\
    abi_decoder_budget first last b cap actual /\ fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    abi_decode_footprint_frame [(d,32);(b,cap)] initial actual /\
    abi_decode_footprint_frame [(d,32);(slot,32)] initial actual /\
    FLOOKUP actual.vs_allocas (loop_st.cs_next_id - 2) = SOME (slot,32) /\
    (!id. id <> loop_st.cs_next_id - 2 ==>
      FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    actual.vs_halted = initial.vs_halted /\ inst_extends st loop_st
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_reentry_code >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`]
    abi_decode_array_loop_init_sequence) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decoder_prune_fresh, abi_decoder_prune_eval] >>
  strip_tac >> rename1 `mload slot clean = 0w` >>
  `abi_decoder_vars_extend initial.vs_vars
    (abi_decoder_prune_vars st.cs_next_var initial) initial` by
    irule abi_decoder_prune_extension >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_prefix_vars_extend >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `abi_decoder_budget first last b cap actual` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  `eval_operand (FST setup) actual = SOME (n2w slot) /\
   eval_operand (SND setup) actual = SOME (n2w n)` by
    metis_tac[abi_decoder_vars_extend_eval] >>
  `actual.vs_halted = initial.vs_halted` by
    (mp_tac (Q.INST [`insts` |-> `emitted_insts st loop_st`,
       `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`]
       abi_decoder_sequence_halted) >> simp[]) >>
  `abi_decode_footprint_frame [(d,32);(b,cap)] initial actual` by
    (gvs[abi_decode_footprint_frame_def, abi_decoder_prune_vars_def] >> first_assum ACCEPT_TAC) >>
  `abi_decode_footprint_frame [(d,32);(slot,32)] initial actual` by
    (gvs[abi_decode_footprint_frame_def, abi_decoder_prune_vars_def] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`actual`, `slot`] >> gvs[mload_def, abi_decoder_prune_vars_def]
QED

Theorem abi_decode_array_loop_init_reentry_from_state:
  abi_decode_array_loop_init dst src opc base_op hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  eval_operand base_op initial = SOME (n2w B) /\
  abi_decode_load opc (n2w (B+sb):bytes32) initial = n2w n /\ n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  (d + 32 <= b \/ b + cap <= d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st loop_st (\s. s = initial)
    (abi_decoder_array_init_post setup st.cs_next_var limit_st (loop_st.cs_next_id - 2)
      first last b cap d n initial) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decode_array_loop_init_reentry >> strip_tac >>
  qexists_tac `actual` >> simp[] >>
  simp_tac bool_ss [abi_decoder_array_init_post_def] >> qexists_tac `slot` >> simp[]
QED
