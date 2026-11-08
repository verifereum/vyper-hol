(* Safe arbitrary-calldata dynamic count guard and initialization adapters. *)
Theory calldataDynInit
Ancestors
  valueEncodingDefs loweringStateRelDefs actualAllocExec actualAllocCredit allocaFrontierBound unitTransformDefs
  fragExec memSafeRun contextCodegenRel codegenRel abiDecoderExecution
  calldataBytesLeaf calldataWordLeaf abiDecoderContract calldataChildFrame safeSequence fragExecMem
  abiDecoderGuards abiDecoderIndexInit abiDecoderArrayHeader abiDecoderReservation
  abiDecoderArrayLoopInit abiDecoderDynarrayPrefix abiDecoderDynarrayBound
  abiDecoderLoopEmit abiDecoderFrameCompose allocaBudgetProps
  emitHelperProps exprLoweringProps compileEnv emitHelper context
  valueEncodingProps venomExecSemantics venomMemProps venomState venomInst words arithmetic finite_map list rich_list

Theorem calldata_dynarray_prefix_opcodes:
  abi_decode_dynarray_prefix src CALLDATALOAD hi maxn abi_sz st = ((),st') ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (emitted_insts st st')
Proof
  strip_tac >> Cases_on `hi = Lit 0w` >>
  gvs[abi_decode_dynarray_prefix_def, abi_decode_count_guard_def,
      abi_decode_dynarray_end_guard_def, abi_decode_dynarray_end_def,
      abiDecoderGuardTheory.abi_decode_le_guard_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem calldata_array_header_opcodes:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (emitted_insts st st')
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_decode_index_init_opcodes:
  abi_decode_index_init st = (ip,st') ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (emitted_insts st st')
Proof
  simp[abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem calldata_count_guard_code_shape:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (emitted_insts st st')
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, IS_PREFIX_APPEND]
QED

Theorem calldata_count_guard_frag_mem:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src initial = SOME p /\ limit < dimword (:256) /\
  fresh_vars_wrt st initial ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. w2n (abi_decode_load CALLDATALOAD p initial) <= limit /\
      eval_operand count_op t = SOME (abi_decode_load CALLDATALOAD p initial) /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = initial.vs_memory /\
      t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section)
    (\r. ?u. r = Abort Revert_abort u)
Proof
  strip_tac >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule calldata_count_guard_code_shape >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >>
  fs[inst_extends_def] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_count_guard_instruction_safe >> simp[]) >>
  Cases_on `w2n (abi_decode_load CALLDATALOAD p initial) <= limit`
  >- (`abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
      `abi_decode_load CALLDATALOAD p initial =
        n2w (w2n (abi_decode_load CALLDATALOAD p initial))` by simp[] >>
      drule_all abi_decode_count_guard_sequence >> strip_tac >>
      disj1_tac >> qexists_tac `t` >>
      gvs[fresh_vars_wrt_def, instIdxIndepTheory.eval_op_inst_idx]) >>
  `limit < w2n (abi_decode_load CALLDATALOAD p initial)` by decide_tac >>
  drule_all calldata_count_guard_rejected_sequence >> strip_tac >>
  disj2_tac >> qexists_tac `t` >> simp[]
QED

Theorem calldata_index_init_instructions:
  abi_decode_index_init st = (ip,st') ==>
  ip = Var (STRING #"%" (toString st.cs_next_var)) /\
  emitted_insts st st' =
    [mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id+1) MSTORE [ip;Lit 0w] []]
Proof
  simp[abi_decode_index_init_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[DROP_LENGTH_APPEND]
QED

(* Reset is an actual store even when the ALLOCA site is reused. *)
Theorem calldata_index_init_after_alloca:
  abi_decode_index_init st = (ip,st') /\
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
  eval_operand ip allocated = SOME (n2w p) /\ p < dimword (:256) ==>
  run_inst_seq (emitted_insts st st') s = OK (mstore p 0w allocated) /\
  eval_operand ip (mstore p 0w allocated) = SOME (n2w p) /\
  mload p (mstore p 0w allocated) = 0w
Proof
  strip_tac >> drule calldata_index_init_instructions >> strip_tac >>
  simp[run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_def, w2n_n2w, mload_mstore_same,
       abi_decoder_operand_mstore] >>
  gvs[eval_operand_def]
QED

Theorem calldata_index_init_fresh_sequence:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w s.vs_alloca_next) /\
    mload s.vs_alloca_next t = 0w /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (s.vs_alloca_next,32) /\
    t.vs_alloca_next = s.vs_alloca_next+32 /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id)
Proof
  strip_tac >> drule calldata_index_init_instructions >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `MEM inst (fn_insts fn)` by
    (first_x_assum irule >> simp[Abbr `inst`]) >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id = st.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `FLOOKUP s.vs_allocas inst.inst_id = NONE` by simp[] >>
  drule_all actual_word_alloca_fresh_run >> strip_tac >>
  `eval_operand ip t = SOME (n2w s.vs_alloca_next)` by
    simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  `run_inst_seq (emitted_insts st st') s =
     OK (mstore s.vs_alloca_next 0w t) /\
   eval_operand ip (mstore s.vs_alloca_next 0w t) = SOME (n2w s.vs_alloca_next) /\
   mload s.vs_alloca_next (mstore s.vs_alloca_next 0w t) = 0w` by
    (irule calldata_index_init_after_alloca >>
     goal_assum (drule_at Any) >> gvs[Abbr `inst`]) >>
  qexists_tac `mstore s.vs_alloca_next 0w t` >>
  gvs[mstore_def, write_memory_with_expansion_def, FLOOKUP_UPDATE]
QED

Theorem calldata_index_init_reuse_sequence:
  abi_decode_index_init st = (ip,st') /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,32) /\ p < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule calldata_index_init_instructions >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id = st.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32)` by simp[] >>
  drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  `eval_operand ip t = SOME (n2w p)` by
    simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `run_inst_seq (emitted_insts st st') s = OK (mstore p 0w t) /\
   eval_operand ip (mstore p 0w t) = SOME (n2w p) /\
   mload p (mstore p 0w t) = 0w` by
    (irule calldata_index_init_after_alloca >>
     goal_assum (drule_at Any) >> gvs[Abbr `inst`]) >>
  qexists_tac `mstore p 0w t` >>
  gvs[mstore_def, write_memory_with_expansion_def]
QED

Theorem calldata_index_init_prefix_safe:
  abi_decode_index_init st = (ip,st') /\
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
  eval_operand ip allocated = SOME (n2w p) /\ p < dimword (:256) /\
  p+32 <= allocated.vs_alloca_next ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  strip_tac >> drule calldata_index_init_instructions >> strip_tac >>
  qpat_x_assum `emitted_insts st st' = _` SUBST1_TAC >>
  rpt strip_tac >> Cases_on `pre` >> gvs[run_inst_seq_def]
  >- simp[inst_mem_below_frontier_def,
        contextCodegenRelTheory.source_memory_read_ranges_def,
        codegenRelTheory.source_memory_write_ranges_def, mk_inst_def] >>
  Cases_on `t` >> gvs[run_inst_seq_def] >>
  simp[inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       mk_inst_def, eval_operand_def, w2n_n2w] >>
  gvs[eval_operand_def]
QED

Theorem calldata_index_init_frag_mem:
  abi_decode_index_init st = (ip,st') /\
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) initial = OK allocated /\
  eval_operand ip allocated = SOME (n2w p) /\ p < dimword (:256) /\
  p+32 <= allocated.vs_alloca_next ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. t = (mstore p 0w allocated with
      vs_inst_idx := LENGTH st'.cs_current_insts)) (K F)
Proof
  strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  drule abi_decode_index_init_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_index_init_prefix_safe) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> gvs[]) >>
  drule_all calldata_index_init_after_alloca >> strip_tac >>
  qexists_tac `mstore p 0w allocated` >> simp[]
QED

Theorem calldata_array_header_prefix_safe:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ d+32 <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  simp_tac bool_ss [abi_decode_array_header_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (cnt,c1)` >>
  rename1 `emit_void MSTORE [dst;cnt] c1 = ((),st')` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. !u. inst_mem_below_frontier i u) (emitted_insts st c1)` by
    (drule emitted_insts_emit_op >> simp[] >>
     simp[inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]) >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (`EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
        (emitted_insts st c1)` by
       (drule emitted_insts_emit_op >> simp[mk_inst_def,
          is_terminator_def, is_alloca_op_def]) >>
     drule_all abi_decode_sequence_allocation_frame >> simp[]) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `s1` >> asm_rewrite_tac[] >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >> simp[]) >>
  drule emitted_insts_emit_void >> simp[] >> strip_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL calldata_mstore_prefix_safe) >>
  qexists_tac `d` >> simp[] >> metis_tac[]
QED

Theorem calldata_array_header_frag_mem:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') /\
  eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  d+32 <= initial.vs_alloca_next /\ fresh_vars_wrt st initial ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD p initial) /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      abi_decode_frame d 32 initial t /\ fresh_vars_wrt st' t /\
      (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w))
    (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  `st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  drule calldata_array_header_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> fs[inst_extends_def] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_array_header_prefix_safe) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[]) >>
  gvs[fresh_vars_wrt_def, instIdxIndepTheory.eval_op_inst_idx,
      abi_decode_frame_def] >> metis_tac[]
QED

Theorem calldata_index_init_reuse_frag_mem:
  abi_decode_index_init st = (ip,st') /\
  FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32) /\
  p < dimword (:256) /\ p+32 <= initial.vs_alloca_next ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. t = (mstore p 0w (update_var
      (STRING #"%" (toString st.cs_next_var)) (n2w p) initial) with
      vs_inst_idx := LENGTH st'.cs_current_insts)) (K F)
Proof
  strip_tac >> irule calldata_index_init_frag_mem >>
  goal_assum (drule_at Any) >>
  drule calldata_index_init_instructions >> strip_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def,
    update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem calldata_index_init_fresh_frag_mem:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP initial.vs_allocas st.cs_next_id = NONE ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. t = (mstore initial.vs_alloca_next 0w
      (update_var (STRING #"%" (toString st.cs_next_var))
        (n2w initial.vs_alloca_next)
        (initial with <|vs_allocas := initial.vs_allocas |+
          (st.cs_next_id,(initial.vs_alloca_next,32));
          vs_alloca_next := initial.vs_alloca_next+32|>)) with
      vs_inst_idx := LENGTH st'.cs_current_insts)) (K F)
Proof
  strip_tac >> drule calldata_index_init_instructions >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `MEM inst (fn_insts fn)` by
    (first_x_assum irule >> simp[Abbr `inst`]) >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id = st.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `FLOOKUP initial.vs_allocas inst.inst_id = NONE` by simp[] >>
  drule_all actual_word_alloca_fresh_run >> strip_tac >>
  irule calldata_index_init_frag_mem >>
  gvs[Abbr `inst`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  decide_tac
QED

Theorem calldata_index_init_frame:
  abi_decode_index_init st = (ip,st') /\
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
  fresh_vars_wrt st s ==>
  fresh_vars_wrt st' (mstore p 0w allocated) /\
  (!op w. eval_operand op s = SOME w ==>
    eval_operand op (mstore p 0w allocated) = SOME w) /\
  abi_decode_frame p 32 s (mstore p 0w allocated) /\
  (!id. id <> st.cs_next_id ==>
    FLOOKUP (mstore p 0w allocated).vs_allocas id = FLOOKUP s.vs_allocas id)
Proof
  strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  `abi_decode_frame p 32 allocated (mstore p 0w allocated)` by
    irule abi_decode_mstore_frame >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  gvs[fresh_vars_wrt_def, update_var_def, mstore_def,
    write_memory_with_expansion_def, FDOM_FUPDATE, FLOOKUP_UPDATE,
    abi_decode_frame_def] >>
  (conj_tac
   >- (Cases_on `op` >>
       simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
       rpt strip_tac >> IF_CASES_TAC >> gvs[] >>
       fs[FLOOKUP_DEF] >>
       qpat_x_assum `!n. n >= st.cs_next_var ==> _`
         (qspec_then `st.cs_next_var` mp_tac) >> simp[]) >>
   first_assum MATCH_ACCEPT_TAC)
QED

(* State-only assembly: compiler trace equations never enter this proof. *)
Theorem calldata_init_frame_assemble:
  g.vs_memory = initial.vs_memory /\
  g.vs_call_ctx = initial.vs_call_ctx /\
  g.vs_data_section = initial.vs_data_section /\
  abi_decode_frame d 32 g h /\ abi_decode_frame p 32 h t /\
  mem_word_at d h.vs_memory = word /\
  (d+32 <= p \/ p+32 <= d) /\
  (!op w. eval_operand op initial = SOME w ==> eval_operand op g = SOME w) /\
  (!op w. eval_operand op g = SOME w ==> eval_operand op h = SOME w) /\
  (!op w. eval_operand op h = SOME w ==> eval_operand op t = SOME w) ==>
  mem_word_at d t.vs_memory = word /\
  (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
  t.vs_call_ctx = initial.vs_call_ctx /\
  t.vs_data_section = initial.vs_data_section /\
  (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n initial.vs_memory)
Proof
  strip_tac >>
  `mem_word_at d t.vs_memory = mem_word_at d h.vs_memory` by
    (irule abi_decode_frame_mem_word >> goal_assum (drule_at Any) >> simp[]) >>
  fs[abi_decode_frame_def] >>
  rpt strip_tac >>
  `mem_bytes_at a n t.vs_memory = mem_bytes_at a n h.vs_memory` by
    (qpat_x_assum `!p' k. _ ==> mem_bytes_at p' k t.vs_memory = _`
      irule >> decide_tac) >>
  `mem_bytes_at a n h.vs_memory = mem_bytes_at a n g.vs_memory` by
    (qpat_x_assum `!p' k. _ ==> mem_bytes_at p' k h.vs_memory = _`
      irule >> decide_tac) >> simp[]
QED

Theorem calldata_init_index_transport:
  eval_operand ip t = SOME pointerword /\ mload p t = 0w /\
  mem_word_at d t.vs_memory = word /\ eval_operand cnt t = SOME word /\
  fresh_vars_wrt st t /\
  (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
  t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
  (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n initial.vs_memory) /\
  (!id. id <> aid ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
  FLOOKUP t.vs_allocas aid = SOME (p,32) /\
  (if FLOOKUP initial.vs_allocas aid = NONE then
    t.vs_alloca_next = initial.vs_alloca_next+32 else
    t.vs_alloca_next = initial.vs_alloca_next) ==>
  eval_operand ip (t with vs_inst_idx := k) = SOME pointerword /\
  mload p (t with vs_inst_idx := k) = 0w /\
  mem_word_at d (t with vs_inst_idx := k).vs_memory = word /\
  eval_operand cnt (t with vs_inst_idx := k) = SOME word /\
  fresh_vars_wrt st (t with vs_inst_idx := k) /\
  (!op w. eval_operand op initial = SOME w ==>
    eval_operand op (t with vs_inst_idx := k) = SOME w) /\
  (t with vs_inst_idx := k).vs_call_ctx = initial.vs_call_ctx /\
  (t with vs_inst_idx := k).vs_data_section = initial.vs_data_section /\
  (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
    mem_bytes_at a n (t with vs_inst_idx := k).vs_memory =
    mem_bytes_at a n initial.vs_memory) /\
  (!id. id <> aid ==> FLOOKUP (t with vs_inst_idx := k).vs_allocas id =
    FLOOKUP initial.vs_allocas id) /\
  FLOOKUP (t with vs_inst_idx := k).vs_allocas aid = SOME (p,32) /\
  (if FLOOKUP initial.vs_allocas aid = NONE then
    (t with vs_inst_idx := k).vs_alloca_next = initial.vs_alloca_next+32 else
    (t with vs_inst_idx := k).vs_alloca_next = initial.vs_alloca_next)
Proof
  simp_tac (srw_ss()) [instIdxIndepTheory.eval_op_inst_idx,
    venomStateTheory.mload_def, fresh_vars_wrt_def] >>
  strip_tac >> first_assum MATCH_ACCEPT_TAC
QED

(* Integrated initialization.  The trace states name the actual counter site;
   they are compiler equations, not assumptions about an executed prefix. *)
Theorem calldata_array_loop_init_safe:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\ fresh_vars_wrt st initial /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
    p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) ==>
  frag_exec_mem ctx st loop_st (\s. s = initial)
    (\t. ?q. q = p /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      eval_operand ip t = SOME (n2w q) /\ mload q t = 0w /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD srcword initial /\
      eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD srcword initial) /\
      fresh_vars_wrt loop_st t /\
      (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= q \/ q+32 <= a) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n initial.vs_memory) /\
      (!id. id <> header_st.cs_next_id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (q,32) /\
      (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
         t.vs_alloca_next = initial.vs_alloca_next+32
       else t.vs_alloca_next = initial.vs_alloca_next))
    (\r. ?u. r = Abort Revert_abort u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `?cop. abi_decode_count_guard CALLDATALOAD src maxn st = (cop,guard_st)` by
    (qpat_x_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_dynarray_prefix_def, abi_decode_dynarray_end_guard_def,
          comp_bind_def, comp_return_def] >> pairarg_tac >> simp[] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `inst_extends st loop_st` by metis_tac[inst_extends_trans] >>
  `emitted_insts st loop_st = emitted_insts st guard_st ++
      emitted_insts guard_st header_st ++ emitted_insts header_st loop_st` by
    metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC] >>
  `isPREFIX st.cs_current_insts loop_st.cs_current_insts` by
    (qpat_x_assum `inst_extends st loop_st` mp_tac >>
     simp_tac bool_ss [inst_extends_def] >> strip_tac >>
     simp_tac bool_ss [IS_PREFIX_APPEND] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st loop_st)` by
    (asm_rewrite_tac[EVERY_APPEND] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
     (emitted_insts st loop_st)` by
    (imp_res_tac calldata_dynarray_prefix_opcodes >>
     imp_res_tac calldata_array_header_opcodes >>
     imp_res_tac abi_decode_index_init_opcodes >>
     asm_rewrite_tac[EVERY_APPEND]) >>
  reverse (Cases_on `w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn`)
  >- suspend "reject" >>
  `abi_decode_load CALLDATALOAD srcword initial =
     n2w (w2n (abi_decode_load CALLDATALOAD srcword initial))` by simp[] >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  qpat_x_assum `abi_decode_load CALLDATALOAD srcword initial = n2w _` kall_tac >>
  rename1 `run_inst_seq (emitted_insts st guard_st) initial = OK g` >>
  `g.vs_allocas = initial.vs_allocas /\ g.vs_alloca_next = initial.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >>
     goal_assum (drule_at Any) >> fs[EVERY_MEM]) >>
  `eval_operand src g = SOME srcword /\ eval_operand dst g = SOME (n2w d)` by
    metis_tac[] >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts guard_st header_st) g = OK h` >>
  `h.vs_allocas = initial.vs_allocas /\ h.vs_alloca_next = initial.vs_alloca_next` by
    (`h.vs_allocas = g.vs_allocas /\ h.vs_alloca_next = g.vs_alloca_next` by
       (irule abi_decode_sequence_allocation_frame >>
        goal_assum (drule_at Any) >> fs[EVERY_MEM]) >> simp[]) >>
  `?allocated. step_inst_base (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString header_st.cs_next_var)]) h = OK allocated /\
     eval_operand ip allocated = SOME (n2w p) /\ p < dimword (:256) /\
     p+32 <= allocated.vs_alloca_next /\
     FLOOKUP allocated.vs_allocas header_st.cs_next_id = SOME (p,32) /\
     (!id. id <> header_st.cs_next_id ==>
       FLOOKUP allocated.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
     (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
        allocated.vs_alloca_next = initial.vs_alloca_next+32
      else allocated.vs_alloca_next = initial.vs_alloca_next)` by
    suspend "allocation" >>
  drule_all calldata_index_init_after_alloca >> strip_tac >>
  drule_all calldata_index_init_frame >>
  disch_then (qspec_then `p` strip_assume_tac) >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> asm_rewrite_tac[] >>
  simp_tac bool_ss [] >>
  reverse conj_tac
  >- suspend "execution" >>
  suspend "safety"
QED

Resume calldata_array_loop_init_safe[execution]:
  disj1_tac >> qexists_tac `mstore p 0w allocated` >>
  `run_inst_seq (emitted_insts st guard_st ++
     emitted_insts guard_st header_st ++ emitted_insts header_st loop_st)
     initial = OK (mstore p 0w allocated)` by
    (qpat_assum `run_inst_seq _ initial = OK g` mp_tac >>
     qpat_assum `run_inst_seq _ g = OK h` mp_tac >>
     qpat_assum `run_inst_seq _ h = OK (mstore p 0w allocated)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[run_inst_seq_append]) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  irule calldata_init_index_transport >>
  SUBGOAL_THEN ``d+32 <= p \/ p+32 <= d`` assume_tac >- decide_tac >>
  `abi_decode_load CALLDATALOAD srcword g =
     abi_decode_load CALLDATALOAD srcword initial` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  drule_all calldata_init_frame_assemble >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand cnt (mstore p 0w allocated) =
     SOME (abi_decode_load CALLDATALOAD srcword initial)` by metis_tac[] >>
  `(mstore p 0w allocated).vs_allocas = allocated.vs_allocas /\
   (mstore p 0w allocated).vs_alloca_next = allocated.vs_alloca_next` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  qpat_x_assum `header_st.cs_next_var = _`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_x_assum `header_st.cs_next_id = _`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_x_assum `ip = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  asm_rewrite_tac[]
QED

Resume calldata_array_loop_init_safe[safety]:
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `g` >> asm_rewrite_tac[] >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_count_guard_instruction_safe >> simp[]) >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `h` >> asm_rewrite_tac[] >> conj_tac
  >- (`d+32 <= g.vs_alloca_next` by (asm_rewrite_tac[] >> decide_tac) >>
      ho_match_mp_tac (GEN_ALL calldata_array_header_prefix_safe) >>
      goal_assum (drule_at (Pos hd)) >>
      qexistsl_tac [`srcword`, `d`] >> asm_rewrite_tac[]) >>
  ho_match_mp_tac (GEN_ALL calldata_index_init_prefix_safe) >>
  goal_assum (drule_at (Pos hd)) >> goal_assum (drule_at (Pos hd)) >>
  qexists_tac `p` >> asm_rewrite_tac[]
QED

Resume calldata_array_loop_init_safe[allocation]:
  qabbrev_tac `inst = mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString header_st.cs_next_var)]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString header_st.cs_next_var)] /\
   inst.inst_id = header_st.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `MEM inst (fn_insts fn)` by
    (first_x_assum irule >> drule calldata_index_init_instructions >> simp[Abbr `inst`]) >>
  `alloca_frontier_inv ctx fn site h` by
    (fs[alloca_frontier_inv_def, remaining_alloca_budget_def]) >>
  qpat_x_assum `(_ /\ p = _) \/ _` strip_assume_tac
  >- (`FLOOKUP h.vs_allocas inst.inst_id = NONE` by metis_tac[] >>
      drule_all actual_word_alloca_fresh_run >> strip_tac >>
      qexists_tac `t` >>
      gvs[Abbr `inst`, update_var_def, eval_operand_def, lookup_var_def,
          FLOOKUP_UPDATE] >> decide_tac) >>
  `FLOOKUP h.vs_allocas inst.inst_id = SOME (p,32)` by metis_tac[] >>
  drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >> qexists_tac `t` >>
  gvs[Abbr `inst`, update_var_def, eval_operand_def, lookup_var_def,
      FLOOKUP_UPDATE]
QED

Resume calldata_array_loop_init_safe[reject]:
  `cs_extends st guard_st /\ cs_extends guard_st loop_st` by
    (conj_tac >> irule cs_extends_same_block >>
     simp[] >> metis_tac[inst_extends_def, IS_PREFIX_APPEND,
                        inst_extends_trans]) >>
  irule frag_exec_mem_exit_prefix >> qexists_tac `guard_st` >>
  asm_rewrite_tac[] >>
  drule_all calldata_count_guard_frag_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (fn th => irule frag_exec_mem_conseq >> irule_at Any th) >>
  simp[] >> metis_tac[]
QED

Finalise calldata_array_loop_init_safe

(* The initial loop edge transfers both execution and the safety check. *)
Theorem calldata_loop_entry_safe_transfer:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr fn.fn_blocks = SOME hb /\
  phi_prefix_length hb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted ==>
  !fuel r. run_from fuel ctx fn (jump_to hdr s) = r /\
    (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn (jump_to hdr s) ==>
       mem_safe_run fuel' ctx fn s)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> qexists_tac `SUC fuel` >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst id JMP [Label hdr] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `step_inst_base (mk_inst id JMP [Label hdr] []) s =
     OK (jump_to hdr s)` by
    simp[Once step_inst_base_def, mk_inst_def, jump_to_def] >>
  conj_tac
  >- (`is_terminator (mk_inst id JMP [Label hdr] []).inst_opcode /\
        (mk_inst id JMP [Label hdr] []).inst_opcode <> INVOKE` by
        simp[mk_inst_def, is_terminator_def] >>
      drule_all run_from_jump >> simp[]) >>
  strip_tac >>
  `eval_phis (jump_to hdr s) hb.bb_instructions = OK (jump_to hdr s)` by
    (Cases_on `hb.bb_instructions` >>
     gvs[phi_prefix_length_def, eval_phis_def] >>
     Cases_on `h.inst_opcode = PHI` >> gvs[]) >>
  `mem_safe_blocks (SUC fuel) ctx fn (jump_to hdr s)` by
    (`lookup_block (jump_to hdr s).vs_current_bb fn.fn_blocks = SOME hb` by
       simp[jump_to_def] >>
     drule_all mem_safe_blocks_run >>
     disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
     `jump_to hdr s with vs_inst_idx := 0 = jump_to hdr s` by
       simp[jump_to_def] >> asm_rewrite_tac[]) >>
  `step_inst (SUC fuel) ctx (mk_inst id JMP [Label hdr] []) s =
     OK (jump_to hdr s)` by
    (simp[step_inst_non_invoke] >>
     simp[mk_inst_def, Once step_inst_base_def, jump_to_def]) >>
  `exec_block (SUC fuel) ctx bb s = OK (jump_to hdr s)` by
    (pure_once_rewrite_tac[exec_block_def] >>
     asm_rewrite_tac[] >> simp[jump_to_def, mk_inst_def, is_terminator_def]) >>
  simp_tac pure_ss [mem_safe_run_def] >>
  asm_simp_tac (srw_ss()) [] >>
  pure_once_rewrite_tac[mem_safe_block_def] >>
  asm_simp_tac (srw_ss()) [] >>
  simp[mem_safe_step_non_invoke, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

Theorem calldata_loop_prefix_entry_code:
  !ip src start hdr body exit_lbl end_st fn.
  abi_decode_loop_prefix ip src CALLDATALOAD start = ((hdr,body,exit_lbl),end_st) /\
  fn_has_code start end_st fn ==>
  ?bb hb.
    lookup_block start.cs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = start.cs_current_insts ++
      [mk_inst start.cs_next_id JMP [Label hdr] []] /\
    lookup_block hdr fn.fn_blocks = SOME hb /\
    phi_prefix_length hb.bb_instructions = 0
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def, emitted_blocks_def,
       abi_decode_loop_prefix_state_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >>
  simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem calldata_loop_prefix_entry_safe:
  !ip src start hdr body exit_lbl end_st fn s ctx.
  abi_decode_loop_prefix ip src CALLDATALOAD start = ((hdr,body,exit_lbl),end_st) /\
  fn_has_code start end_st fn /\
  s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\ ~s.vs_halted ==>
  !fuel r. run_from fuel ctx fn (jump_to hdr s) = r /\
    (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn (jump_to hdr s) ==>
       mem_safe_run fuel' ctx fn s)
Proof
  rpt gen_tac >> strip_tac >> drule_all calldata_loop_prefix_entry_code >> strip_tac >>
  ho_match_mp_tac (GEN_ALL calldata_loop_entry_safe_transfer) >>
  metis_tac[]
QED

(* Retain the complete initialization payload while crossing the emitted edge. *)
Theorem calldata_init_to_header_safe:
  !ctx st loop_st P Q R ip src hdr body exit_lbl end_st fn s.
  frag_exec_mem ctx st loop_st P Q R /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st =
    ((hdr,body,exit_lbl),end_st) /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st end_st fn /\
  P s /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?t. Q t /\ ~t.vs_halted /\
    (jump_to hdr t).vs_current_bb = hdr /\
    (jump_to hdr t).vs_inst_idx = 0 /\
    !fuel r. run_from fuel ctx fn (jump_to hdr t) = r /\
      (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn (jump_to hdr t) ==>
         mem_safe_run fuel' ctx fn s)) \/
  ?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r /\
    mem_safe_run fuel ctx fn s
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [frag_exec_mem_def] >>
  disch_then (qspecl_then [`fn`, `s`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac
  >- (disj1_tac >> qexists_tac `s'` >>
      simp_tac (srw_ss()) [jump_to_def] >> asm_rewrite_tac[] >>
      rpt gen_tac >> strip_tac >>
      drule calldata_loop_prefix_entry_safe >>
      disch_then (qspecl_then [`fn`, `s'`, `ctx`, `fuel`] mp_tac) >>
      simp[jump_to_def] >> strip_tac >>
      qpat_x_assum `!fuel. _` (qspec_then `fuel'` mp_tac) >>
      (impl_tac >- metis_tac[]) >> strip_tac >>
      qexists_tac `fuel''` >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED
