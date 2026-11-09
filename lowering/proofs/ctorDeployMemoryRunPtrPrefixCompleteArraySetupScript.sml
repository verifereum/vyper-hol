(* Shifted, same-witness array preheader boundaries for Entry. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteArraySetup
Ancestors
  ctorDeployMemoryRunPtrPrefixCompleteArrayRun
  ctorDeployLoweringEntryCompletePrefix ctorDeployLoweringEntryArrayOps
  ctorDeployMemoryRunPtrPrefixLoopSetup ctorDeployMemoryRunPtrPrefixLoopSlot
  ctorDeployMemoryFrontier ctorDeployLoweringEntryArrayFrame
  ctorAbiActualArrayInvariant ctorAbiActualAlloc
  abiDecoderArrayLoopInit abiDecoderIndexInit abiDecoderDynamicLoopSetup
  abiDecoderArrayHeader abiDecoderReservation
  abiDecoderReentry abiDecoderContract abiDecoderVarSequence
  venomState venomExecSemantics venomMemDefs venomInst
  compileEnv ptrSafeRun ptrDiscipline finite_map words arithmetic list pred_set
  ctorAbiActualArrayPrepare ctorDeployLoweringEntryCompleteScalar
  ctorDeployLoweringEntryRegistration
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderGuards emitHelper emitHelperProps
  exprLowering fragExec instIdxIndep rich_list exprLoweringProps abiDecoderLoop
  abiEncoderRegisteredEffect ctorAbiActualFrame ctorAbiActualObservations fragGasSeqAbort
  abiDecoderRecursiveLoopContext abiDecoderTypedContract abiEncoderZeroFrame venomWf

val Ok = ``\k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s.
    prefix <= LENGTH vs /\ cursor <= LENGTH vs /\
    elems_in_memory (TAKE prefix vs) (d+32) tv s.vs_memory /\
    mload d s = n2w (LENGTH vs) /\
    FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\ mload slot s = n2w cursor /\
    alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
    ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
    fresh_vars_wrt limit_st s /\ s.vs_data_section = base.vs_data_section /\
    s.vs_call_ctx = base.vs_call_ctx /\ s.vs_labels = base.vs_labels /\
    (!x w. abi_decoder_older_vars next x /\ lookup_var x base = SOME w ==>
      lookup_var x s = SOME w) /\
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s /\
    s.vs_gas_readings = base.vs_gas_readings /\ s.vs_code = base.vs_code``;

Theorem prefix_complete_array_index_pair:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts func)) /\
  st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ mload d s = n2w (LENGTH vs) /\
  st.cs_next_var < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME
    (mk_inst st.cs_next_id ALLOCA [Lit 32w] [iv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (st.cs_next_id+1) MSTORE [Var iv;Lit 0w] []) /\
  ip = Var iv ==>
  ?t p H qt.
    run_inst_seq (emitted_insts st st') s = OK t /\
    (^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t /\
    FLOOKUP H iv = SOME (p,32) /\
    eval_operand ip t = SOME (n2w p) /\ op_taint qt ip = {} /\
    DISJOINT qt.t_mem {b | p <= b /\ b < p+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ lo <= p /\
    (!v. v <> iv ==> FLOOKUP H v = FLOOKUP G v /\
      eval_operand (Var v) t = eval_operand (Var v) s /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!b n. b+n <= p \/ p+32 <= b ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    t.vs_current_bb = s.vs_current_bb /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt
       (t with vs_inst_idx := s.vs_inst_idx+2)) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >>
  drule_all deploy_ctor_array_index_observation >>
  disch_then (qspecl_then [`tv`,`outsz`] strip_assume_tac) >>
  `FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
   alloca_inv t /\ alloca_frontier_inv_from k ctx func site t` by fs[] >>
  `p < dimword (:256)` by
    (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >>
     fs[alloca_inv_def,alloca_next_valid_def] >>
     `p+32 <= t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  `emitted_insts st st' = [mk_inst st.cs_next_id ALLOCA [Lit 32w] [iv];
    mk_inst (st.cs_next_id+1) MSTORE [Var iv;Lit 0w] []]` by
    (drule ctor_actual_index_insts >> drule abi_decode_index_init_shape >> simp[]) >>
  `run_inst_seq [mk_inst st.cs_next_id ALLOCA [Lit 32w] [iv];
    mk_inst (st.cs_next_id+1) MSTORE [Var iv;Lit 0w] []] s = OK t` by metis_tac[] >>
  drule_all prefix_loop_index_slot_run >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`Ddead`] strip_assume_tac) >>
  qexistsl [`t`,`p`,`H`,`qt`] >> simp[] >> metis_tac[]
QED

Theorem prefix_complete_stage_code_prefix[local]:
  fn_has_code st st' func /\ inst_extends st st' /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> fs[fn_has_code_def] >>
  qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
  asm_rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
  fs[inst_extends_def] >>
  asm_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
  simp[IS_PREFIX_APPEND]
QED

Theorem prefix_complete_stage_raw_indexed[local]:
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
  run_inst_seq (emitted_insts st st') s = OK raw /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ~raw.vs_halted /\ raw.vs_current_bb = st'.cs_current_bb /\
  abi_decode_sim ctx func s (raw with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  `frag_exec ctx st st' (\u. u = s)
    (\t. t = raw with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> fs[inst_extends_def]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

Theorem prefix_complete_guard_fresh[local]:
  abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn asz st = ((),st') /\
  emitted_insts st st' =
    [mk_inst st.cs_next_id DLOAD [src] [x];
     mk_inst (st.cs_next_id+1) GT [Var x;Lit (n2w maxn)] [y];
     mk_inst (st.cs_next_id+2) ISZERO [Var y] [z];
     mk_inst (st.cs_next_id+3) ASSERT [Var z] []] ==>
  !v. abi_decoder_older_vars st.cs_next_var v ==> v <> x /\ v <> y /\ v <> z
Proof
  simp[abi_decode_dynarray_prefix_def,abi_decode_count_guard_def,
    abi_decode_dynarray_end_guard_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  fs[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND,mk_inst_def] >>
  simp[abi_decoder_older_vars_def] >>
  metis_tac[LESS_EQ_REFL,DECIDE ``n <= n+1``,DECIDE ``n <= n+2``]
QED

Theorem prefix_complete_array_guard_entry_pair_exact:
  abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn asz st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\ op_taint tn src = {} /\
  abi_decode_load DLOAD (n2w sb : bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?t H qt.
    (!v. abi_decoder_older_vars st.cs_next_var v ==> lookup_var v t = lookup_var v s) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    t.vs_labels = s.vs_labels /\ abi_encoder_registered_effect {} [] s t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_code = s.vs_code /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. abi_decoder_older_vars st.cs_next_var v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all ctor_actual_array_prefix_code >> strip_tac >>
  drule_all prefix_complete_stage_code_prefix >> strip_tac >>
  drule prefix_loop_count_guard_code >> strip_tac >>
  `isPREFIX [mk_inst st.cs_next_id DLOAD [src] [x];
    mk_inst (st.cs_next_id+1) GT [Var x;Lit (n2w maxn)] [y];
    mk_inst (st.cs_next_id+2) ISZERO [Var y] [z];
    mk_inst (st.cs_next_id+3) ASSERT [Var z] []]
    (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  mp_tac (Q.INST [`iid` |-> `st.cs_next_id`, `cnt` |-> `n`,
    `limit` |-> `maxn`, `fn` |-> `func`, `a` |-> `n2w sb`, `D` |-> `Ddead`]
    prefix_loop_count_guard_run) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK raw` >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  mp_tac (Q.INST [`hi` |-> `Lit 0w`, `initial` |-> `s`, `st'` |-> `st'`,
    `n` |-> `n`] ctor_actual_array_prefix_reentry) >> simp[] >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s = OK raw` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all prefix_complete_stage_raw_indexed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    fs[EVERY_CONJ] >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  `LENGTH st'.cs_current_insts = LENGTH st.cs_current_insts+4` by
    (qpat_x_assum `emitted_insts st st' = _` mp_tac >>
     fs[inst_extends_def,emitted_insts_def] >>
     disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  drule prefix_complete_guard_fresh >> simp[mk_inst_def] >> disch_tac >>
  qmatch_asmsub_abbrev_tac `ptr_safe_run Ddead lo _ ctx func PG H qt _` >>
  qexistsl [`raw with vs_inst_idx := LENGTH st'.cs_current_insts`,`H`,`qt`] >>
  suspend "package"
QED

Resume prefix_complete_array_guard_entry_pair_exact[package]:
  conj_tac >-
    (simp[Abbr `raw`,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  gvs[Abbr `H`,Abbr `qt`,fresh_vars_wrt_def,
    abi_decoder_address_frame_def,eval_op_inst_idx,abi_encoder_registered_effect_def,
    allocas_from_def,FLOOKUP_DRESTRICT,op_taint_def,FLOOKUP_UPDATE,update_var_def] >>
  rpt strip_tac >> res_tac >> simp[]
QED

Finalise prefix_complete_array_guard_entry_pair_exact
Theorem prefix_complete_array_guard_entry_pair:
  abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn asz st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\ op_taint tn src = {} /\
  abi_decode_load DLOAD (n2w sb : bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?t H qt.
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    t.vs_labels = s.vs_labels /\ abi_encoder_registered_effect {} [] s t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_code = s.vs_code /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. abi_decoder_older_vars st.cs_next_var v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >> drule_all prefix_complete_array_guard_entry_pair_exact >>
  disch_then (qspecl_then [`PG`,`G`,`Ddead`] strip_assume_tac) >> qexistsl [`t`,`H`,`qt`] >> simp[]
QED


Theorem prefix_complete_header_fresh[local]:
  abi_decode_array_header dst src DLOAD st = (cnt,st') /\
  emitted_insts st st' = [mk_inst st.cs_next_id DLOAD [src] [x];
    mk_inst (st.cs_next_id+1) MSTORE [dst;Var x] []] ==>
  !v. abi_decoder_older_vars st.cs_next_var v ==> v <> x
Proof
  simp[abi_decode_array_header_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  fs[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND,mk_inst_def] >>
  simp[abi_decoder_older_vars_def] >>
  qexists `st.cs_next_var` >> simp[]
QED

Theorem prefix_complete_array_header_entry_pair_exact:
  abi_decode_array_header (Var dst) src DLOAD st = (cnt,st') /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  eval_operand (Var dst) s = SOME (n2w d) /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,cap) /\ b <= d /\ d+32 <= b+cap /\ d < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?t H qt.
    (!v. abi_decoder_older_vars st.cs_next_var v ==> lookup_var v t = lookup_var v s) /\
    eval_operand cnt t = SOME (abi_decode_load DLOAD a s) /\
    mem_word_at d t.vs_memory = abi_decode_load DLOAD a s /\
    fresh_vars_wrt limit_st t /\ abi_decode_frame d 32 s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    t.vs_labels = s.vs_labels /\ abi_encoder_registered_effect {} [(d,32)] s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    t.vs_code = s.vs_code /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ FLOOKUP H dst = SOME (b,cap) /\
    op_taint qt (Var dst) = {} /\ op_taint qt cnt = {} /\
    DISJOINT qt.t_mem {a | d <= a /\ a < d+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. abi_decoder_older_vars st.cs_next_var v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule_all prefix_complete_stage_code_prefix >> strip_tac >>
  drule prefix_loop_count_header_code >> strip_tac >>
  `!v. abi_decoder_older_vars st.cs_next_var v ==> v <> x` by
    (drule prefix_complete_header_fresh >> simp[mk_inst_def]) >>
  `dst <> x` by
    (fs[abi_decoder_operand_live_def,IN_DEF] >> metis_tac[]) >>
  drule_all prefix_loop_count_header_pair_interior >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all prefix_complete_stage_raw_indexed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule ctor_actual_array_count_header_code >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >>
     qexists `emitted_insts st st'` >> fs[EVERY_CONJ]) >>
  `LENGTH st'.cs_current_insts = LENGTH st.cs_current_insts+2` by
    (qpat_x_assum `emitted_insts st st' = _` mp_tac >>
     fs[inst_extends_def,emitted_insts_def] >>
     disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  qexistsl [`t with vs_inst_idx := LENGTH st'.cs_current_insts`,`H`,`qt`] >>
  conj_tac >-
    (simp[Once lookup_var_def] >> rpt strip_tac >>
     `lookup_var v t = lookup_var v s` suffices_by simp[lookup_var_def] >>
     irule ctor_actual_sequence_var_frame >>
     qexists `emitted_insts st st'` >> simp[mk_inst_def,is_terminator_def]) >>
  gvs[fresh_vars_wrt_def,abi_decode_frame_def,eval_op_inst_idx,
    abi_encoder_registered_effect_def,allocas_from_def] >> metis_tac[]
QED

Theorem prefix_complete_array_header_entry_pair:
  abi_decode_array_header (Var dst) src DLOAD st = (cnt,st') /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  eval_operand (Var dst) s = SOME (n2w d) /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,cap) /\ b <= d /\ d+32 <= b+cap /\ d < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?t H qt.
    eval_operand cnt t = SOME (abi_decode_load DLOAD a s) /\
    mem_word_at d t.vs_memory = abi_decode_load DLOAD a s /\
    fresh_vars_wrt limit_st t /\ abi_decode_frame d 32 s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    t.vs_labels = s.vs_labels /\ abi_encoder_registered_effect {} [(d,32)] s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    t.vs_code = s.vs_code /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ FLOOKUP H dst = SOME (b,cap) /\
    op_taint qt (Var dst) = {} /\ op_taint qt cnt = {} /\
    DISJOINT qt.t_mem {a | d <= a /\ a < d+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. abi_decoder_older_vars st.cs_next_var v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >> drule_all prefix_complete_array_header_entry_pair_exact >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  qexistsl [`t`,`H`,`qt`] >> simp[]
QED

Theorem prefix_complete_array_index_entry_pair:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts func)) /\
  st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ mload d s = n2w (LENGTH vs) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t p H qt.
    (^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t /\
    FLOOKUP H (STRING #"%" (toString st.cs_next_var)) = SOME (p,32) /\
    eval_operand ip t = SOME (n2w p) /\ op_taint qt ip = {} /\
    DISJOINT qt.t_mem {b | p <= b /\ b < p+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ lo <= p /\
    (!v. abi_decoder_older_vars st.cs_next_var v ==>
      FLOOKUP H v = FLOOKUP G v /\
      eval_operand (Var v) t = eval_operand (Var v) s /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!b n. b+n <= p \/ p+32 <= b ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule_all prefix_complete_stage_code_prefix >> strip_tac >>
  `emitted_insts st st' =
    [mk_inst st.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id+1) MSTORE [ip;Lit 0w] []]` by
    (drule ctor_actual_index_insts >> simp[]) >>
  `get_instruction bb s.vs_inst_idx = SOME
     (mk_inst st.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString st.cs_next_var)]) /\
   get_instruction bb (SUC s.vs_inst_idx) = SOME
     (mk_inst (st.cs_next_id+1) MSTORE [Var (STRING #"%" (toString st.cs_next_var));Lit 0w] [])` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     pure_asm_rewrite_tac[] >> strip_tac >>
     drule instruction_prefix_cursor >> strip_tac >>
     drule instruction_prefix_cursor >> simp[]) >>
  `st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  `abi_decode_index_init st = (Var (STRING #"%" (toString st.cs_next_var)),st')` by simp[] >>
  drule_all (SRULE [] (Q.INST [`ip` |-> `Var iv`]
    (SPEC_ALL prefix_complete_array_index_pair))) >>
  disch_then (qspecl_then [`tv`,`tn`,`outsz`,`PG`,`G`,`Ddead`] strip_assume_tac) >>
  drule_all prefix_complete_stage_raw_indexed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    simp[abi_decoder_reentry_opcode_def,mk_inst_def] >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  `LENGTH st'.cs_current_insts = LENGTH st.cs_current_insts+2` by
    (qpat_x_assum `emitted_insts st st' = _` mp_tac >>
     fs[inst_extends_def,emitted_insts_def] >>
     disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  qexistsl [`t with vs_inst_idx := LENGTH st'.cs_current_insts`,`p`,`H`,`qt`] >>
  simp[eval_op_inst_idx] >>
  conj_tac >- (fs[allocas_from_def] >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >>
     `v <> STRING #"%" (toString st.cs_next_var)` by
       (fs[abi_decoder_older_vars_def] >> metis_tac[LESS_EQ_REFL]) >>
     metis_tac[]) >>
  metis_tac[]
QED

Theorem prefix_complete_array_setup_pair_exact:
  abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn asz st = ((),guard_st) /\
  abi_decode_array_header (Var dst) src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= outsz /\
  fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
  fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+outsz <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?prepared slot iv H qt.
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      lookup_var x prepared = lookup_var x initial) /\
    ip = Var iv /\
    (^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 prepared /\
    (^Ok) k ctx func site ids D N d outsz
      loop_st.cs_next_var limit_st tv vs header_st.cs_next_id slot prepared 0 0 prepared /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial prepared /\
    eval_operand src prepared = SOME (n2w sb) /\
    eval_operand (Var dst) prepared = SOME (n2w d) /\
    eval_operand ip prepared = SOME (n2w slot) /\
    FLOOKUP H dst = SOME (b,sz) /\ FLOOKUP H iv = SOME (slot,32) /\
    op_taint qt src = {} /\ op_taint qt (Var dst) = {} /\ op_taint qt ip = {} /\
    DISJOINT qt.t_mem {a | d <= a /\ a < d+32} /\
    DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\ lo <= slot /\
    prepared.vs_code = initial.vs_code /\ prepared.vs_gas_readings = initial.vs_gas_readings /\
    prepared.vs_outcomes = initial.vs_outcomes /\ prepared.vs_tx_ctx = initial.vs_tx_ctx /\
    prepared.vs_block_ctx = initial.vs_block_ctx /\
    (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= slot \/ slot+32 <= a) ==>
      mem_bytes_at a n prepared.vs_memory = mem_bytes_at a n initial.vs_memory) /\
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `guard_st.cs_next_var <= limit_st.cs_next_var /\
   header_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all prefix_complete_array_guard_entry_pair_exact >>
  disch_then (qspecl_then [`PG`,`G`,`Ddead`] strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial guard` >>
  rename1 `qt.t_mem = tn.t_mem` >>
  rename1 `!v. abi_decoder_older_vars st.cs_next_var v ==>
    FLOOKUP GG v = FLOOKUP G v /\ op_taint gt (Var v) = op_taint tn (Var v)` >>
  `eval_operand src guard = SOME (n2w sb) /\
   eval_operand (Var dst) guard = SOME (n2w d)` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `FLOOKUP GG dst = SOME (b,sz) /\ op_taint gt src = {} /\
   op_taint gt (Var dst) = {}` by
    (Cases_on `src` >> fs[abi_decoder_operand_live_def,op_taint_def,IN_DEF] >> metis_tac[]) >>
  `abi_decoder_operand_live guard_st.cs_next_var src /\
   abi_decoder_operand_live guard_st.cs_next_var (Var dst)` by
    (metis_tac[abi_decoder_operand_live_mono]) >>
  `d+32 <= b+sz` by decide_tac >>
  drule_all prefix_complete_array_header_entry_pair_exact >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  `t.vs_allocas = initial.vs_allocas /\
   t.vs_alloca_next = initial.vs_alloca_next` by metis_tac[] >>
  `alloca_inv t /\ alloca_frontier_inv_from k ctx func site t /\
   ctor_actual_scratch func ids D N t /\ D+N <= t.vs_alloca_next` by
    metis_tac[deploy_ctor_array_allocation_state] >>
  `abi_decode_load DLOAD (n2w sb : bytes32) guard = n2w (LENGTH vs)` by
    (fs[abi_decoder_address_frame_def,abi_decode_load_def,abi_decode_source_def]) >>
  `mload d t = n2w (LENGTH vs)` by metis_tac[valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  drule_all prefix_complete_array_index_entry_pair >>
  disch_then (qspecl_then [`tv`,`qt`,`outsz`,`PG`,`H`,`Ddead`] strip_assume_tac) >>
  `!x. abi_decoder_older_vars st.cs_next_var x ==>
    abi_decoder_older_vars guard_st.cs_next_var x /\
    abi_decoder_older_vars header_st.cs_next_var x` by
    (simp[abi_decoder_older_vars_def,IN_DEF] >> metis_tac[LESS_EQ_TRANS,LESS_EQ_ADD]) >>
  `!x w. abi_decoder_older_vars st.cs_next_var x /\ lookup_var x initial = SOME w ==>
    lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `eval_operand (Var x) guard = SOME w` by
       (qpat_x_assum `abi_decoder_address_frame _ initial guard` mp_tac >>
        simp[abi_decoder_address_frame_def] >> strip_tac >>
        first_x_assum irule >> simp[abi_decoder_operand_live_def,eval_operand_def,IN_DEF]) >>
     `eval_operand (Var x) t = SOME w` suffices_by simp[eval_operand_def] >>
     qpat_x_assum `!op w. abi_decoder_operand_live guard_st.cs_next_var op /\ _ ==> _` irule >>
     simp[abi_decoder_operand_live_def,IN_DEF]) >>
  `t.vs_data_section = initial.vs_data_section /\
   t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_labels = initial.vs_labels` by
    (fs[abi_decode_frame_def,abi_decoder_address_frame_def] >> metis_tac[]) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial guard` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`,`[]`] >> simp[]) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] guard t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`,`[(d,32)]`] >> simp[] >> decide_tac) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial t` by
    (irule abi_encoder_registered_effect_trans >> qexists `guard` >> simp[]) >>
  `(^Ok) k ctx func site ids D N d outsz st.cs_next_var limit_st tv vs
    header_st.cs_next_id p initial 0 0 t'` by
    (irule deploy_ctor_array_observation_rebase >>
     qexistsl [`header_st.cs_next_var`,`t`] >> simp[] >> decide_tac) >>
  `(^Ok) k ctx func site ids D N d outsz loop_st.cs_next_var limit_st tv vs
    header_st.cs_next_id p t' 0 0 t'` by
    (irule deploy_ctor_array_observation_self >> metis_tac[]) >>
  `!x. abi_decoder_older_vars st.cs_next_var x ==>
    lookup_var x t' = lookup_var x initial` by
    (rpt strip_tac >>
     `lookup_var x guard = lookup_var x initial` by metis_tac[] >>
     `lookup_var x t = lookup_var x guard` by metis_tac[] >>
     `eval_operand (Var x) t' = eval_operand (Var x) t` by metis_tac[] >>
     fs[eval_operand_def]) >>
  qexistsl [`t'`,`p`,`STRING #"%" (toString header_st.cs_next_var)`,`H'`,`qt'`] >>
  simp[] >>
  conj_tac >- metis_tac[abi_decode_sim_trans] >>
  conj_tac >-
    (Cases_on `src` >> fs[eval_operand_def,abi_decoder_operand_live_def,IN_DEF] >>
     qpat_x_assum `(^Ok) _ _ _ _ _ _ _ _ _ st.cs_next_var _ _ _ _ _ initial _ _ t'` mp_tac >>
     BETA_TAC >> strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `(^Ok) _ _ _ _ _ _ _ _ _ st.cs_next_var _ _ _ _ _ initial _ _ t'` mp_tac >>
     BETA_TAC >> strip_tac >> fs[eval_operand_def,abi_decoder_operand_live_def,IN_DEF] >>
     first_x_assum irule >> simp[]) >>
  `abi_decoder_older_vars header_st.cs_next_var dst` by
    (fs[abi_decoder_operand_live_def,IN_DEF] >> metis_tac[]) >>
  simp[] >>
  conj_tac >-
    (Cases_on `src` >> fs[abi_decoder_operand_live_def,op_taint_def,IN_DEF] >> metis_tac[]) >>
  conj_tac >-
    (irule SUBSET_DISJOINT >> qexistsl [`qt.t_mem`,`{a | d <= a /\ a < d+32}`] >> simp[]) >>
  conj_tac >- metis_tac[SUBSET_TRANS] >>
  conj_tac >- (fs[] >> NO_TAC) >>
  conj_tac >- (fs[] >> NO_TAC) >>
  rpt strip_tac >> fs[abi_decode_frame_def] >> metis_tac[]
QED

Theorem prefix_complete_array_setup_pair:
  abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn asz st = ((),guard_st) /\
  abi_decode_array_header (Var dst) src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= outsz /\
  fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
  fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+outsz <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?prepared slot iv H qt.
    ip = Var iv /\
    (^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 prepared /\
    (^Ok) k ctx func site ids D N d outsz
      loop_st.cs_next_var limit_st tv vs header_st.cs_next_id slot prepared 0 0 prepared /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial prepared /\
    eval_operand src prepared = SOME (n2w sb) /\
    eval_operand (Var dst) prepared = SOME (n2w d) /\
    eval_operand ip prepared = SOME (n2w slot) /\
    FLOOKUP H dst = SOME (b,sz) /\ FLOOKUP H iv = SOME (slot,32) /\
    op_taint qt src = {} /\ op_taint qt (Var dst) = {} /\ op_taint qt ip = {} /\
    DISJOINT qt.t_mem {a | d <= a /\ a < d+32} /\
    DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\ lo <= slot /\
    prepared.vs_code = initial.vs_code /\ prepared.vs_gas_readings = initial.vs_gas_readings /\
    prepared.vs_outcomes = initial.vs_outcomes /\ prepared.vs_tx_ctx = initial.vs_tx_ctx /\
    prepared.vs_block_ctx = initial.vs_block_ctx /\
    (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= slot \/ slot+32 <= a) ==>
      mem_bytes_at a n prepared.vs_memory = mem_bytes_at a n initial.vs_memory) /\
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)
Proof
  strip_tac >> drule_all prefix_complete_array_setup_pair_exact >>
  disch_then (qspecl_then [`tv`,`PG`,`Ddead`] strip_assume_tac) >>
  qexistsl [`prepared`,`slot`,`iv`,`H`,`qt`] >> asm_rewrite_tac[]
QED

(* A finite protected header determines its word observation. *)
Theorem prefix_complete_array_protected_header[local]:
  mload d s = w /\
  (!a. a IN range_bytes [(d,32)] ==>
    mem_bytes_at a 1 mem = mem_bytes_at a 1 s.vs_memory) ==>
  mload d (s with vs_memory := mem) = w
Proof
  strip_tac >>
  `mem_bytes_at d 32 mem = mem_bytes_at d 32 s.vs_memory` by
    (irule abiEncoderZeroFrameTheory.abi_encoder_mem_bytes_singletons >>
     fs[range_bytes_def]) >>
  fs[mload_def,valueEncodingTheory.mem_bytes_at_def]
QED

Theorem prefix_complete_array_slot_separation[local]:
  ctor_actual_scratch func ids D N s /\
  slot_id IN ctor_actual_sites func ids /\
  FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\
  D <= d /\ d+outsz <= D+N /\ 0 < outsz ==>
  venomMemDefs$regions_disjoint (slot,32) (d,outsz)
Proof
  simp [ctor_actual_scratch_def,ctorAbiActualSitesTheory.ctor_actual_sites_def] >>
  strip_tac >>
  `venomMemDefs$regions_disjoint (D,N) (slot,32)` by metis_tac[] >>
  qpat_x_assum `!inst b sz. _` kall_tac >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

val PreparedPk = ``
  abi_decoder_recursive_loop_compiled ce sf ty func body_st middle end_st ops (Var slot_var) src (Var dst_var)
    DLOAD (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi loop_st.cs_next_var limit_st header_st.cs_next_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) (Var slot_var) src (Var dst_var)
    sb d slot slot 32 loop_st.cs_next_var prepared /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    prepared.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  fn_inst_ids_distinct func /\ k + unit_alloca_budget ctx < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  lo <= slot /\ lo <= d /\ D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\ frag_ids body_st end_st SUBSET ids /\
  header_st.cs_next_id NOTIN frag_ids middle end_st /\ b <= d /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b+sz``;

val PreparedLoopAt = ``
  (^Ok) k ctx func site ids D N d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    loop_st.cs_next_var limit_st tv vs header_st.cs_next_id slot prepared 0 0 prepared /\
  ~prepared.vs_halted /\ prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
  allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\
  FLOOKUP H slot_var = SOME (slot,32) /\ FLOOKUP H dst_var = SOME (b,sz) /\
  op_taint qt (Var slot_var) = {} /\ op_taint qt (Var dst_var) = {} /\ op_taint qt src = {} /\
  DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\
  FINITE (range_bytes [(d,32)]) /\
  range_bytes [(d,32)] SUBSET range_bytes [(d,32+0*type_memory_size tv)] /\
  DISJOINT (range_bytes [(d,32)]) qt.t_mem /\
  (!mem. (!a. a IN range_bytes [(d,32)] ==>
     mem_bytes_at a 1 mem = mem_bytes_at a 1 prepared.vs_memory) ==>
    mload d (prepared with vs_memory := mem) = n2w (LENGTH vs) /\
    elems_in_memory (TAKE 0 vs) (d+32) tv mem)``;

Theorem prefix_complete_array_setup_loop_pair_exact:
  abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn asz st = ((),guard_st) /\
  abi_decode_array_header (Var dst_var) src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (Var slot_var,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst_var) initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst_var) /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
  fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst_var = SOME (b,sz) /\ b <= d /\
  d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst_var) = {} /\
  allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  abi_decoder_recursive_loop_compiled ce sf ty func body_st middle end_st ops (Var slot_var) src (Var dst_var)
    DLOAD (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi loop_st.cs_next_var limit_st header_st.cs_next_id /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn))) (ListV avs) (ArrayV (DynArrayV vs)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))) initial.vs_data_section =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  lo <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids body_st end_st SUBSET ids /\ header_st.cs_next_id NOTIN frag_ids middle end_st /\
  lookup_block loop_st.cs_current_bb func.fn_blocks = SOME entry_bb /\
  entry_bb.bb_instructions = loop_st.cs_current_insts ++ [mk_inst jump_id JMP [Label hdr] []] ==>
  ?prepared slot H qt.
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      lookup_var x prepared = lookup_var x initial) /\
    (^Ok) k ctx func site ids D N d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 prepared /\
    (^Ok) k ctx func site ids D N d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
      loop_st.cs_next_var limit_st tv vs header_st.cs_next_id slot prepared 0 0 prepared /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial prepared /\
    eval_operand src prepared = SOME (n2w sb) /\
    eval_operand (Var dst_var) prepared = SOME (n2w d) /\
    eval_operand (Var slot_var) prepared = SOME (n2w slot) /\
    FLOOKUP H dst_var = SOME (b,sz) /\ FLOOKUP H slot_var = SOME (slot,32) /\
    op_taint qt src = {} /\ op_taint qt (Var dst_var) = {} /\ op_taint qt (Var slot_var) = {} /\
    DISJOINT qt.t_mem {a | d <= a /\ a < d+32} /\
    DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\ lo <= slot /\
    prepared.vs_code = initial.vs_code /\ prepared.vs_gas_readings = initial.vs_gas_readings /\
    prepared.vs_outcomes = initial.vs_outcomes /\ prepared.vs_tx_ctx = initial.vs_tx_ctx /\
    prepared.vs_block_ctx = initial.vs_block_ctx /\
    (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= slot \/ slot+32 <= a) ==>
      mem_bytes_at a n prepared.vs_memory = mem_bytes_at a n initial.vs_memory) /\
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial) /\
    (^PreparedPk) /\ (^PreparedLoopAt) /\
    lookup_block prepared.vs_current_bb func.fn_blocks = SOME entry_bb /\
    ?hdr_bb. lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0
Proof
  strip_tac >>
  drule_all prefix_complete_array_setup_pair_exact >>
  disch_then (qspecl_then [`tv`,`PG`,`Ddead`] strip_assume_tac) >>
  qpat_x_assum `Var slot_var = Var iv` (SUBST_ALL_TAC o SYM o SRULE []) >>
  `(^PreparedPk)` by suspend "data_package" >>
  `(^PreparedLoopAt)` by suspend "loop_zero" >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_recursive_compiled_facts >> strip_tac >>
  qexistsl [`prepared`,`slot`,`H`,`qt`] >> asm_simp_tac bool_ss [] >>
  metis_tac[]
QED

Resume prefix_complete_array_setup_loop_pair_exact[data_package]:
  qpat_assum `(^Ok) _ _ _ _ _ _ _ _ _ st.cs_next_var _ _ _ _ _ initial _ _ prepared`
    (strip_assume_tac o BETA_RULE) >>
  `venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))` by
    (irule prefix_complete_array_slot_separation >> (conj_tac >- decide_tac) >>
     qexistsl [`D`,`N`,`func`,`ids`,`prepared`,`header_st.cs_next_id`] >> simp[]) >>
  `slot < dimword (:256)` by suspend "slot_bound" >>
  `abi_decoder_operand_live loop_st.cs_next_var src /\
   abi_decoder_operand_live loop_st.cs_next_var (Var dst_var) /\
   abi_decoder_operand_live loop_st.cs_next_var (Var slot_var)` by suspend "live" >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- suspend "recursive_data" >>
  suspend "distinct_ids"
QED

Resume prefix_complete_array_setup_loop_pair_exact[loop_zero]:
  asm_simp_tac std_ss [SUBSET_REFL] >>
  conj_tac >- metis_tac[ctorDeployMemoryRunPtrPrefixCopySupportTheory.prefix_copy_range_finite] >>
  conj_tac >-
    (qpat_x_assum `DISJOINT qt.t_mem {a | d <= a /\ a < d+32}` mp_tac >>
     simp[range_bytes_def,DISJOINT_SYM]) >>
  gen_tac >> disch_tac >> conj_tac
  >- (irule prefix_complete_array_protected_header >> simp[] >>
      qpat_assum `(^Ok) _ _ _ _ _ _ _ _ _ st.cs_next_var _ _ _ _ _ initial _ _ prepared`
        (strip_assume_tac o BETA_RULE) >> simp[]) >>
  simp[valueEncodingTheory.val_in_memory_def]
QED

Resume prefix_complete_array_setup_loop_pair_exact[slot_bound]:
  `prepared.vs_alloca_next < dimword (:256)` by
    (drule_all deploy_ctor_shifted_frontier_bound >> simp[]) >>
  `slot+32 <= prepared.vs_alloca_next` by
    (qpat_x_assum `alloca_inv prepared` mp_tac >>
     simp_tac bool_ss [alloca_inv_def,alloca_next_valid_def] >>
     strip_tac >> first_x_assum drule >> simp[]) >> decide_tac
QED

Resume prefix_complete_array_setup_loop_pair_exact[live]:
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `st.cs_next_var <= loop_st.cs_next_var` by decide_tac >>
  conj_tac >- metis_tac[abi_decoder_operand_live_mono] >>
  conj_tac >- metis_tac[abi_decoder_operand_live_mono] >>
  qpat_x_assum `Var slot_var = Var _` (SUBST_ALL_TAC o SRULE []) >>
  simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,IN_DEF]
QED

Resume prefix_complete_array_setup_loop_pair_exact[recursive_data]:
  asm_simp_tac bool_ss [abi_decoder_recursive_loop_data_def,abi_decoder_ranges_def,
    abi_decode_source_opcode_def,abi_decoder_operand_live_def] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (slot,32) _` mp_tac >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Resume prefix_complete_array_setup_loop_pair_exact[distinct_ids]:
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  qpat_x_assum `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` mp_tac >>
  simp[fn_inst_ids_distinct_def,fn_insts_def]
QED

Finalise prefix_complete_array_setup_loop_pair_exact

Theorem prefix_complete_array_setup_loop_pair:
  abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn asz st = ((),guard_st) /\
  abi_decode_array_header (Var dst_var) src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (Var slot_var,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst_var) initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst_var) /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
  fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst_var = SOME (b,sz) /\ b <= d /\
  d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst_var) = {} /\
  allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  abi_decoder_recursive_loop_compiled ce sf ty func body_st middle end_st ops (Var slot_var) src (Var dst_var)
    DLOAD (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi loop_st.cs_next_var limit_st header_st.cs_next_id /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn))) (ListV avs) (ArrayV (DynArrayV vs)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))) initial.vs_data_section =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  lo <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids body_st end_st SUBSET ids /\ header_st.cs_next_id NOTIN frag_ids middle end_st /\
  lookup_block loop_st.cs_current_bb func.fn_blocks = SOME entry_bb /\
  entry_bb.bb_instructions = loop_st.cs_current_insts ++ [mk_inst jump_id JMP [Label hdr] []] ==>
  ?prepared slot H qt.
    (^Ok) k ctx func site ids D N d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 prepared /\
    (^Ok) k ctx func site ids D N d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
      loop_st.cs_next_var limit_st tv vs header_st.cs_next_id slot prepared 0 0 prepared /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial prepared /\
    eval_operand src prepared = SOME (n2w sb) /\
    eval_operand (Var dst_var) prepared = SOME (n2w d) /\
    eval_operand (Var slot_var) prepared = SOME (n2w slot) /\
    FLOOKUP H dst_var = SOME (b,sz) /\ FLOOKUP H slot_var = SOME (slot,32) /\
    op_taint qt src = {} /\ op_taint qt (Var dst_var) = {} /\ op_taint qt (Var slot_var) = {} /\
    DISJOINT qt.t_mem {a | d <= a /\ a < d+32} /\
    DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\ lo <= slot /\
    prepared.vs_code = initial.vs_code /\ prepared.vs_gas_readings = initial.vs_gas_readings /\
    prepared.vs_outcomes = initial.vs_outcomes /\ prepared.vs_tx_ctx = initial.vs_tx_ctx /\
    prepared.vs_block_ctx = initial.vs_block_ctx /\
    (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= slot \/ slot+32 <= a) ==>
      mem_bytes_at a n prepared.vs_memory = mem_bytes_at a n initial.vs_memory) /\
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial) /\
    (^PreparedPk) /\ (^PreparedLoopAt) /\
    lookup_block prepared.vs_current_bb func.fn_blocks = SOME entry_bb /\
    ?hdr_bb. lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0
Proof
  strip_tac >>
  mp_tac (Q.INST [`PG` |-> `PG`, `Ddead` |-> `Ddead`]
    (SPEC_ALL prefix_complete_array_setup_loop_pair_exact)) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qexistsl [`prepared`,`slot`,`H`,`qt`] >> asm_rewrite_tac[] >>
  qexists `hdr_bb` >> simp[]
QED
