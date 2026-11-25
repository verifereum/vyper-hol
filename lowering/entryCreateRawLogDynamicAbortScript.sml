(* The static dynamic-data RawLog stops at the LOG fetch, after MLOAD/ADD. *)
Theory entryCreateRawLogDynamicAbort
Ancestors
  bodyFullRawLogDynamicTailPath entryCreatePathScope entryCreateCompletedCut
  createSizePrefixReplay createMarkedPath fragGasSeq fragGasOrigin fragExec
  emitHelperProps exprLoweringProps abiEncoderProps venomInstProofs1 instIdxIndep
  venomExecSemantics venomState venomInst list rich_list relation arithmetic

Theorem raw_log_scope_ok_edge[local]:
  ~s.vs_halted /\ s.vs_inst_idx < LENGTH b.cs_current_insts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\ step_inst_base i s = OK u ==>
  create_expr_prefix a b E C fn s [] (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `gas_path_edge C fn s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_all tuple_straight_line_edge >> simp[]) >>
  drule gas_path_edge_zero_origin >> strip_tac >>
  simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
  simp[create_marked_edge_def, create_prefix_step_def] >>
  `s.vs_inst_idx <> LENGTH b.cs_current_insts` by decide_tac >>
  qexistsl_tac [`bb`,`i`] >> simp[]
QED

Theorem raw_log_scope_two_steps[local]:
  ~s.vs_halted /\ SUC s.vs_inst_idx < LENGTH b.cs_current_insts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME j /\
  EVERY (\k. k.inst_id IN frag_ids a b /\ k.inst_opcode <> INVOKE /\
          k.inst_opcode <> GAS /\ ~is_terminator k.inst_opcode) [i;j] /\
  run_inst_seq [i;j] s = OK t ==>
  create_expr_prefix a b E C fn s [] (t with vs_inst_idx := SUC (SUC s.vs_inst_idx))
Proof
  strip_tac >> fs[EVERY_DEF] >>
  Cases_on `step_inst_base i s` >> fs[run_inst_seq_def] >>
  rename1 `step_inst_base i s = OK v` >>
  `~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb` by
    (drule_all step_inst_base_preserves_all >> simp[]) >>
  qabbrev_tac `w = v with vs_inst_idx := SUC s.vs_inst_idx` >>
  `run_inst_seq [j] v = OK t` by simp[run_inst_seq_def] >>
  `run_inst_seq [j] w = OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Abbr `w`, run_inst_seq_inst_idx, exec_result_map_def] >>
  `step_inst_base j w = OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `run_inst_seq [j] w = _` mp_tac >>
     Cases_on `step_inst_base j w` >> simp[run_inst_seq_def]) >>
  `s.vs_inst_idx < LENGTH b.cs_current_insts` by decide_tac >>
  `create_expr_prefix a b E C fn s [] w` by
    (simp[Abbr `w`] >> irule raw_log_scope_ok_edge >> simp[] >>
     qexistsl_tac [`bb`,`i`] >> simp[]) >>
  `create_expr_prefix a b E C fn w []
     ((t with vs_inst_idx := SUC s.vs_inst_idx) with vs_inst_idx := SUC w.vs_inst_idx)` by
    (irule raw_log_scope_ok_edge >> fs[Abbr `w`] >>
     qexistsl_tac [`bb`,`j`] >> simp[]) >>
  `create_expr_prefix a b E C fn w [] (t with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by
    fs[Abbr `w`] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`left` |-> `[]`, `right` |-> `[]`] create_expr_prefix_append)) >> simp[]
QED

Theorem raw_log_dynamic_prepare_scope[local]:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG logops [] s2 = ((),sb) /\ fn_has_code sm sb func /\
  EVERY (\i. i.inst_id IN frag_ids sm sb /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
    ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sm sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm s2) s = OK t ==>
  create_expr_prefix sm sb explicit ctx func s []
    (t with vs_inst_idx := LENGTH s2.cs_current_insts)
Proof
  strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_assum `emit_op ADD _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_tac o MATCH_MP emit_op_extends) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_tac o MATCH_MP emit_op_extends) >>
  qpat_assum `emit_inst LOG _ _ _ = _` (strip_assume_tac o MATCH_MP emit_inst_extends) >>
  strip_tac >> strip_tac >> fs[same_blocks_def] >>
  qmatch_asmsub_abbrev_tac `emitted_insts sm s1 = [i]` >>
  qmatch_asmsub_abbrev_tac `emitted_insts s1 s2 = [j]` >>
  qabbrev_tac `k = mk_inst s2.cs_next_id LOG logops []` >>
  `s2.cs_current_insts = sm.cs_current_insts ++ [i;j] /\
   sb.cs_current_insts = sm.cs_current_insts ++ [i;j;k]` by
    (asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[]) >>
  `emitted_insts sm s2 = [i;j] /\ emitted_insts sm sb = [i;j;k]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb (LENGTH sm.cs_current_insts) = SOME i /\
        get_instruction bb (SUC (LENGTH sm.cs_current_insts)) = SOME j` by
    (drule_all fn_has_code_same_block >> strip_tac >> qexists_tac `bb` >> simp[] >>
     conj_tac
     >- (qpat_assum `!n. n < _ ==> get_instruction _ _ = _`
           (qspec_then `0` mp_tac) >> simp[NoAsms,EL]) >>
     qpat_assum `!n. n < _ ==> get_instruction _ _ = _`
       (qspec_then `SUC 0` mp_tac) >> simp[NoAsms,EL,ADD_CLAUSES,ADD1]) >>
  `LENGTH sm.cs_current_insts + 2 = SUC (SUC s.vs_inst_idx)` by simp[ADD1] >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
  irule raw_log_scope_two_steps >> simp[] >>
  qpat_x_assum `EVERY _ (emitted_insts sm sb)` mp_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts sm s2) s = OK t` mp_tac >>
  simp[EVERY_DEF]
QED

Theorem create_raw_log_dynamic_tail_scoped_abort:
  cx.txn.is_static /\
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  LENGTH ops < dimword (:256) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (data_op::ops) /\
  sa.cs_next_var <= sm.cs_next_var /\
  expr_type data = BaseT (BytesT (Dynamic cap)) /\
  post_value_type cenv data = expr_type data /\
  evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_type (Call ann RawLog es_call dflt) = NoneT /\
  post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
  expr_has_effect (Call ann RawLog es_call dflt) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
    expr_store_bound cx (expr_type data) (BytesV bs) data_op s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn s /\
    ptr_buf_ok cenv data data_op G s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    eval_operands ops s = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tn op = {}) ops /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts) /\
  EVERY (\i. i.inst_id IN frag_ids sm sb /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
    ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sm sb) ==>
  ?u G1 tn1. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort ExHalt_abort u,G1,tn1) /\
    create_operand_full_scope sm sb explicit ctx func s [] (Abort ExHalt_abort u)
Proof
  strip_tac >> drule_all raw_log_dynamic_static_tail_witness >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`u`,`G1`,`tn1`] >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> run_inst_seq _ _ = _ /\ _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  simp[] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `create_expr_prefix sm sb explicit ctx func s []
      (t with vs_inst_idx := LENGTH s2.cs_current_insts)` by
    (drule_all raw_log_dynamic_prepare_scope >> simp[]) >>
  irule (SIMP_RULE (srw_ss()) [exit_result_def]
    (Q.INST [`left` |-> `[]`,`last` |-> `[]`] create_operand_full_scope_terminal)) >>
  simp[exit_result_def] >>
  qexists_tac `t with vs_inst_idx := LENGTH s2.cs_current_insts` >> simp[] >>
  drule emit_inst_extends >> simp[]
QED
