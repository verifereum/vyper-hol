(* Pointer-check boundary for LOG, including literal-zero empty data. *)
Theory logEmitPtr
Ancestors
  stmtSimLogEmit stmtSimLogSuffix emitHelperProps emitHelper compileEnv
  ghostPcTransportPtr stmtFragPtr exprSimPtrLiteralBuffer
  ptrSafeRun ptrDiscipline bodyPtrDefs contextCodegenRel
  logInstSeqPtr fragGasSeqPtr exprLoweringProps codegenRel memLocDefs venomExecSemantics venomState venomInst finite_map words list
  arithmetic pred_set

Theorem log_emit_memory_interface:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op] /\
  LENGTH topic_ops < dimword (:256) /\ eval_operands topic_ops s = SOME topics /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME len ==>
  source_memory_read_ranges inst s = [(w2n off,w2n len)] /\
  source_memory_write_ranges inst s = [] /\
  mem_read_ops inst = SOME <|iao_ofst := ptr_op; iao_size := SOME len_op;
    iao_max_size := SOME len_op|>
Proof
  strip_tac >>
  simp[source_memory_read_ranges_def, source_memory_write_ranges_def,
    memory_range_of_operands_def, mem_read_ops_def, REVERSE_APPEND, w2n_n2w] >>
  Cases_on `topic_ops` >> simp[]
QED

Theorem log_emit_access_taint:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op] /\
  LENGTH topic_ops < dimword (:256) /\ eval_operands topic_ops s = SOME topics /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME len /\
  EVERY (\op. op_taint tn op = {}) (ptr_op::len_op::topic_ops) /\
  (w2n len <> 0 ==> ?v. ptr_op = Var v /\ ptr_covers G tn v s (w2n len)) /\
  (!i. w2n off <= i /\ i < w2n off + w2n len ==> i NOTIN tn.t_mem) ==>
  access_ok 0 G func inst s /\ taint_ok func tn inst s
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all log_emit_memory_interface >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  conj_tac
  >- (simp[access_ok_def] >> rpt strip_tac >>
      `w2n len <> 0` by simp[] >>
      qpat_x_assum `w2n len <> 0 ==> _` drule >> strip_tac >>
      gvs[ptr_covers_def, eval_operand_def]) >>
  `EVERY (\op. op_taint tn op = {}) inst.inst_operands` by
    (simp[EVERY_MEM, MEM_REVERSE] >> rpt strip_tac >>
     fs[EVERY_MEM] >> gvs[op_taint_def]) >>
  pure_rewrite_tac[taint_ok_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `EVERY _ inst.inst_operands` mp_tac >>
      rewrite_tac[EVERY_MEM] >> disch_then drule >> simp[]) >>
  asm_simp_tac bool_ss [] >> simp[] >> metis_tac[ADD_COMM]
QED

Theorem log_emit_inst_ok:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op] /\
  LENGTH topic_ops < dimword (:256) /\ eval_operands topic_ops s = SOME topics /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME len /\
  EVERY (\op. op_taint tn op = {}) (ptr_op::len_op::topic_ops) /\
  (w2n len <> 0 ==> ?v. ptr_op = Var v /\ ptr_covers G tn v s (w2n len)) /\
  (!i. w2n off <= i /\ i < w2n off + w2n len ==> i NOTIN tn.t_mem) /\
  ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx func G tn inst s
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all log_emit_access_taint >> strip_tac >>
  drule_all log_emit_step >> disch_tac >>
  simp[ptr_inst_ok_def, allocas_from_def] >> rpt strip_tac >>
  gvs[step_inst_non_invoke]
QED

Theorem log_emit_ghost_step:
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  step_prov PG G inst t = G /\ step_taint inst s t tn = tn
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, step_taint_def, mem_taint_def,
    set_var_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    taint_component_equality, DRESTRICT_UNIV, step_writes_def,
    source_memory_write_ranges_def, range_bytes_def, new_site_bytes_def] >>
  `!aid b sz. aid NOTIN FDOM s.vs_allocas ==> FLOOKUP s.vs_allocas aid <> SOME (b,sz)` by
    simp[FLOOKUP_DEF] >>
  `{i | ?aid b sz. aid NOTIN FDOM s.vs_allocas /\
      FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ b <= i /\ i < b+sz} = {}` by
    (simp[EXTENSION] >> metis_tac[]) >>
  asm_simp_tac bool_ss [UNION_EMPTY] >>
  Cases_on `inst.inst_operands` >> simp[written_taint_def] >>
  rpt (CASE_TAC >> simp[written_taint_def])
QED

Theorem log_emit_singleton_seq_ptr:
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\
  inst.inst_operands = Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op] /\
  LENGTH topic_ops < dimword (:256) /\ eval_operands topic_ops s = SOME topics /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME len /\
  EVERY (\op. op_taint tn op = {}) (ptr_op::len_op::topic_ops) /\
  (w2n len <> 0 ==> ?v. ptr_op = Var v /\ ptr_covers G tn v s (w2n len)) /\
  (!i. w2n off <= i /\ i < w2n off + w2n len ==> i NOTIN tn.t_mem) /\
  ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx ==>
  ?t. run_inst_seq [inst] s = OK t /\ inst_seq_ptr D 0 ctx func PG G tn [inst] s G tn /\
    (t with vs_logs := s.vs_logs) = s /\
    t.vs_logs = s.vs_logs ++ [<|logger := w2w s.vs_call_ctx.cc_address;
      topics := topics; data := mem_bytes_at (w2n off) (w2n len) s.vs_memory|>]
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all log_emit_step >> disch_tac >>
  `ptr_inst_ok D 0 0 ctx func G tn inst s` by
    (drule_all log_emit_inst_ok >> simp[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK t` >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp` by simp[Abbr `t`] >>
  drule_all log_emit_ghost_step >> strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn [inst] s G tn` by
    (drule_all inst_seq_ptr_singleton >> asm_simp_tac bool_ss []) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  simp[run_inst_seq_def, is_terminator_def, Abbr `t`]
QED

Theorem log_emit_singleton_path_ptr:
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\
  inst.inst_operands = Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op] /\
  LENGTH topic_ops < dimword (:256) /\ eval_operands topic_ops s = SOME topics /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME len /\
  EVERY (\op. op_taint tn op = {}) (ptr_op::len_op::topic_ops) /\
  (w2n len <> 0 ==> ?v. ptr_op = Var v /\ ptr_covers G tn v s (w2n len)) /\
  (!i. w2n off <= i /\ i < w2n off + w2n len ==> i NOTIN tn.t_mem) /\
  ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [inst] (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_ptr D 0 ctx func PG G tn s 0 G tn
      (OK (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
    (t with vs_logs := s.vs_logs) = s /\
    t.vs_logs = s.vs_logs ++ [<|logger := w2w s.vs_call_ctx.cc_address;
      topics := topics; data := mem_bytes_at (w2n off) (w2n len) s.vs_memory|>]
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all log_emit_singleton_seq_ptr >>
  disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) [inst]` by
    simp[is_terminator_def] >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_path_ptr >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[ADD1]
QED

Theorem log_emit_ghost_inv:
  ghost_inv d ce cx es G tn s ==>
  ghost_inv d ce cx (es with logs := es.logs ++ [ev]) G tn
    (s with vs_logs := s.vs_logs ++ [ev])
Proof
  strip_tac >> qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> Cases_on `d`
  >- (simp[ghost_inv_def, ptr_covers_def, lookup_var_def, stor_taint_ok_def,
       return_buf_ptr_def] >> metis_tac[]) >>
  PairCases_on `x` >>
  simp[ghost_inv_def, ptr_covers_def, lookup_var_def, stor_taint_ok_def,
    return_buf_ptr_def] >> metis_tac[]
QED

Theorem compile_log_emit_path_ptr:
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) [] sa = ((),sb) /\
  LENGTH topic_ops < dimword (:256) /\ eval_operands topic_ops s = SOME topics /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME len /\
  EVERY (\op. op_taint tn op = {}) (ptr_op::len_op::topic_ops) /\
  (w2n len <> 0 ==> ?v. ptr_op = Var v /\ ptr_covers G tn v s (w2n len)) /\
  (!i. w2n off <= i /\ i < w2n off + w2n len ==> i NOTIN tn.t_mem) /\
  stmt_state_rel ctx func ce cx es s /\ fresh_vars_wrt limit_st s /\
  ghost_inv d ce cx es G tn s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_ptr D 0 ctx func PG G tn s 0 G tn
      (OK (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
    stmt_state_rel ctx func ce cx (es with logs := es.logs ++
      [<|logger := w2w cx.txn.target; topics := topics;
        data := mem_bytes_at (w2n off) (w2n len) s.vs_memory|>])
      (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    ghost_inv d ce cx (es with logs := es.logs ++
      [<|logger := w2w cx.txn.target; topics := topics;
        data := mem_bytes_at (w2n off) (w2n len) s.vs_memory|>]) G tn
      (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    fresh_vars_wrt limit_st (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    (t with vs_logs := s.vs_logs) = s /\ inst_extends sa sb
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule emitted_insts_emit_inst >> strip_tac >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `isPREFIX [mk_inst sa.cs_next_id LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) []]
    (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  mp_tac (Q.INST [`sz` |-> `(len:bytes32)`,
    `data` |-> `mem_bytes_at (w2n (off:bytes32)) (w2n (len:bytes32)) s.vs_memory`]
    (SPEC_ALL log_emit_continuation)) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `t` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  suspend "emit"
QED
Resume compile_log_emit_path_ptr[emit]:
  markerLib.RESUME_TAC >>
  `ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst sa.cs_next_id LOG
      (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) []) s` by
    (irule log_emit_inst_ok >> simp[mk_inst_def] >> fs[EVERY_DEF]) >>
  qmatch_asmsub_abbrev_tac `ptr_inst_ok D 0 0 ctx func G tn i s` >>
  `i.inst_opcode = LOG /\ i.inst_outputs = []` by simp[Abbr `i`, mk_inst_def] >>
  `run_inst_seq [i] s = OK t` by metis_tac[] >>
  `step_inst_base i s = OK t` by
    (qpat_x_assum `run_inst_seq [i] s = OK t` mp_tac >>
     simp[run_inst_seq_def, is_terminator_def, AllCaseEqs()]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp` by
    (qpat_assum `t with vs_logs := s.vs_logs = s`
      (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  drule_all log_emit_ghost_step >> strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn [i] s G tn` by
    (drule_all inst_seq_ptr_singleton >> asm_simp_tac bool_ss []) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) [i]` by
    simp[is_terminator_def] >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_path_ptr >>
  simp[] >> disch_tac >>
  suspend "post"
QED
Resume compile_log_emit_path_ptr[post]:
  markerLib.RESUME_TAC >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `t = s with vs_logs := s.vs_logs ++
    [<|logger := w2w cx.txn.target; topics := topics;
      data := mem_bytes_at (w2n off) (w2n len) s.vs_memory|>]` by
    (`i.inst_operands = Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]` by
       simp[Abbr `i`, mk_inst_def] >>
     drule_all log_emit_step >> asm_simp_tac bool_ss [] >>
     simp[] >> metis_tac[]) >>
  qexists_tac `t` >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by metis_tac[ADD1] >>
  asm_simp_tac bool_ss [stmt_state_rel_inst_idx,
    PURE_REWRITE_RULE [ghost_inv_gas_obs] literal_ptr_ghost_inv_normalize] >>
  conj_tac
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with logs := _) t` mp_tac >>
      asm_simp_tac bool_ss [w2w_id]) >>
  conj_tac
  >- (qpat_x_assum `t = _` SUBST_ALL_TAC >>
      simp_tac bool_ss [w2w_id] >> irule log_emit_ghost_inv >> first_assum ACCEPT_TAC) >>
  fs[fresh_vars_wrt_def]
QED
Finalise compile_log_emit_path_ptr
