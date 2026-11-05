Theory bodyPtrBopCompareSuffix
Ancestors
  bodyPtrBopCompareCompile bodyPtrBopHashSuffix bodyPtrBopHashFrame exprLoweringProps
  emitHelperProps venomState venomInst instIdxIndep fragExec
  fragGasPathPtr codegenRel compileEnv arithmetic rich_list exprLowering emitHelper exprSimHash

Theorem bop_compare_pair_run_split:
  emit_op opc1 ops1 sc = (a,sd) /\ emit_op opc2 ops2 sd = (b,se) /\
  ~is_terminator opc2 /\ fn_has_code sc se fn /\
  run_inst_seq (emitted_insts sc se) s = OK t ==>
  ?u. run_inst_seq (emitted_insts sc sd) s = OK u /\
    run_inst_seq (emitted_insts sd se)
      (u with vs_inst_idx := LENGTH sd.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    fn_has_code sc sd fn /\ fn_has_code sd se fn
Proof
  strip_tac >> imp_res_tac bop_compare_emit_layout >>
  `emitted_insts sc se = emitted_insts sc sd ++ emitted_insts sd se` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `fn_has_code sc sd fn /\ fn_has_code sd se fn` by
    (irule fn_has_code_split >> simp[]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  pure_asm_rewrite_tac[bop_run_inst_seq_append_ok] >> strip_tac >>
  qexists_tac `u` >> simp[] >>
  drule_all bop_compare_emit_run_cursor >> simp[]
QED

Theorem bop_noteq_emit_ptr:
  emit_op EQ [left;right] sc = (eq,sd) /\ emit_op ISZERO [eq] sd = (op,se) /\
  fn_has_code sc se fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sc se) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := s.vs_inst_idx + 2)) /\
  op_prov G' op = NONE /\ op_taint tn' op = {} /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  (!x. not_fresh_at sc x ==> FLOOKUP G' x = FLOOKUP G x /\
    FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `~is_terminator ISZERO` by simp[is_terminator_def] >>
  drule_all bop_compare_pair_run_split >> strip_tac >>
  drule_all bop_eq_emit_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  imp_res_tac bop_compare_emit_layout >>
  drule_all (GEN_ALL (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `EQ`, `ops` |-> `[left;right]`]
      (SPEC_ALL bop_compare_emit_readonly)))) >> strip_tac >>
  `u.vs_current_bb = sd.cs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `(u with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  drule_all (GEN_ALL (SIMP_RULE (srw_ss()) []
    (Q.INST [`s` |-> `v with vs_inst_idx := LENGTH sc.cs_current_insts`,
             `t` |-> `w with vs_inst_idx := LENGTH sc.cs_current_insts`]
      (SPEC_ALL bop_iszero_emit_ptr)))) >>
  disch_then (qspecl_then [`PG`, `G'`, `D`] strip_assume_tac) >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  `!x. not_fresh_at sc x ==> not_fresh_at sd x` by
    (imp_res_tac emitted_insts_emit_op >> fs[not_fresh_at_def] >>
     metis_tac[LESS_EQ_TRANS, DECIDE ``n <= n + 1``]) >>
  qexistsl_tac [`G''`, `tn''`] >> fs[] >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL gas_path_ptr_then))) >>
  qexistsl_tac [`G'`, `u with vs_inst_idx := LENGTH sd.cs_current_insts`, `tn'`] >>
  fs[ADD_ASSOC, ADD1] >> gvs[ADD1]
QED

Theorem bop_compile_compare_ptr:
  (bop = Eq \/ bop = NotEq) /\
  compile_compare bop left right ty sc = (op,sd) /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sd.cs_current_insts)) /\
  op_prov G' op = NONE /\ op_taint tn' op = {} /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  (!x. not_fresh_at sc x ==> FLOOKUP G' x = FLOOKUP G x /\
    FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> gvs[compile_compare_def, comp_bind_def, AllCaseEqs()]
  >- (drule_all bop_eq_emit_ptr >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      imp_res_tac bop_compare_emit_layout >>
      qexistsl_tac [`G'`, `tn'`] >> gvs[ADD1]) >>
  pairarg_tac >> gvs[] >>
  drule_all bop_noteq_emit_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  imp_res_tac bop_compare_emit_layout >>
  qexistsl_tac [`G'`, `tn'`] >> gvs[ADD_ASSOC]
QED

Theorem bop_compile_compare_layout:
  (bop = Eq \/ bop = NotEq) /\
  compile_compare bop left right ty sc = (op,sd) ==>
  inst_extends sc sd /\ cs_extends sc sd /\
  sd.cs_current_bb = sc.cs_current_bb /\
  sc.cs_next_var <= sd.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sd)
Proof
  strip_tac >>
  gvs[compile_compare_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND,
       mk_inst_def, is_terminator_def, cs_extends_def, APPEND_ASSOC,
       IS_PREFIX_APPEND] >>
  pure_once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def]
QED

Theorem bop_compile_compare_run_cursor:
  (bop = Eq \/ bop = NotEq) /\
  compile_compare bop left right ty sc = (op,sd) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  run_inst_seq (emitted_insts sc sd) (s with vs_inst_idx := idx) =
    OK (t with vs_inst_idx := idx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_compile_compare_layout >> strip_tac >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`s`, `idx`] mp_tac) >> simp[exec_result_map_def]
QED

Theorem bop_hash_pair_readonly:
  compile_bytestring_hash (Var p) sc = (h1,sd) /\
  compile_bytestring_hash (Var r) sd = (h2,se) /\
  not_fresh_at sc p /\ not_fresh_at sc r /\
  lookup_var p s = SOME w1 /\ lookup_var r s = SOME w2 /\
  run_inst_seq (emitted_insts sc se) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s
Proof
  strip_tac >> imp_res_tac bop_hash_compile_layout >>
  `emitted_insts sc se = emitted_insts sc sd ++ emitted_insts sd se` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  pure_asm_rewrite_tac[bop_run_inst_seq_append_ok] >> strip_tac >>
  `not_fresh_at sd r` by fs[not_fresh_at_def] >>
  drule_all bop_hash_compile_run_frame >> strip_tac >>
  `lookup_var r u = SOME w2` by fs[lookup_var_def] >>
  imp_res_tac bop_hash_compile_readonly >>
  fs[venom_state_component_equality] >> metis_tac[]
QED

Theorem bop_compare_suffix_run_split:
  inst_extends sc se /\ cs_extends sc se /\
  (bop = Eq \/ bop = NotEq) /\
  compile_compare bop h1 h2 ty se = (op,sf) /\ fn_has_code sc sf fn /\
  run_inst_seq (emitted_insts sc sf) s = OK t ==>
  ?u. run_inst_seq (emitted_insts sc se) s = OK u /\
    run_inst_seq (emitted_insts se sf)
      (u with vs_inst_idx := LENGTH se.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH se.cs_current_insts) /\
    fn_has_code sc se fn /\ fn_has_code se sf fn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_compile_compare_layout >> strip_tac >>
  `emitted_insts sc sf = emitted_insts sc se ++ emitted_insts se sf` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `fn_has_code sc se fn /\ fn_has_code se sf fn` by
    (irule fn_has_code_split >> simp[]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  pure_asm_rewrite_tac[bop_run_inst_seq_append_ok] >> strip_tac >>
  qexists_tac `u` >> simp[] >>
  drule_all bop_compile_compare_run_cursor >> simp[]
QED
