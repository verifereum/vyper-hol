(* Memory-safe unary lowering. *)
Theory bodyNotFlagMemory
Ancestors
  exprSimSource exprSimHypsDefs exprSimProps exprSimUnopProps
  exprSimMemoryStack exprSimMemoryValues exprSimMemDefs loweringPosts
  gasNormalPrefix gasSummary gasSummaryCompose gasContext gasCount fragGasMode
  fragGasPathMem fragGasSeqMem gasExemptCert
  bodyMemoryDefs emitHelperProps fragExecMem instMemFrontier allocaHistoryFragment
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  compileEnv fragExec exprSimDefs valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState vyperExprNoControl
  builtinSimple freshWrites varsExt vyperTyping vyperValueOperation integer_word

Theorem body_xor_prefix_mem_ok:
  emit_op XOR ops sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem body_xor_run:
  emit_op XOR [x; Lit mask] sm = (dst,sn) /\ eval_operand x s = SOME w ==>
  run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var)) (word_xor w mask) s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_def] >> drule step_XOR >>
  disch_then (qspec_then `Lit mask` mp_tac) >> simp[eval_operand_def]
QED

Theorem body_xor_history:
  emit_op XOR ops sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  rpt strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sn ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sn) = LENGTH sn.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem body_xor_state_post:
  emit_op XOR [x; Lit mask] sm = (dst,sn) /\ eval_operand x s = SOME w /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s ==>
  ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
      stmt_state_rel ctx func cenv cx es q /\
      eval_operand dst q = SOME (word_xor w mask) /\
      (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
             lookup_var z q = SOME v) /\
      q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
      q.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> drule_all body_xor_run >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qexists_tac `update_var out (word_xor w mask) s` >>
  simp[Abbr `out`] >> conj_tac
  >- (irule stmt_state_rel_update_var >> simp[]) >>
  `dst = Var (STRING #"%" (toString sm.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  gvs[] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem body_xor_frag_mem_at:
  emit_op XOR [x; Lit mask] sm = (dst,sn) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand x s = SOME w /\ alloca_history func s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (word_xor w mask) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
    eval_operand x s = SOME w /\ alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sn P
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (word_xor w mask) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R`
    suffices_by (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >> fs[same_blocks_def] >>
  simp[IS_PREFIX_APPEND3, mk_inst_def, is_terminator_def] >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac
  >- (simp[GSYM mk_inst_def, run_inst_seq_mem_ok_last] >>
      irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  disj1_tac >> drule_all body_xor_state_post >> strip_tac >>
  `alloca_inv entry` by gvs[stmt_state_rel_def] >>
  drule_all body_xor_history >> strip_tac >>
  qexists_tac `q` >>
  fs[GSYM mk_inst_def, stmt_state_rel_inst_idx, lookup_var_def] >>
  qpat_x_assum `run_inst_seq _ _ = OK q` mp_tac >>
  qpat_x_assum `alloca_history func (q with vs_inst_idx := _)` mp_tac >>
  simp[]
QED

Theorem body_not_flag_tail_mem[local]:
  emit_op XOR [x; Lit (n2w (2 ** m - 1))] sm = (op,sb) /\
  local_ptrs_reserved cenv sm /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  evaluate_type (get_tenv cx) (FlagT nsid) = SOME (FlagTV m) /\
  value_has_type (FlagTV m) v1 /\ expr_type e = FlagT nsid /\
  sa.cs_next_var <= sm.cs_next_var /\
  expr_post ctx func cenv cx e es sa sm s0 es' v1 x entry /\
  alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
  res = unop_result cx (FlagT nsid) Not [expr_type e] v1 es' ==>
  frag_exec_mem ctx sm sb (\s. s = entry)
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx (Builtin (FlagT nsid) Not [e]) es
           sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit res)
Proof
  strip_tac >> Cases_on `v1` >> gvs[value_has_type_def] >>
  rename1 `k < 2 ** m` >>
  `stmt_state_rel ctx func cenv cx es' entry /\
   eval_operand x entry = SOME (n2w k)` by
    gvs[expr_post_def, expr_val_rel_def, typed_val_to_w256_def,
        val_to_w256_def, is_word_type_def] >>
  drule_all body_xor_frag_mem_at >>
  disch_then (qspecl_then
    [`n2w k : bytes32`, `es'`, `entry`, `cx`, `ctx`,
     `expr_exit (unop_result cx (FlagT nsid) Not [expr_type e] (FlagV k) es')`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  gvs[unop_result_def, vyperContextTheory.evaluate_builtin_def,
       vyperValueTheory.evaluate_type_def, AllCaseEqs(), expr_exit_def] >>
  irule expr_post_unop >> simp[is_word_type_def] >>
  conj_tac
  >- gvs[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
         typed_val_to_w256_def, val_to_w256_def, is_word_type_def, flag_not_xor] >>
  qexistsl_tac [`sm`, `entry`, `FlagV k`, `x`] >> simp[]
QED

Theorem compile_not_flag_sim_mem:
  is_flag_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  strip_tac >>
  `?nsid. expr_type e = FlagT nsid` by (Cases_on `expr_type e` >> gvs[]) >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule lower_value_not >> strip_tac >> gvs[compile_invert_def] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   (!z. x = Var z ==> not_fresh_at s1 z)` by
    (drule expr_body_pre_lower_value_word_shape >>
     disch_then drule >> simp[is_word_type_def]) >>
  `cs_extends s1 sb` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `builtin_args_length_ok Not 1 /\ Not <> Len` by
    simp[vyperContextTheory.builtin_args_length_ok_def] >>
  drule_all eval_expr_unop_cases >> strip_tac
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `x`, `INR exc`, `es'`, `s0`] mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
      disch_then (qspecl_then
        [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
         `\s. F`, `expr_exit res`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      irule frag_exec_mem_exit_prefix >> qexists_tac `s1` >> simp[]) >>
  `?m. evaluate_type (get_tenv cx) (FlagT nsid) = SOME (FlagTV m) /\
       value_has_type (FlagTV m) v1 /\
       cenv.ce_flag_n_members (nsid_to_string nsid) = m` by
    (drule expr_body_pre_word_value >> simp[is_word_type_def] >>
     strip_tac >> gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `INL v1`, `es'`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_pre_exit_c) >>
  disch_then (qspecl_then
    [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
     `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_mem_then th)) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  irule body_not_flag_tail_mem >> simp[] >> qexistsl_tac [`v1`, `x`] >> simp[]
QED

Theorem compile_not_flag_vv_sim_mem:
  is_flag_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  strip_tac >> irule body_expr_vv_sim_mem_stack >>
  conj_tac >- simp[compile_not_abs_stack] >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  irule compile_not_flag_sim_mem >> simp[] >> qexists_tac `env` >> simp[]
QED

