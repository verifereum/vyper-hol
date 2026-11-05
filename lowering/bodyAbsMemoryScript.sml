(* Memory-safe unary lowering. *)
Theory bodyAbsMemory
Ancestors
  exprSimSource exprSimHypsDefs exprSimProps exprSimUnopProps
  exprSimMemoryStack exprSimMemoryValues exprSimMemDefs loweringPosts
  gasNormalPrefix gasSummary gasSummaryCompose gasContext gasCount fragGasMode
  fragGasPathMem fragGasSeqMem gasExemptCert
  bodyMemoryDefs emitHelperProps fragExecMem instMemFrontier allocaHistoryFragment
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  compileEnv fragExec exprSimDefs valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState vyperExprNoControl
  builtinSimple builtinProps freshWrites varsExt vyperTyping vyperValueOperation integer_word

Theorem body_unop_no_ranges_seq[local]:
  !is s. EVERY (\i. !q. inst_mem_below_frontier i q) is ==>
         run_inst_seq_mem_ok is s
Proof
  Induct >> simp[run_inst_seq_mem_ok_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> simp[]
QED

Theorem body_abs_prefix_mem_ok:
  compile_builtin_abs x sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  strip_tac >> irule body_unop_no_ranges_seq >>
  gvs[builtinSimpleTheory.compile_builtin_abs_def,
      builtinSimpleTheory.compile_select_def,
      comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def,
      emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem body_abs_shape[local]:
  compile_builtin_abs x sm = (dst,sn) ==>
  sn.cs_blocks = sm.cs_blocks /\ sn.cs_current_bb = sm.cs_current_bb /\
  sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
  sm.cs_next_var <= sn.cs_next_var /\
  writes_fresh sm (emitted_insts sm sn) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_ext_call_op i.inst_opcode) (emitted_insts sm sn)
Proof
  strip_tac >> mp_tac (Q.SPEC `x` straight_fresh_abs) >>
  rewrite_tac[straight_fresh_def] >> disch_then drule >> strip_tac >>
  simp[] >> gvs[writes_fresh_def, EVERY_MEM] >>
  metis_tac[fresh_write_op_simple]
QED

Theorem body_abs_run[local]:
  compile_builtin_abs x sm = (dst,sn) /\ eval_operand x s = SOME w /\
  (!z. x = Var z ==> not_fresh_at sm z) ==>
  (w <> INT_MINw ==>
   ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
       eval_operand dst q = SOME (if word_msb w then 0w - w else w)) /\
  (w = INT_MINw ==>
   ?q. run_inst_seq (emitted_insts sm sn) s = Abort Revert_abort q)
Proof
  strip_tac >> drule body_abs_shape >> strip_tac >>
  `eval_operand x (drop_fresh sm s) = SOME w` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sm (drop_fresh sm s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all compile_builtin_abs_run >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sm sn) (drop_fresh sm s))
                   (run_inst_seq (emitted_insts sm sn) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh, EVERY_MEM] >>
     gvs[EVERY_MEM]) >>
  conj_tac >> strip_tac >> gvs[vars_ext_result_def] >>
  gvs[vars_ext_def] >> drule eval_operand_vars_ext >>
  disch_then (qspec_then `dst` mp_tac) >> simp[] >>
  qpat_x_assum `t' = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem body_abs_history[local]:
  compile_builtin_abs x sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  rpt strip_tac >> drule body_abs_shape >> strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sn ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sn) = LENGTH sn.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[] >>
     gvs[EVERY_MEM]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem body_abs_state_post[local]:
  compile_builtin_abs x sm = (dst,sn) /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s /\
  run_inst_seq (emitted_insts sm sn) s = OK q ==>
  stmt_state_rel ctx func cenv cx es q /\
  (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
         lookup_var z q = SOME v) /\
  q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
  q.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule body_abs_shape >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `q = _` (fn th => once_rewrite_tac[th]) >>
      irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
      `not_fresh_at sm p` by
        (gvs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) >>
      simp[lookup_var_def]) >>
  qpat_x_assum `q = _` (fn th => once_rewrite_tac[th]) >>
  simp[lookup_var_def]
QED

Theorem body_abs_frag_mem_at[local]:
  compile_builtin_abs x sm = (dst,sn) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  (w = INT_MINw ==> !q. R (Abort Revert_abort q)) ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand x s = SOME w /\ alloca_history func s)
    (\s. w <> INT_MINw /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (if word_msb w then 0w - w else w) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  strip_tac >> drule body_abs_shape >> strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
    eval_operand x s = SOME w /\ alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sn P
    (\s. w <> INT_MINw /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (if word_msb w then 0w - w else w) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R`
    suffices_by (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >> simp[IS_PREFIX_APPEND3] >>
  reverse conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac >- metis_tac[body_abs_prefix_mem_ok] >>
  drule_all body_abs_run >> strip_tac >>
  Cases_on `w = INT_MINw`
  >- (gvs[] >> disj2_tac >> metis_tac[]) >>
  gvs[] >>
  drule_all body_abs_state_post >> strip_tac >>
  `alloca_inv entry` by gvs[stmt_state_rel_def] >>
  drule_all body_abs_history >> strip_tac >>
  gvs[stmt_state_rel_inst_idx, lookup_var_def, eval_operand_def]
QED

Theorem body_abs_tail_mem[local]:
  compile_builtin_abs x sm = (op,sb) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  value_has_type (BaseTV (IntT 256)) v1 /\ expr_type e = BaseT (IntT 256) /\
  sa.cs_next_var <= sm.cs_next_var /\
  expr_post ctx func cenv cx e es sa sm s0 es' v1 x entry /\
  alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
  res = unop_result cx (BaseT (IntT 256)) Abs [expr_type e] v1 es' ==>
  frag_exec_mem ctx sm sb (\s. s = entry)
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx (Builtin (BaseT (IntT 256)) Abs [e]) es
           sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit res)
Proof
  strip_tac >> Cases_on `v1` >> gvs[value_has_type_def] >>
  rename1 `within_int_bound _ i` >>
  drule int256_abs_bound >> strip_tac >> drule_all abs_i2w >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' entry /\
   eval_operand x entry = SOME (integer_word$i2w i : bytes32)` by
    gvs[expr_post_def, expr_val_rel_def, vyperValueTheory.evaluate_type_def,
        typed_val_to_w256_def, val_to_w256_def, is_word_type_def] >>
  `i2w i = (INT_MINw : bytes32) ==>
   !q. expr_exit (unop_result cx (BaseT (IntT 256)) Abs [expr_type e] (IntV i) es')
          (Abort Revert_abort q)` by
    (strip_tac >> gvs[unop_result_def, vyperContextTheory.evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def, vyperValueOperationTheory.bounded_int_op_def,
       expr_exit_def]) >>
  drule_all body_abs_frag_mem_at >>
  disch_then (qspecl_then
    [`es'`, `entry`, `cx`, `ctx`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  Cases_on `i = INT_MIN (:256)`
  >- gvs[unop_result_def, vyperContextTheory.evaluate_builtin_def,
         vyperASTTheory.type_to_int_bound_def, vyperValueOperationTheory.bounded_int_op_def] >>
  simp[unop_result_def, vyperContextTheory.evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def, vyperValueOperationTheory.bounded_int_op_def] >>
  irule expr_post_unop >> simp[is_word_type_def] >>
  conj_tac
  >- gvs[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
         typed_val_to_w256_def, val_to_w256_def, is_word_type_def] >>
  qexistsl_tac [`sm`, `entry`, `IntV i`, `x`] >> simp[]
QED

Theorem compile_abs_sim_mem:
  expr_type e = BaseT (IntT 256) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx ty e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin (BaseT (IntT 256)) Abs [e]) es
Proof
  strip_tac >> simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule lower_value_abs >> strip_tac >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   (!z. x = Var z ==> not_fresh_at s1 z)` by
    (drule expr_body_pre_lower_value_word_shape >>
     disch_then drule >> simp[is_word_type_def]) >>
  `cs_extends s1 sb` by
    (drule_at Any straight_fresh_cs_extends >> simp[straight_fresh_abs]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `builtin_args_length_ok Abs 1 /\ Abs <> Len` by
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
  `value_has_type (BaseTV (IntT 256)) v1` by
    (drule expr_body_pre_word_value >>
     simp[is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
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
  irule body_abs_tail_mem >> simp[] >> qexistsl_tac [`v1`, `x`] >> simp[]
QED

Theorem compile_abs_vv_sim_mem:
  expr_type e = BaseT (IntT 256) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx ty e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin (BaseT (IntT 256)) Abs [e]) es
Proof
  strip_tac >> irule body_expr_vv_sim_mem_stack >>
  conj_tac >- simp[compile_not_abs_stack] >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  irule compile_abs_sim_mem >> simp[] >> qexists_tac `env` >> simp[]
QED

