(* Actual Neg opcode suffix; independent of source numeric correctness. *)
Theory bodyNegMemory
Ancestors
  exprSimUnopProps exprSimHypsDefs exprSimProps exprSimMemoryStack
  exprSimMemoryValues exprSimMemDefs loweringPosts gasNormalPrefix gasSummary
  gasSummaryCompose gasContext gasCount fragGasMode fragGasPathMem fragGasSeqMem gasExemptCert
  exprSimUnopProps
  exprSimSource
  bodyMemoryDefs   emitHelperProps
  fragExecMem instMemFrontier allocaHistoryFragment
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  compileEnv fragExec exprSimDefs valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState freshWrites varsExt integer_word
  arithmeticProps vyperArith vyperTypeSystem vyperTyping
  exprBopLowering

Theorem body_neg_no_ranges_seq[local]:
  !is s. EVERY (\i. !q. inst_mem_below_frontier i q) is ==>
         run_inst_seq_mem_ok is s
Proof
  Induct >> simp[run_inst_seq_mem_ok_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> simp[]
QED

Theorem body_neg_prefix_mem_ok:
  compile_neg x ty sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  strip_tac >> irule body_neg_no_ranges_seq >>
  gvs[compile_neg_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def,
      emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem body_neg_emitted:
  compile_neg x ty sm = (dst,sn) ==>
  emitted_insts sm sn =
    [mk_inst sm.cs_next_id SGT [x; Lit (FST (type_bounds ty))]
       ["%" ++ toString sm.cs_next_var];
     mk_inst (sm.cs_next_id + 1) ASSERT [Var ("%" ++ toString sm.cs_next_var)] [];
     mk_inst (sm.cs_next_id + 2) SUB [Lit 0w; x]
       ["%" ++ toString (sm.cs_next_var + 1)]]
Proof
  strip_tac >>
  gvs[compile_neg_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def,
      emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem body_neg_straight_fresh[local]:
  straight_fresh (compile_neg x ty)
Proof
  Cases_on `type_bounds ty` >> simp[compile_neg_def] >>
  irule straight_fresh_bind >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule straight_fresh_ignore_bind >>
      simp[straight_fresh_emit_void, straight_fresh_emit_op, fresh_write_op_def]) >>
  simp[straight_fresh_emit_op, fresh_write_op_def]
QED

Theorem body_neg_shape:
  compile_neg x ty sm = (dst,sn) ==>
  sn.cs_blocks = sm.cs_blocks /\ sn.cs_current_bb = sm.cs_current_bb /\
  sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
  sm.cs_next_var <= sn.cs_next_var /\
  writes_fresh sm (emitted_insts sm sn) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_ext_call_op i.inst_opcode) (emitted_insts sm sn)
Proof
  strip_tac >> mp_tac body_neg_straight_fresh >>
  rewrite_tac[straight_fresh_def] >> disch_then drule >> strip_tac >>
  simp[] >> gvs[writes_fresh_def, EVERY_MEM] >>
  metis_tac[fresh_write_op_simple]
QED

Theorem body_neg_history:
  compile_neg x ty sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  rpt strip_tac >> drule body_neg_shape >> strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sn ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sn) = LENGTH sn.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[] >> gvs[EVERY_MEM]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem body_neg_state_post:
  compile_neg x ty sm = (dst,sn) /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s /\
  run_inst_seq (emitted_insts sm sn) s = OK q ==>
  stmt_state_rel ctx func cenv cx es q /\
  (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
         lookup_var z q = SOME v) /\
  q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
  q.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule body_neg_shape >> strip_tac >>
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

Theorem body_neg_result:
  compile_neg x ty sm = (dst,sn) ==>
  dst = Var ("%" ++ toString (sm.cs_next_var + 1))
Proof
  strip_tac >>
  gvs[compile_neg_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def]
QED

Theorem body_neg_old_operand[local]:
  (!z. x = Var z ==> not_fresh_at sm z) ==>
  eval_operand x (update_var ("%" ++ toString sm.cs_next_var) v s) =
  eval_operand x s
Proof
  Cases_on `x` >> simp[eval_operand_def, lookup_var_update_var] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]
QED

Theorem body_neg_run:
  compile_neg x ty sm = (dst,sn) /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ eval_operand x s = SOME w ==>
  (word_gt w (FST (type_bounds ty)) ==>
    ?t. run_inst_seq (emitted_insts sm sn) s = OK t /\
        eval_operand dst t = SOME (0w - w)) /\
  (~word_gt w (FST (type_bounds ty)) ==>
    run_inst_seq (emitted_insts sm sn) s =
      Abort Revert_abort (revert_state (set_returndata []
        (update_var ("%" ++ toString sm.cs_next_var) 0w s))))
Proof
  strip_tac >> drule body_neg_emitted >> strip_tac >>
  drule body_neg_result >> strip_tac >>
  `!v. eval_operand x (update_var ("%" ++ toString sm.cs_next_var) v s) = SOME w`
    by (gen_tac >> drule body_neg_old_operand >> simp[]) >>
  `step_inst_base
     (mk_inst sm.cs_next_id SGT [x; Lit (FST (type_bounds ty))]
       ["%" ++ toString sm.cs_next_var]) s =
    OK (update_var ("%" ++ toString sm.cs_next_var)
      (bool_to_word (word_gt w (FST (type_bounds ty)))) s)` by
    (irule step_SGT >> simp[eval_operand_lit]) >>
  `!v. step_inst_base
    (mk_inst (sm.cs_next_id + 2) SUB [Lit 0w; x]
      ["%" ++ toString (sm.cs_next_var + 1)])
    (update_var ("%" ++ toString sm.cs_next_var) v s) =
    OK (update_var ("%" ++ toString (sm.cs_next_var + 1)) (0w - w)
      (update_var ("%" ++ toString sm.cs_next_var) v s))` by
    (gen_tac >> irule step_SUB >> simp[eval_operand_lit]) >>
  gvs[] >> simp[run_inst_seq_def] >>
  conj_tac >> strip_tac >>
  simp[bool_to_word_def, run_inst_seq_def, step_ASSERT_ok, step_ASSERT_revert,
       step_SUB, eval_operand_lit, eval_operand_def, lookup_var_update_var]
QED

Theorem body_neg_frag_mem_at:
  compile_neg x ty sm = (dst,sn) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  (~word_gt w (FST (type_bounds ty)) ==> !q. R (Abort Revert_abort q)) ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand x s = SOME w /\ alloca_history func s)
    (\s. word_gt w (FST (type_bounds ty)) /\
         stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (0w - w) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  strip_tac >> drule body_neg_shape >> strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
    eval_operand x s = SOME w /\ alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sn P
    (\s. word_gt w (FST (type_bounds ty)) /\
         stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (0w - w) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R`
    suffices_by (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >> simp[IS_PREFIX_APPEND3] >>
  reverse conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac >- metis_tac[body_neg_prefix_mem_ok] >>
  drule_all body_neg_run >> strip_tac >>
  Cases_on `word_gt w (FST (type_bounds ty))`
  >- (gvs[] >> drule_all body_neg_state_post >> strip_tac >>
      `alloca_inv entry` by gvs[stmt_state_rel_def] >>
      drule_all body_neg_history >> strip_tac >>
      gvs[stmt_state_rel_inst_idx, lookup_var_def, eval_operand_def]) >>
  gvs[] >> disj2_tac >> metis_tac[]
QED

Theorem body_neg_signed_interval:
  0 < n ==>
  (within_int_bound (Signed n) i <=>
   -&(2 ** (n - 1)) <= i /\ i < &(2 ** (n - 1)))
Proof
  strip_tac >> simp[within_int_bound_def] >>
  Cases_on `i < 0` >> simp[]
  >- (`0 <= -i` by intLib.ARITH_TAC >>
      simp[Once (GSYM integerTheory.INT_OF_NUM)] >>
      `0 <= &(2 ** (n - 1))` by simp[] >>
      eq_tac >> strip_tac >> intLib.ARITH_TAC) >>
  `0 <= i` by intLib.ARITH_TAC >>
  simp[Once (GSYM integerTheory.INT_OF_NUM)] >>
  `0 <= &(2 ** (n - 1))` by simp[] >>
  eq_tac >> strip_tac >> intLib.ARITH_TAC
QED

Theorem body_neg_signed_comparison:
  0 < n /\ n <= 256 /\ within_int_bound (Signed n) i ==>
  (word_gt (i2w i : bytes32) (i2w (-&(2 ** (n - 1)))) <=>
   within_int_bound (Signed n) (-i))
Proof
  strip_tac >>
  `n - 1 <= 255` by decide_tac >>
  drule w2i_i2w_neg_pow2 >> strip_tac >>
  drule_all w2i_i2w_within_signed >> strip_tac >>
  simp[integer_wordTheory.WORD_GTi] >>
  gvs[body_neg_signed_interval] >> intLib.ARITH_TAC
QED

Theorem body_neg_source_value:
  is_numeric_type ann /\ ~is_uint_type ann /\
  0 < type_bits ann /\ type_bits ann <= 256 /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  word_gt (typed_val_to_w256 tv v) (FST (type_bounds ann)) ==>
  ?out. unop_result cx ann Neg [ann] v es = INL out /\
        value_has_type tv out /\
        typed_val_to_w256 tv out = 0w - typed_val_to_w256 tv v
Proof
  Cases_on `ann` >> simp[is_numeric_type_def, is_int_type_def, is_uint_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >>
  simp[is_int_type_def, is_uint_type_def] >> rpt strip_tac >>
  Cases_on `v` >>
  gvs[type_bits_def, evaluate_type_def, value_has_type_def,
      type_bounds_def, is_signed_type_def, typed_val_to_w256_def,
      val_to_w256_def]
  >- (`0 < n` by decide_tac >>
      drule_all body_neg_signed_comparison >> strip_tac >> gvs[] >>
      simp[unop_result_def, vyperContextTheory.evaluate_builtin_def,
           vyperASTTheory.type_to_int_bound_def,
           vyperValueOperationTheory.bounded_int_op_def,
           value_has_type_def, typed_val_to_w256_def, val_to_w256_def,
           GSYM word_i2w_neg, wordsTheory.WORD_SUB_LZERO]) >>
  `within_int_bound (Signed 168) (-i)` by
    (qspec_then `168` mp_tac (GEN_ALL body_neg_signed_comparison) >>
     simp[] >> disch_then drule >> simp[]) >>
  simp[unop_result_def, vyperContextTheory.evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def,
       vyperValueOperationTheory.bounded_int_op_def,
       vyperValueOperationTheory.bounded_decimal_op_def,
       decimal_bound_def, value_has_type_def, typed_val_to_w256_def,
       val_to_w256_def, GSYM word_i2w_neg, wordsTheory.WORD_SUB_LZERO]
QED

Theorem body_neg_source_abort:
  is_numeric_type ann /\ ~is_uint_type ann /\
  0 < type_bits ann /\ type_bits ann <= 256 /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  ~word_gt (typed_val_to_w256 tv v) (FST (type_bounds ann)) ==>
  !q. expr_exit (unop_result cx ann Neg [ann] v es) (Abort Revert_abort q)
Proof
  Cases_on `ann` >> simp[is_numeric_type_def, is_int_type_def, is_uint_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >>
  simp[is_int_type_def, is_uint_type_def] >> rpt strip_tac >>
  Cases_on `v` >>
  gvs[type_bits_def, evaluate_type_def, value_has_type_def,
      type_bounds_def, is_signed_type_def, typed_val_to_w256_def,
      val_to_w256_def]
  >- (`0 < n` by decide_tac >>
      drule_all body_neg_signed_comparison >> strip_tac >> gvs[] >>
      simp[unop_result_def, vyperContextTheory.evaluate_builtin_def,
           vyperASTTheory.type_to_int_bound_def,
           vyperValueOperationTheory.bounded_int_op_def, expr_exit_def]) >>
  `~within_int_bound (Signed 168) (-i)` by
    (qspec_then `168` mp_tac (GEN_ALL body_neg_signed_comparison) >>
     simp[] >> disch_then drule >> simp[]) >>
  simp[unop_result_def, vyperContextTheory.evaluate_builtin_def,
       vyperValueOperationTheory.bounded_decimal_op_def,
       decimal_bound_def, expr_exit_def]
QED

Theorem expr_body_pre_neg:
  expr_body_pre cenv cx env (Builtin ann Neg [e]) es ==>
  ann = expr_type e /\ expr_body_pre cenv cx env e es /\
  is_numeric_type ann /\ ~is_uint_type ann /\
  0 < type_bits ann /\ type_bits ann <= 256 /\ is_word_type ann
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> simp[] >>
     qexistsl_tac [`ann`, `[e]`, `Neg`, `es`] >> simp[]) >>
  `ann = expr_type e /\ is_numeric_type ann /\ ~is_uint_type ann /\
   well_formed_type env.type_defs ann` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  `0 < type_bits ann /\ type_bits ann <= 256 /\ is_word_type ann` by
    (qpat_x_assum `ann = expr_type e` kall_tac >>
     Cases_on `ann` >> gvs[is_numeric_type_def, is_int_type_def, is_uint_type_def] >>
     rename1 `BaseT b` >> Cases_on `b` >>
     gvs[is_numeric_type_def, is_int_type_def, is_uint_type_def, type_bits_def,
         is_word_type_def, well_formed_type_def, evaluate_type_def,
         expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def]) >>
  simp[]
QED

Theorem body_neg_tail_mem:
  compile_neg x ann sm = (op,sb) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  is_numeric_type ann /\ ~is_uint_type ann /\ is_word_type ann /\
  0 < type_bits ann /\ type_bits ann <= 256 /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v1 /\
  expr_type e = ann /\ sa.cs_next_var <= sm.cs_next_var /\
  expr_post ctx func cenv cx e es sa sm s0 es' v1 x entry /\
  alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
  res = unop_result cx ann Neg [ann] v1 es' ==>
  frag_exec_mem ctx sm sb (\s. s = entry)
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx (Builtin ann Neg [e]) es
           sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit res)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es' entry /\
   eval_operand x entry = SOME (typed_val_to_w256 tv v1)` by
    gvs[expr_post_def, expr_val_rel_def] >>
  `~word_gt (typed_val_to_w256 tv v1) (FST (type_bounds ann)) ==>
   !q. expr_exit (unop_result cx ann Neg [ann] v1 es') (Abort Revert_abort q)` by
    (strip_tac >> irule body_neg_source_abort >> simp[] >>
     qexists_tac `tv` >> simp[]) >>
  drule_all body_neg_frag_mem_at >>
  disch_then (qspecl_then [`es'`, `entry`, `cx`, `ctx`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  drule_all body_neg_source_value >>
  disch_then (qspec_then `es'` strip_assume_tac) >>
  simp[] >> irule expr_post_unop >> simp[] >>
  conj_tac
  >- gvs[expr_val_rel_def] >>
  qexistsl_tac [`sm`, `entry`, `v1`, `x`] >> simp[]
QED

Theorem body_compile_expr_neg[local]:
  compile_expr cenv ty (Builtin ann Neg [e]) sa =
  compile_builtin_dispatch cenv ann ty Neg [e] sa
Proof
  Cases_on `e` >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       expr_type_def, listTheory.list_size_def, vyperASTTheory.expr_size_def,
       basicSizeTheory.option_size_def]
QED

Theorem body_lower_value_neg[local]:
  lower_value compile_expr cenv ty (Builtin ann Neg [e]) sa = (op,sb) ==>
  ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
         compile_neg x (expr_type e) sm = (op,sb)
Proof
  strip_tac >> qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, body_compile_expr_neg] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_child_call] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  strip_tac >> qexistsl_tac [`v`, `st1`] >> simp[]
QED

Theorem body_compile_neg_stack[local]:
  !sa. ?t op sb. compile_expr cenv ty (Builtin ann Neg [e]) sa =
                (StackValue t op,sb)
Proof
  simp[body_compile_expr_neg] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, as_stack_val_pair, pairTheory.UNCURRY]
QED

Theorem compile_neg_sim_mem:
  expr_body_pre cenv cx env (Builtin ann Neg [e]) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin ann Neg [e]) es
Proof
  strip_tac >> drule expr_body_pre_neg >> strip_tac >>
  qpat_x_assum `ann = expr_type e` SUBST_ALL_TAC >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule body_lower_value_neg >> strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   (!z. x = Var z ==> not_fresh_at sm z)` by
    (drule expr_body_pre_lower_value_word_shape >>
     disch_then drule >> simp[]) >>
  `cs_extends sm sb` by
    (drule_at Any straight_fresh_cs_extends >> simp[body_neg_straight_fresh]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `builtin_args_length_ok Neg 1 /\ Neg <> Len` by
    simp[vyperContextTheory.builtin_args_length_ok_def] >>
  drule_all eval_expr_unop_cases >> strip_tac
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`sa`, `sm`, `x`, `INR exc`, `es'`, `s0`] mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
      disch_then (qspecl_then
        [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
         `\s. F`, `expr_exit res`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      irule frag_exec_mem_exit_prefix >> qexists_tac `sm` >> simp[]) >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         value_has_type tv v1` by
    (drule expr_body_pre_word_value >> simp[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `x`, `INL v1`, `es'`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_pre_exit_c) >>
  disch_then (qspecl_then
    [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
     `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_mem_then th)) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  irule body_neg_tail_mem >> simp[] >> qexistsl_tac [`v1`, `x`] >> simp[]
QED

Theorem compile_neg_vv_sim_mem:
  expr_body_pre cenv cx env (Builtin ann Neg [e]) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann Neg [e]) es
Proof
  strip_tac >> irule body_expr_vv_sim_mem_stack >>
  conj_tac >- simp[body_compile_neg_stack] >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  irule compile_neg_sim_mem >> simp[] >> qexists_tac `env` >> simp[]
QED

