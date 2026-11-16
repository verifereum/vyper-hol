(* AssertReason-specific control boundaries.  The reason producer stays opaque. *)
Theory bodyFullAssertReasonControl
Ancestors
  reasonCompilerProps stmtSimReason stmtSimAssertProps bodyFullShared bodySimFull
  gasShadowCompileStmtCases gasShadowCompileStmtHelpers
  bodyFullAllocaFresh bodyFullGhostFrame
  exprSimDefs stmtSimProps stmtSimDefs bodyMemoryDefs bodyPtrDefs
  emitHelper emitHelperProps freshWrites compileEnv allocaHistory
  venomExecSemantics venomState loweringPosts exprLoweringProps
  gasShadowState gasShadow stmtLowering stmtLoweringMono

Theorem assert_reason_true_post_full:
  expr_post H ctx func cenv cx e es sa s1 s0 mid (BoolV T) op t /\
  ~t.vs_halted /\ sb.cs_current_insts = [] /\
  sa.cs_next_var <= sb.cs_next_var /\
  return_buf_frame d cenv sa s0 /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
  (!x. not_fresh_at sa x ==> FLOOKUP G1 x = FLOOKUP G0 x /\
    op_taint tn1 (Var x) = op_taint tn0 (Var x)) ==>
  ?cenv''.
    stmt_lands lctx sb (INL () : unit + exception) (jump_to sb.cs_current_bb t) /\
    ~(jump_to sb.cs_current_bb t).vs_halted /\
    (~block_is_terminated sb /\ cenv'' = cenv) /\
    cenv_top_ext cenv cenv'' mid.scopes /\
    stmt_state_rel H ctx func cenv'' cx mid (jump_to sb.cs_current_bb t) /\
    storage_well_formed_on cx mid (FST H) /\
    return_buf_frame d cenv'' sb (jump_to sb.cs_current_bb t) /\
    alloca_history func (jump_to sb.cs_current_bb t) /\
    s0.vs_alloca_next <= (jump_to sb.cs_current_bb t).vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv'' cx mid G1 tn1 (jump_to sb.cs_current_bb t) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x (jump_to sb.cs_current_bb t) = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP (jump_to sb.cs_current_bb t).vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G1 x = FLOOKUP G0 x /\
      op_taint tn1 (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >> drule_all assert_success_post_mem >> strip_tac >>
  gvs[] >> simp[ghost_inv_at_jump]
QED

Theorem assert_reason_false_entry_full:
  expr_post H ctx func cenv cx e es sa s1 s0 mid (BoolV F) op t /\
  ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
  ~t.vs_halted /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  sa.cs_next_var <= entry.cs_next_var /\
  entry.cs_current_bb = fl /\ entry.cs_current_insts = [] ==>
  stmt_state_rel H ctx func cenv cx mid (jump_to fl t) /\
  storage_well_formed_on cx mid (FST H) /\
  ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 (jump_to fl t) /\
  local_ptrs_reserved cenv entry /\
  ret_pc_ok cenv entry (jump_to fl t) /\
  return_buf_frame d cenv entry (jump_to fl t) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at entry x) /\
  alloca_history func (jump_to fl t) /\ ~block_is_terminated entry /\
  ~(jump_to fl t).vs_halted /\
  (jump_to fl t).vs_current_bb = entry.cs_current_bb /\
  (jump_to fl t).vs_inst_idx = LENGTH entry.cs_current_insts
Proof
  strip_tac >>
  `ret_pc_ok cenv entry t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     gvs[expr_post_def]) >>
  `return_buf_frame d cenv entry t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     gvs[expr_post_def]) >>
  `local_ptrs_reserved cenv entry` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at entry x` by metis_tac[not_fresh_at_mono] >>
  gvs[expr_post_def, stmt_state_rel_jump_to, ghost_inv_at_jump,
      ret_pc_ok_jump_to, return_buf_frame_jump_to, block_is_terminated_def,
      alloca_history_def, jump_to_def]
QED

Theorem compile_assert_reason_layout_full:
  stmt_env cenv lctx ty (Assert e (AssertReason r)) sa = (ce,sb) /\
  stmt_env cenv lctx ty
    (Assert (gas_shadow_expr e) (AssertReason (gas_shadow_expr r))) ta = (ct,tb) /\
  gas_shadow_state sa ta /\ fn_has_code sa sb func /\ fn_has_code ta tb sfunc ==>
  ?op s1 ok s2 fl s3 s4 entry last t1 t2 t3 t4 sentry slast.
    ce = cenv /\ ct = cenv /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
    fresh_label "assert_ok" s1 = (ok,s2) /\
    fresh_label "assert_fail" s2 = (fl,s3) /\
    emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
    new_block fl s4 = (s4.cs_current_bb,entry) /\
    stmt_env cenv lctx ty (Raise (RaiseReason r)) entry = (cenv,last) /\
    new_block ok last = (last.cs_current_bb,sb) /\
    lower_value compile_expr cenv (BaseT BoolT) (gas_shadow_expr e) ta = (op,t1) /\
    fresh_label "assert_ok" t1 = (ok,t2) /\
    fresh_label "assert_fail" t2 = (fl,t3) /\
    emit_inst JNZ [op; Label ok; Label fl] [] t3 = ((),t4) /\
    new_block fl t4 = (t4.cs_current_bb,sentry) /\
    stmt_env cenv lctx ty (Raise (RaiseReason (gas_shadow_expr r))) sentry = (cenv,slast) /\
    new_block ok slast = (slast.cs_current_bb,tb) /\
    gas_shadow_state s1 t1 /\ gas_shadow_state entry sentry /\
    gas_shadow_state last slast /\
    fn_has_code sa s1 func /\ fn_has_code s3 s4 func /\
    fn_has_code entry last func /\
    s3.cs_current_bb = s1.cs_current_bb /\
    s3.cs_current_insts = s1.cs_current_insts /\
    entry.cs_current_bb = fl /\ entry.cs_current_insts = [] /\
    sb.cs_current_bb = ok /\ sb.cs_current_insts = [] /\
    sa.cs_next_var <= entry.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    fn_has_code ta t1 sfunc /\ fn_has_code t3 t4 sfunc /\
    fn_has_code sentry slast sfunc /\
    t3.cs_current_bb = t1.cs_current_bb /\
    t3.cs_current_insts = t1.cs_current_insts /\
    sentry.cs_current_bb = fl /\ sentry.cs_current_insts = [] /\
    tb.cs_current_bb = ok /\ tb.cs_current_insts = [] /\
    ta.cs_next_var <= sentry.cs_next_var /\ ta.cs_next_var <= tb.cs_next_var
Proof
  strip_tac >>
  qpat_assum `stmt_env _ _ _ (Assert e _) _ = _`
    (mp_then Any strip_assume_tac compile_assert_reason_parts) >>
  qpat_assum `stmt_env _ _ _ (Assert (gas_shadow_expr e) _) _ = _`
    (mp_then Any (qx_choosel_then [`op'`, `t1`, `ok'`, `t2`, `fl'`, `t3`,
      `t4`, `sentry`, `slast`] strip_assume_tac) compile_assert_reason_parts) >>
  `op' = op /\ gas_shadow_state s1 t1` by
    metis_tac[gas_shadow_step, gas_shadow_stmt_lower_value] >> gvs[] >>
  `ok' = ok /\ gas_shadow_state s2 t2` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_fresh_label] >> gvs[] >>
  `fl' = fl /\ gas_shadow_state s3 t3` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_fresh_label] >> gvs[] >>
  `gas_shadow_state s4 t4` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_emit_inst] >>
  `gas_shadow_state entry sentry` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_new_block] >>
  rename1 `stmt_env cenv lctx ty (Raise (RaiseReason r)) entry = (cenv,last)` >>
  `gas_shadow_compiles (stmt_env cenv lctx ty (Raise (RaiseReason r)))
    (stmt_env cenv lctx ty (Raise (RaiseReason (gas_shadow_expr r))))` by
    (simp[stmt_env_def, declare_stmt_local_def] >>
     ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
     >- simp[gas_shadow_compiles_return] >> gen_tac >>
     simp[comp_ignore_bind_def] >>
     ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
     >- (irule (SRULE [gas_shadow_stmt_def, gas_shadow_raise_reason_def]
         (gas_shadow_stmt_raise |> Q.GEN `r` |> Q.SPEC `RaiseReason r`))) >>
     simp[gas_shadow_compiles_return]) >>
  `gas_shadow_state last slast` by metis_tac[gas_shadow_step] >>
  `fn_has_code sa s1 func /\ fn_has_code s3 s4 func /\
    fn_has_code entry last func /\
    s3.cs_current_bb = s1.cs_current_bb /\
    s3.cs_current_insts = s1.cs_current_insts /\
    entry.cs_current_bb = fl /\ entry.cs_current_insts = [] /\
    sb.cs_current_bb = ok /\ sb.cs_current_insts = [] /\
    sa.cs_next_var <= entry.cs_next_var` by
    (irule assert_reason_compiler_code >> metis_tac[]) >>
  `fn_has_code ta t1 sfunc /\ fn_has_code t3 t4 sfunc /\
    fn_has_code sentry slast sfunc /\
    t3.cs_current_bb = t1.cs_current_bb /\
    t3.cs_current_insts = t1.cs_current_insts /\
    sentry.cs_current_bb = fl /\ sentry.cs_current_insts = [] /\
    tb.cs_current_bb = ok /\ tb.cs_current_insts = [] /\
    ta.cs_next_var <= sentry.cs_next_var` by
    (irule assert_reason_compiler_code >> metis_tac[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ ta.cs_next_var <= tb.cs_next_var` by
    (qpat_x_assum `stmt_env _ _ _ (Assert e _) _ = _` mp_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assert (gas_shadow_expr e) _) _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> rpt strip_tac >>
     metis_tac[cj 1 compile_stmt_cs_mono, fragExecTheory.cs_mono_def]) >>
  qexistsl_tac [`s4`, `entry`, `last`, `t4`, `sentry`, `slast`] >> simp[]
QED
