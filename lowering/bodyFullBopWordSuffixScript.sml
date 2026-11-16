Theory bodyFullBopWordSuffix
Ancestors
  bodyFullBopWordSuccess bodyFullBopWordAbort bodyFullGhostFrame
  bodyFullBopWordExtract bodyFullBopWordPost gasStorage gasShadow
  bodyPtrBopScalarSeq fragExec exprSimDefs freshWrites vyperStorageFootprint
  instMemFrontier valueEncoding exprLoweringProps vyperTypeSystem augAssignPtrCompiler
  bodyPtrBopTypedSource bodyPtrBopScalarRun bodyPtrBopScalarDispatch
  bodySimFull gasOutcomeFullCompose exprBopSimProps exprSimSource
  wordArgsPtr ptrDiscipline bodyPtrDefs loweringPosts exprSimWordArgs

Theorem bop_word_suffix_inputs[local]:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  ptr_val_ok cx (expr_type e1) v1 x G1 tn1 t /\
  ptr_val_ok cx (expr_type e2) v2 y G2 tn2 u /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) ==>
  op_prov G2 x = NONE /\ op_taint tn2 x = {} /\
  op_prov G2 y = NONE /\ op_taint tn2 y = {}
Proof
  strip_tac >>
  `op_prov G2 x = op_prov G1 x /\ op_taint tn2 x = op_taint tn1 x` by
    (Cases_on `x` >> gvs[op_prov_def, op_taint_def, ghost_kept_at_def]) >>
  gvs[ptr_val_ok_def]
QED

Theorem bop_word_suffix_full:
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  lower_value compile_expr cenv ty (gas_shadow_expr (Builtin ann (Bop bop) [e1;e2]))
    shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
  lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) shadow_sa =
    (x,shadow_s1) /\
  lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e2) shadow_s1 =
    (y,shadow_s2) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
  gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
  cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  s2.cs_next_var <= sb.cs_next_var /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\ (!l. y <> Label l) /\
  cs_extends shadow_sa shadow_s1 /\ cs_extends shadow_s1 shadow_s2 /\
  cs_extends shadow_s2 shadow_sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
  fn_has_code shadow_sa shadow_s1 shadow_func /\
  fn_has_code shadow_s1 shadow_s2 shadow_func /\
  fn_has_code shadow_s2 shadow_sb shadow_func /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
    (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
    (INL v1, mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    (expr_post H ctx func cenv cx e1 es sa s1 s0 mid v1 x t /\
      expr_store_bound cx (expr_type e1) v1 x t /\
      t.vs_current_bb = s1.cs_current_bb /\
      t.vs_inst_idx = LENGTH s1.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
      ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t /\
      (~is_word_type (post_value_type cenv e1) ==> ptr_buf_ok cenv e1 x G1 t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
      ~t.vs_halted /\ mid.gas_obs = [])) /\
  (!tail. bind (eval_expr cx e2) (read_result cx)
    (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
    (INL v2, fin with gas_obs := tail)) /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    (expr_post H ctx func cenv cx e2 mid s1 s2 t fin v2 y u /\
      expr_store_bound cx (expr_type e2) v2 y u /\
      u.vs_current_bb = s2.cs_current_bb /\
      u.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx fin G2 tn2 u /\
      ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 u /\
      (~is_word_type (post_value_type cenv e2) ==> ptr_buf_ok cenv e2 y G2 u) /\
      ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\
      ~u.vs_halted /\ fin.gas_obs = [])) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
    (fin,u,G2,tn2) (\H (res : value + vyperState$exception) ee G tn t. ?v. res = INL v /\
    expr_post H ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 ee v op t /\
    expr_store_bound cx (expr_type (Builtin ann (Bop bop) [e1;e2])) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
    ptr_val_ok cx (post_value_type cenv (Builtin ann (Bop bop) [e1;e2])) v op G tn t /\
    (~is_word_type (post_value_type cenv (Builtin ann (Bop bop) [e1;e2])) ==>
      ptr_buf_ok cenv (Builtin ann (Bop bop) [e1;e2]) op G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) (\H res ee gt r. expr_exit res r)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  fs[] >> mp_tac (SRULE [LET_THM] bop_word_suffix_extract) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace /\
   valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `op_prov G2 x = NONE /\ op_taint tn2 x = {} /\
   op_prov G2 y = NONE /\ op_taint tn2 y = {}` by
    (`post_value_type cenv e1 = expr_type e1 /\
      post_value_type cenv e2 = expr_type e2` by
       metis_tac[post_value_type_word] >>
     gvs[] >> drule_all bop_word_suffix_inputs >> simp[]) >>
  `!a. a IN ({x;y} UNION IMAGE Lit UNIV) ==>
     op_prov G2 a = NONE /\ op_taint tn2 a = {}` by
    metis_tac[bop_scalar_binop_input_clean] >>
  `allocas_from lo u` by fs[ghost_inv_at_def] >>
  `MEM bop [Add; Sub; Mul; Div; Mod; UnsafeAdd; UnsafeSub; UnsafeMul;
    UnsafeDiv; And; Or; XOr; ShL; ShR; Eq; NotEq; Lt; LtE; Gt; GtE;
    Exp; Min; Max; In; NotIn]` by
    (qpat_x_assum `well_typed_binop _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `bop` >>
     simp[well_typed_binop_def]) >>
  drule augAssignPtrCompilerTheory.compile_binop_straight_fresh_ptr >>
  simp[straight_fresh_def] >> disch_then drule >> strip_tac >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts s2 sb) (DROP u.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code s2 sb func` mp_tac >>
     simp[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> goal_assum (drule_at Any) >> simp[listTheory.DROP_APPEND]) >>
  qpat_x_assum `?B. bop_scalar_seq _ _ _ B /\ _` strip_assume_tac >>
  qpat_x_assum `(?v r. _) \/ _` strip_assume_tac
  >- suspend "full_success" >> suspend "full_abort"
QED

Resume bop_word_suffix_full[full_success]:
  drule_all bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G'`, `fin`, `[]`,
    `OK (r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb))`,
    `INL v`, `tn'`] >>
  conj_tac >- simp[] >> conj_tac
  >- (gen_tac >> strip_tac >> conj_tac >- simp[] >>
      disj1_tac >> qexists_tac `r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)` >>
      pure_rewrite_tac[boolTheory.REFL_CLAUSE, boolTheory.AND_CLAUSES] >>
      `storage_trace_frame (bind (eval_expr cx e2) (read_result cx)) /\
       storage_trace_frame (bind (eval_expr cx e1) (read_result cx))` by
        (conj_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
              vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      `valid_horizon cx st0 H mid.storage_trace` by
        (qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
          (qspec_then `[]` mp_tac) >> strip_tac >>
         drule_at (Pat `f st = _`) valid_horizon_frame >>
         simp[] >> disch_then irule >> simp[]) >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
          (qspec_then `[]` mp_tac) >> strip_tac >>
         drule_at (Pat `f st = _`) valid_horizon_frame >>
         simp[] >> disch_then irule >> simp[]) >>
      mp_tac (Q.INST_TYPE [`:'a` |-> `:256`]
        (SRULE [LET_THM] bop_word_suffix_success_post)) >>
      (impl_tac >- (rpt conj_tac >> simp[] >> metis_tac[])) >>
      simp[]) >>
  simp[]
QED

Resume bop_word_suffix_full[full_abort]:
  drule_all bop_word_scalar_abort_joint >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G'`, `fin`, `[]`, `Abort Revert_abort (r with vs_inst_idx := j)`,
    `INR (Error (RuntimeError m))`, `tn'`] >>
  simp[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def] >> metis_tac[]
QED
Finalise bop_word_suffix_full
