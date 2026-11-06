(* Typed Neg boundaries retain the original scalar operand judgment. *)
Theory bodyPtrWordBuiltinsNegCase
Ancestors
  bodyPtrWordBuiltinsNegPost bodyPtrWordBuiltinsNotCase
  bodyPtrWordBuiltinsNegSuffix bodyPtrDefs fragExec fragGasSeqPtr fragGasPathPtr ptrDiscipline
  bodyPtrWordBuiltinsIntervalGhost stmtFragPtr exprSimWordArgs
  exprSimSource exprSimHypsDefs vyperTyping vyperTypeSystem
  exprSimUnopProps exprSimUnopComposeProps exprUnopStraight
  fragGasFresh freshWrites exprSimDefs loweringPosts exprLoweringProps
  vyperAST vyperInterpreter varsExt compileEnv list

Theorem word_neg_operand_pre:
  expr_body_pre cenv cx env (Builtin ann Neg [e]) es ==>
  ann = expr_type e /\
  is_numeric_type (expr_type e) /\ ~is_uint_type (expr_type e) /\
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `ann = expr_type e /\ is_numeric_type (expr_type e) /\
   ~is_uint_type (expr_type e)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  simp[] >> drule expr_body_pre_builtin_arg >>
  disch_then irule >> gvs[expr_body_pre_def]
QED

Theorem word_neg_typed_post:
  is_numeric_type ann /\ ~is_uint_type ann /\ ann = expr_type e /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  compile_neg x ann s1 = (op,sb) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  eval_operand x t0 = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv s1 /\
  ~t0.vs_halted /\ t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  sa.cs_next_var <= s1.cs_next_var /\
  w2i (FST (type_bounds ann)) < w2i (typed_val_to_w256 tv v) ==>
  ?v' t. unop_result cx ann Neg [expr_type e] v ee = INL v' /\
    run_inst_seq (emitted_insts s1 sb) t0 = OK t /\
    expr_post ctx func cenv cx (Builtin ann Neg [e]) es sa sb s0 ee v' op
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `is_word_type ann` by
    (qpat_x_assum `is_numeric_type ann` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `ann` >> simp[is_numeric_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def]) >>
  `stmt_state_rel ctx func cenv cx ee t0` by gvs[expr_post_def] >>
  `straight_fresh (compile_neg x ann)` by metis_tac[straight_fresh_neg, ETA_AX] >>
  drule_all neg_typed_source >> disch_then (qspec_then `ee` mp_tac) >>
  simp[] >> strip_tac >>
  `fresh_vars_wrt s1 (drop_fresh s1 t0)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh s1 t0) = SOME (typed_val_to_w256 tv v)` by
    simp[eval_operand_drop_fresh] >>
  drule_all compile_neg_run >> simp[] >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  rename1 `run_inst_seq _ t0 = OK actual` >>
  qexists `actual` >> simp[] >>
  reverse conj_tac >- gvs[] >>
  irule expr_post_unop >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (simp[expr_val_rel_def] >> rpt strip_tac >> gvs[]) >>
  qexistsl [`s1`, `t0`, `v`, `x`] >> gvs[]
QED

Theorem word_neg_normal_ptr_outcome:
  is_numeric_type ann /\ ~is_uint_type ann /\ ann = expr_type e /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  compile_neg x ann s1 = (op,sb) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  eval_operand x t0 = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ fn_has_code s1 sb func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  ~ctx_has_dalloca ctx /\ ~t0.vs_halted /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  sa.cs_next_var <= s1.cs_next_var /\ ghost_inv d cenv cx ee G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ ptr_val_ok cx ann v x G tn t0 /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  w2i (FST (type_bounds ann)) < w2i (typed_val_to_w256 tv v) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vs. (unop_result cx ann Neg [expr_type e] v vs,vs)) (ee,t0,G,tn)
    (\res fin G' tn' u. ?v'. res = INL v' /\
      expr_post ctx func cenv cx (Builtin ann Neg [e]) es sa sb s0 fin v' op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin G' tn' u /\ ptr_val_ok cx ann v' op G' tn' u /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >>
  `is_word_type ann` by
    (qpat_x_assum `is_numeric_type ann` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `ann` >>
     simp[is_numeric_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def]) >>
  drule_all word_neg_typed_post >> strip_tac >>
  `op_taint tn x = {} /\ op_prov G x = NONE` by gvs[ptr_val_ok_def] >>
  `allocas_from 0 t0` by simp[allocas_from_def] >>
  drule_all word_neg_emitted_checked >>
  disch_then (qspecl_then [`func`, `PG`, `G`, `cx_dead cx`] strip_assume_tac) >>
  drule_all word_neg_compiled_normal_post >> strip_tac >>
  drule_all word_neg_code_prefix >> strip_tac >>
  drule word_neg_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[] >> strip_tac >>
  drule word_neg_current_block >> strip_tac >>
  simp[gas_outcome_ptr_def] >> qexists `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl [`INL v'`, `ee`, `G'`, `tn'`,
    `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[exprSimUnopComposePropsTheory.unop_result_gas_obs] >>
  simp[ghost_inv_gas_obs, word_interval_ghost_inv_index, ptr_val_ok_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qpat_x_assum `expr_post _ _ _ _ (Builtin _ _ _) _ _ _ _ _ _ _ _` mp_tac >>
      simp[expr_post_def, expr_val_at_def, stmt_state_rel_gas_obs] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem word_neg_actual_abort:
  compile_neg x ann s1 = (op,sb) /\
  eval_operand x t0 = SOME w /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  ~(w2i (FST (type_bounds ann)) < w2i w) ==>
  ?t. run_inst_seq (emitted_insts s1 sb) t0 = Abort Revert_abort t
Proof
  strip_tac >>
  `straight_fresh (compile_neg x ann)` by metis_tac[straight_fresh_neg, ETA_AX] >>
  `fresh_vars_wrt s1 (drop_fresh s1 t0)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh s1 t0) = SOME w` by simp[eval_operand_drop_fresh] >>
  drule_all compile_neg_run >> simp[] >> strip_tac >>
  `writes_fresh s1 (emitted_insts s1 sb)` by metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result
    (run_inst_seq (emitted_insts s1 sb) (drop_fresh s1 t0))
    (run_inst_seq (emitted_insts s1 sb) t0)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >> metis_tac[]
QED

Theorem word_neg_overflow_ptr_outcome:
  is_numeric_type ann /\ ~is_uint_type ann /\ ann = expr_type e /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  compile_neg x ann s1 = (op,sb) /\
  eval_operand x t0 = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ fn_has_code s1 sb func /\
  op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\ ~t0.vs_halted /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  ~(w2i (FST (type_bounds ann)) < w2i (typed_val_to_w256 tv v)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vs. (unop_result cx ann Neg [expr_type e] v vs,vs)) (ee,t0,G,tn)
    Q (\res fin gt r. expr_exit res r)
Proof
  strip_tac >> drule_all neg_typed_source >>
  disch_then (qspec_then `ee` mp_tac) >> simp[] >> strip_tac >>
  drule_all word_neg_actual_abort >> strip_tac >>
  `allocas_from 0 t0` by simp[allocas_from_def] >>
  drule_all word_neg_emitted_checked >>
  disch_then (qspecl_then [`func`, `PG`, `G`, `cx_dead cx`] strip_assume_tac) >>
  drule_all word_neg_code_prefix >> strip_tac >>
  drule word_neg_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> strip_tac >>
  simp[gas_outcome_ptr_def] >> qexists `REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl [`INR (Error (RuntimeError m))`, `ee`, `G'`, `tn'`,
    `Abort Revert_abort (t with vs_inst_idx := j)`] >>
  simp[exprSimUnopComposePropsTheory.unop_result_gas_obs, expr_exit_def,
       exit_result_def]
QED

Theorem word_neg_typed_ptr_outcome:
  is_numeric_type ann /\ ~is_uint_type ann /\ ann = expr_type e /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  compile_neg x ann s1 = (op,sb) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  eval_operand x t0 = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ fn_has_code s1 sb func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  ~ctx_has_dalloca ctx /\ ~t0.vs_halted /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  sa.cs_next_var <= s1.cs_next_var /\ ghost_inv d cenv cx ee G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ ptr_val_ok cx ann v x G tn t0 /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vs. (unop_result cx ann Neg [expr_type e] v vs,vs)) (ee,t0,G,tn)
    (\res fin G' tn' u. ?v'. res = INL v' /\
      expr_post ctx func cenv cx (Builtin ann Neg [e]) es sa sb s0 fin v' op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin G' tn' u /\ ptr_val_ok cx ann v' op G' tn' u /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >>
  Cases_on `w2i (FST (type_bounds ann)) < w2i (typed_val_to_w256 tv v)`
  >- (drule_all word_neg_normal_ptr_outcome >> simp[]) >>
  `op_taint tn x = {}` by gvs[ptr_val_ok_def] >>
  drule_all word_neg_overflow_ptr_outcome >> simp[]
QED
