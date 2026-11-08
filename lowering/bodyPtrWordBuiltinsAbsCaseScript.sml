(* Typed source and actual-run boundaries for the scalar Abs continuation. *)
Theory bodyPtrWordBuiltinsAbsCase
Ancestors bodyPtrWordBuiltinsAbsPost bodyPtrWordBuiltinsNegCase
  bodyPtrDefs fragGasPathPtr bodyPtrWordBuiltinsIntervalGhost stmtFragPtr
  bodyPtrWordBuiltinsAbsSuffix ptrDiscipline exprSimWordArgs
  exprSimUnopProps exprSimUnopComposeProps exprUnopStraight
  builtinProps builtinSimple freshWrites varsExt fragExec fragGasFresh
  exprSimSource exprSimHypsDefs exprSimDefs loweringPosts
  vyperTyping vyperTypeSystem vyperValueOperation valueEncoding vyperValue
  vyperAST vyperInterpreter vyperState vyperContext compileEnv list words integer_word

Theorem word_abs_operand_pre:
  expr_body_pre cenv cx env (Builtin ann Abs [e]) es ==>
  ann = BaseT (IntT 256) /\ expr_type e = BaseT (IntT 256) /\
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `ann = BaseT (IntT 256) /\ expr_type e = BaseT (IntT 256)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  simp[] >> drule expr_body_pre_builtin_arg >>
  disch_then irule >> gvs[expr_body_pre_def]
QED

Theorem word_abs_actual_run:
  compile_builtin_abs x sm = (dst,sn) /\ eval_operand x s = SOME w /\
  (!z. x = Var z ==> not_fresh_at sm z) ==>
  (w <> INT_MINw ==>
   ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
       eval_operand dst q = SOME (if word_msb w then 0w - w else w)) /\
  (w = INT_MINw ==>
   ?q. run_inst_seq (emitted_insts sm sn) s = Abort Revert_abort q)
Proof
  strip_tac >>
  `straight_fresh (compile_builtin_abs x)` by simp[straight_fresh_abs] >>
  `writes_fresh sm (emitted_insts sm sn)` by metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `eval_operand x (drop_fresh sm s) = SOME w` by
    simp[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sm (drop_fresh sm s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all compile_builtin_abs_run >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sm sn) (drop_fresh sm s))
                   (run_inst_seq (emitted_insts sm sn) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  conj_tac >> strip_tac >> gvs[vars_ext_result_def] >>
  gvs[vars_ext_def] >> drule eval_operand_vars_ext >>
  disch_then (qspec_then `dst` mp_tac) >> simp[] >>
  qpat_x_assum `t' = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem word_abs_typed_source:
  value_has_type (BaseTV (IntT 256)) v ==>
  if typed_val_to_w256 (BaseTV (IntT 256)) v <> INT_MINw then
    ?v'. unop_result cx (BaseT (IntT 256)) Abs tys v es = INL v' /\
      typed_val_to_w256 (BaseTV (IntT 256)) v' =
        (if word_msb (typed_val_to_w256 (BaseTV (IntT 256)) v)
         then 0w - typed_val_to_w256 (BaseTV (IntT 256)) v
         else typed_val_to_w256 (BaseTV (IntT 256)) v)
  else ?m. unop_result cx (BaseT (IntT 256)) Abs tys v es =
    INR (Error (RuntimeError m))
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def] >>
  drule int256_abs_bound >> strip_tac >>
  drule_all abs_i2w >> strip_tac >>
  simp[unop_result_def, evaluate_builtin_def, type_to_int_bound_def,
       bounded_int_op_def, typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `i = INT_MIN (:256)` >> gvs[]
QED

Theorem word_abs_typed_post:
  ann = BaseT (IntT 256) /\ expr_type e = ann /\
  value_has_type (BaseTV (IntT 256)) v /\ compile_builtin_abs x s1 = (op,sb) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  eval_operand x t0 = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv s1 /\
  ~t0.vs_halted /\ t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  sa.cs_next_var <= s1.cs_next_var /\
  typed_val_to_w256 (BaseTV (IntT 256)) v <> INT_MINw ==>
  ?v' t. unop_result cx ann Abs [expr_type e] v ee = INL v' /\
    run_inst_seq (emitted_insts s1 sb) t0 = OK t /\
    expr_post ctx func cenv cx (Builtin ann Abs [e]) es sa sb s0 ee v' op
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx ee t0` by gvs[expr_post_def] >>
  `straight_fresh (compile_builtin_abs x)` by simp[straight_fresh_abs] >>
  drule word_abs_typed_source >>
  disch_then (qspecl_then [`[BaseT (IntT 256)]`, `ee`, `cx`] mp_tac) >>
  simp[] >> strip_tac >>
  `fresh_vars_wrt s1 (drop_fresh s1 t0)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh s1 t0) =
    SOME (typed_val_to_w256 (BaseTV (IntT 256)) v)` by simp[eval_operand_drop_fresh] >>
  drule_all compile_builtin_abs_run >> simp[] >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  rename1 `run_inst_seq _ t0 = OK actual` >>
  qexists `actual` >> simp[] >> reverse conj_tac >- gvs[] >>
  irule expr_post_unop >> simp[is_word_type_def] >>
  conj_tac >- (simp[expr_val_rel_def, evaluate_type_def, is_word_type_def] >> rpt strip_tac >> gvs[]) >>
  qexistsl [`s1`, `t0`, `v`, `x`] >> gvs[]
QED

Theorem word_abs_normal_ptr_outcome:
  ann = BaseT (IntT 256) /\ expr_type e = ann /\
  value_has_type (BaseTV (IntT 256)) v /\ compile_builtin_abs x s1 = (op,sb) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  eval_operand x t0 = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ fn_has_code s1 sb func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  ~ctx_has_dalloca ctx /\ ~t0.vs_halted /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  sa.cs_next_var <= s1.cs_next_var /\ ghost_inv d cenv cx ee G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ ptr_val_ok cx ann v x G tn t0 /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  typed_val_to_w256 (BaseTV (IntT 256)) v <> INT_MINw ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vs. (unop_result cx ann Abs [ann] v vs,vs)) (ee,t0,G,tn)
    (\res fin G' tn' u. ?v'. res = INL v' /\
      expr_post ctx func cenv cx (Builtin ann Abs [e]) es sa sb s0 fin v' op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin G' tn' u /\ ptr_val_ok cx ann v' op G' tn' u /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >> drule_all word_abs_typed_post >> strip_tac >>
  `op_taint tn x = {} /\ op_prov G x = NONE` by
    gvs[ptr_val_ok_def, is_word_type_def] >>
  `allocas_from 0 t0` by simp[allocas_from_def] >>
  drule_all word_abs_counted_normal_post >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  drule word_abs_current_block >> strip_tac >>
  drule word_abs_emitted_shape >> strip_tac >>
  simp[gas_outcome_ptr_def] >> qexists `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl [`INL v'`, `ee`, `H`, `th`,
    `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[exprSimUnopComposePropsTheory.unop_result_gas_obs] >>
  simp[ghost_inv_gas_obs, word_interval_ghost_inv_index,
       ptr_val_ok_def, is_word_type_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qpat_x_assum `expr_post _ _ _ _ (Builtin _ _ _) _ _ _ _ _ _ _ _` mp_tac >>
      simp[expr_post_def, expr_val_at_def, stmt_state_rel_gas_obs] >> metis_tac[]) >>
  qpat_x_assum `expr_post _ _ _ _ (Builtin _ _ _) _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def, expr_val_at_def, stmt_state_rel_gas_obs,
       expr_type_def, is_word_type_def] >> metis_tac[]
QED

Theorem word_abs_overflow_ptr_outcome:
  ann = BaseT (IntT 256) /\ value_has_type (BaseTV (IntT 256)) v /\
  compile_builtin_abs x s1 = (op,sb) /\
  eval_operand x t0 = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ fn_has_code s1 sb func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~t0.vs_halted /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  sa.cs_next_var <= s1.cs_next_var /\ ghost_inv d cenv cx ee G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ ptr_val_ok cx ann v x G tn t0 /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  typed_val_to_w256 (BaseTV (IntT 256)) v = INT_MINw ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vs. (unop_result cx ann Abs tys v vs,vs)) (ee,t0,G,tn)
    Q (\res fin gt r. expr_exit res r)
Proof
  strip_tac >> drule word_abs_typed_source >>
  disch_then (qspecl_then [`tys`, `ee`, `cx`] mp_tac) >> simp[] >> strip_tac >>
  drule_all word_abs_actual_run >> simp[] >> strip_tac >>
  `op_taint tn x = {} /\ op_prov G x = NONE` by
    gvs[ptr_val_ok_def, is_word_type_def] >>
  `allocas_from 0 t0` by simp[allocas_from_def] >>
  drule_all word_abs_counted_abort >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists `REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl [`INR (Error (RuntimeError m))`, `ee`, `H`, `th`,
    `Abort Revert_abort (q with vs_inst_idx := j)`] >>
  simp[exprSimUnopComposePropsTheory.unop_result_gas_obs, expr_exit_def,
       exit_result_def]
QED

Theorem word_abs_typed_ptr_outcome:
  ann = BaseT (IntT 256) /\ expr_type e = ann /\
  value_has_type (BaseTV (IntT 256)) v /\ compile_builtin_abs x s1 = (op,sb) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  eval_operand x t0 = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v) /\
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
    (\vs. (unop_result cx ann Abs [ann] v vs,vs)) (ee,t0,G,tn)
    (\res fin G' tn' u. ?v'. res = INL v' /\
      expr_post ctx func cenv cx (Builtin ann Abs [e]) es sa sb s0 fin v' op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin G' tn' u /\ ptr_val_ok cx ann v' op G' tn' u /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >> Cases_on `typed_val_to_w256 (BaseTV (IntT 256)) v = INT_MINw`
  >- (drule_all word_abs_overflow_ptr_outcome >> simp[]) >>
  drule_all word_abs_normal_ptr_outcome >> simp[]
QED
