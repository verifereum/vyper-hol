Theory logArgsRunPtr
Ancestors
  bodyPtrDefs exprSimDefs logGhostFramePtr stmtSimLogArgs loweringPosts
  stmtFragPtr fragGasPathPtr logArgsPtr logArgsPostPtr stmtSimLogArgsGrowth exprReasonOperand
  exprOperandVar exprSimWordArgs supportedTypes exprSimOps
  arithmetic gasOutcomeMapPtr gasSummaryComposePtr gasContext gasExemptCert
  gasSummary fragGasPath fragGasMode
  loweringSlice exprLoweringProps freshWrites fragExec emitHelperProps varsExt
  compileEnv vyperInterpreter vyperState vyperTyping vyperTypeSystem
  vyperExprNoControl vyperEvalExprPreservesScopesDom list
Libs
  monadsyntax

Theorem eval_exprs_cons_bind:
  eval_exprs cx (e::args) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (eval_exprs cx args) (\vs. return (v::vs)))
Proof
  simp[FUN_EQ_THM, Once evaluate_def] >> gen_tac >>
  simp[bind_def] >> Cases_on `eval_expr cx e x` >> rename1 `_ = (raw, st1)` >>
  Cases_on `raw` >> simp[] >>
  Cases_on `read_result cx x' st1` >> rename1 `_ = (r2, st2)` >>
  Cases_on `r2` >> simp[]
QED

Theorem log_head_admissible:
  gas_admissible (eval_exprs cx (e::args))
    (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rw[gas_admissible_def] >> Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `eval_exprs cx (e::args) (es with gas_obs := gs) = (INR ex, ee)` by
    simp[eval_exprs_cons_bind, Once bind_def] >>
  first_x_assum drule >> simp[]
QED

Theorem log_tail_admissible:
  gas_admissible (eval_exprs cx (e::args))
    (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
            (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  gas_admissible (eval_exprs cx args)
    (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception))
    (mid with gas_obs := [])
Proof
  rw[gas_admissible_def] >> rpt strip_tac >> gvs[] >>
  `eval_exprs cx (e::args) (es with gas_obs := xs ++ gs) = (INR exc, ee)` by
    (simp[eval_exprs_cons_bind, Once bind_def] >> simp[bind_def, return_def]) >>
  first_x_assum drule >> simp[]
QED

Theorem ignore_bind_bind_return:
  ignore_bind (bind a k) (return ()) =
    bind a (\v. ignore_bind (k v) (return ()))
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
  Cases_on `a x` >> rename1 `a x = (r1, st1)` >> Cases_on `r1` >> simp[]
QED

Theorem expr_exit_INR_type:
  expr_exit (INR ex : 'a + exception) r = expr_exit (INR ex : 'b + exception) r
Proof
  Cases_on `ex` >> Cases_on `r` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

(* Keep outcome consequences opaque. The private scope-domain invariant
   supplies the source frame needed when composing successful arguments;
   the public evaluator discards this extra conjunct. *)
Definition log_eval_ptr_post_def:
  log_eval_ptr_post d ctx func cenv cx es sa sb s0 G0 tn0 args xs =
    (\res ee G tn t. ?vs. res = INL vs /\
       log_args_post ctx func cenv cx es sa sb s0 ee xs vs t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                             value_has_type tv v) (MAP expr_type args) vs /\
       EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sb z) /\
                  (!lab. FST p <> Label lab)) xs /\
       ghost_inv d cenv cx ee G tn t /\
       LIST_REL (\p v. ptr_val_ok cx (SND p) v (FST p) G tn t) xs vs /\
       LIST_REL (\e p. ~is_word_type (expr_type e) ==>
         ptr_buf_ok cenv e (FST p) G t) args xs /\
       ghost_kept cenv es sa G0 tn0 s0 G tn /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes)
End

Theorem log_eval_ptr_post_cons:
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ (!l. x <> Label l) /\
  expr_sim_inv cenv cx env0 es0 /\ expr_type e = BaseT bt /\
  post_value_type cenv e = expr_type e /\
  expr_post ctx func cenv cx e es sa sm s0 es1 v x t /\
  ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
  (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G1 t) /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  log_eval_ptr_post d ctx func cenv cx es1 sm sb t G1 tn1 args ys res es' G2 tn2 u ==>
  log_eval_ptr_post d ctx func cenv cx es sa sb s0 G0 tn0
    (e::args) ((x,expr_type e)::ys)
    (case res of INL vs => INL (v::vs) | INR ex => INR ex) es' G2 tn2 u
Proof
  rewrite_tac[log_eval_ptr_post_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
  `!z. x = Var z ==> not_fresh_at sb z` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule_all log_args_post_ptr_cons >> simp[] >> metis_tac[]
QED

Theorem compile_log_eval_all_ptr_ind[local]:
  !d ctx PG func cenv cx R env env0 es0.
    (!e tail es. R (e::tail) es ==>
       expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es /\
       !v es1. bind (eval_expr cx e) (read_result cx) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    (!tail es gs. R tail es ==> R tail (es with gas_obs := gs)) /\
    expr_sim_inv cenv cx env0 es0 /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
    !args es sa xs sb s0 G0 tn0.
    R args es /\ EVERY supported_scalar_type (MAP expr_type args) /\
    compile_log_eval_all cenv args sa = (xs,sb) /\
    gas_admissible (eval_exprs cx args)
      (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    well_typed_exprs env args /\
    stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (eval_exprs cx args) (es,s0,G0,tn0)
      (log_eval_ptr_post d ctx func cenv cx es sa sb s0 G0 tn0 args xs)
      (\res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (rpt gen_tac >> strip_tac >> gvs[compile_log_eval_all_nil] >>
      simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_ptr_at_def] >>
      qexistsl_tac [`INL []`, `es`, `G0`, `tn0`, `OK s0`] >>
      simp[Once evaluate_def, return_def, log_eval_ptr_post_def,
           log_args_post_def, wb_frame_refl, ghost_kept_refl, ghost_inv_gas_obs] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[compile_log_eval_all_cons] >>
  suspend "cons"
QED

Resume compile_log_eval_all_ptr_ind[cons]:
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at sm z)` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     simp[] >> metis_tac[compile_lower_value_var]) >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
   sm.cs_next_id <= sb.cs_next_id` by
    (drule compile_log_eval_all_grows >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es` by metis_tac[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule log_head_admissible >> qexists_tac `args` >> simp[]) >>
  `well_typed_expr env e /\ well_typed_exprs env args` by
    fs[vyperTypeSystemTheory.well_typed_expr_def] >>
  `!lab. x <> Label lab` by
    (drule_all lower_compile_expr_not_label >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> rewrite_tac[eval_exprs_cons_bind] >>
  disch_then (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- suspend "head_summary" >>
  qpat_x_assum `!es' sa' xs' sb' s0' G0' tn0'. _` kall_tac >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fin`] >>
  rewrite_tac[ignore_bind_bind_return] >>
  irule gas_exempt_cert_error_value >> first_assum ACCEPT_TAC
QED

Resume compile_log_eval_all_ptr_ind[head_summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "head_value" >>
  qpat_x_assum `!es' sa' xs' sb' s0' G0' tn0'. _` kall_tac >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  simp[gas_outcome_ptr_def] >>
  qexists_tac `marks` >> disj1_tac >> simp[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR ex`, `es_end`, `G`, `tn`, `r`] >> conj_tac
  >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_log_eval_all_ptr_ind[head_value]:
  gvs[] >>
  drule gas_marked_exec_ptr_exec >> strip_tac >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
   (INL v, es_end with gas_obs := [])` by
    (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
       (qspec_then `[]` mp_tac) >> rewrite_tac[APPEND_NIL]) >>
  `R (e::args) (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[] >>
  `R args (es_end with gas_obs := []) /\
   ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
        value_has_type tv v` by metis_tac[] >>
  `~t.vs_halted` by metis_tac[gas_marked_path_exec, gas_path_normal] >>
  `gas_admissible (eval_exprs cx args)
     (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception))
     (es_end with gas_obs := [])` by
    (irule log_tail_admissible >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (`(do r <- eval_expr cx e; read_result cx r od)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v, es_end with gas_obs := [])` by
       (CONV_TAC (DEPTH_CONV ETA_CONV) >> first_assum ACCEPT_TAC) >>
     drule forced_eval_expr_preserves_scopes_dom >> simp[]) >>
  qpat_x_assum `!es' sa' xs' sb' s0' G0' tn0'. _`
    (qspecl_then [`es_end with gas_obs := []`, `sm`, `ys`, `sb`, `t`, `G`, `tn`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[not_fresh_at_mono])) >>
  strip_tac >>
  qpat_x_assum `!e tail es. _` kall_tac >>
  qpat_x_assum `!tail es gs. _` kall_tac >>
  qpat_x_assum `!tail. bind _ _ _ = _` kall_tac >>
  qpat_x_assum `gas_marked_path _ _ _ _ _ _` kall_tac >>
  suspend "tail_compose"
QED

Resume compile_log_eval_all_ptr_ind[tail_compose]:
  irule gas_outcome_ptr_bind_normal >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`es_end`, `t`, `v`] >> simp[]) >>
  irule gas_outcome_ptr_map_return >>
  goal_assum (drule_at Any) >> conj_tac
  >- suspend "post_cons" >>
  rpt strip_tac >> Cases_on `res` >> gvs[] >>
  metis_tac[expr_exit_def, expr_exit_INR_type]
QED

Resume compile_log_eval_all_ptr_ind[post_cons]:
  rpt strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule stmtSimLogArgsRunTheory.log_scalar_post_value_type >> fs[]) >>
  `?bt. expr_type e = BaseT bt` by (Cases_on `expr_type e` >>
     gvs[supported_scalar_type_def, supported_word_type_def, supported_string_type_def]) >>
  `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by simp[] >>
  irule log_eval_ptr_post_cons >>
  simp[] >> conj_tac >- metis_tac[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Finalise compile_log_eval_all_ptr_ind

Theorem compile_log_eval_all_ptr:
  !args d ctx PG func cenv cx R es sa xs sb s0 G0 tn0 env env0 es0.
    (!e tail es. R (e::tail) es ==>
       expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es /\
       !v es1. bind (eval_expr cx e) (read_result cx) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    (!tail es gs. R tail es ==> R tail (es with gas_obs := gs)) /\
    R args es /\ EVERY supported_scalar_type (MAP expr_type args) /\
    compile_log_eval_all cenv args sa = (xs,sb) /\
    gas_admissible (eval_exprs cx args)
      (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    expr_sim_inv cenv cx env0 es0 /\ well_typed_exprs env args /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (eval_exprs cx args) (es,s0,G0,tn0)
      (\res ee G tn t. ?vs. res = INL vs /\
         log_args_post ctx func cenv cx es sa sb s0 ee xs vs t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                               value_has_type tv v) (MAP expr_type args) vs /\
         EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sb z) /\
                    (!lab. FST p <> Label lab)) xs /\
         ghost_inv d cenv cx ee G tn t /\
         LIST_REL (\p v. ptr_val_ok cx (SND p) v (FST p) G tn t) xs vs /\
         LIST_REL (\e p. ~is_word_type (expr_type e) ==>
           ptr_buf_ok cenv e (FST p) G t) args xs /\
         ghost_kept cenv es sa G0 tn0 s0 G tn)
      (\res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_ptr_conseq >>
  qexistsl_tac [`log_eval_ptr_post d ctx func cenv cx es sa sb s0 G0 tn0 args xs`,
                `\res ee gt r. expr_exit res r`] >>
  conj_tac
  >- (simp[log_eval_ptr_post_def] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  irule compile_log_eval_all_ptr_ind >> simp[] >>
  rpt conj_tac
  >- (qexists_tac `R` >> simp[] >> first_assum ACCEPT_TAC)
  >- (qexists_tac `env` >> simp[]) >>
  qexistsl_tac [`env0`, `es0`] >> simp[]
QED

(* The semantic frame for the statement entry needs scope domains as well
   as the pointer post.  Both are already proved by the same evaluation induction. *)
Theorem compile_log_eval_all_scopes_ptr:
  !args d ctx PG func cenv cx R es sa xs sb s0 G0 tn0 env env0 es0.
    (!e tail es. R (e::tail) es ==>
       expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es /\
       !v es1. bind (eval_expr cx e) (read_result cx) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    (!tail es gs. R tail es ==> R tail (es with gas_obs := gs)) /\
    R args es /\ EVERY supported_scalar_type (MAP expr_type args) /\
    compile_log_eval_all cenv args sa = (xs,sb) /\
    gas_admissible (eval_exprs cx args)
      (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    expr_sim_inv cenv cx env0 es0 /\ well_typed_exprs env args /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (eval_exprs cx args) (es,s0,G0,tn0)
      (\res ee G tn t. ?vs. res = INL vs /\
         log_args_post ctx func cenv cx es sa sb s0 ee xs vs t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                               value_has_type tv v) (MAP expr_type args) vs /\
         EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sb z) /\
                    (!lab. FST p <> Label lab)) xs /\
         ghost_inv d cenv cx ee G tn t /\
         LIST_REL (\p v. ptr_val_ok cx (SND p) v (FST p) G tn t) xs vs /\
         LIST_REL (\e p. ~is_word_type (expr_type e) ==>
           ptr_buf_ok cenv e (FST p) G t) args xs /\
         ghost_kept cenv es sa G0 tn0 s0 G tn /\
         MAP FDOM es.scopes = MAP FDOM ee.scopes)
      (\res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_ptr_conseq >>
  qexistsl_tac [`log_eval_ptr_post d ctx func cenv cx es sa sb s0 G0 tn0 args xs`,
                `\res ee gt r. expr_exit res r`] >>
  conj_tac
  >- (simp[log_eval_ptr_post_def] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  irule compile_log_eval_all_ptr_ind >> simp[] >>
  rpt conj_tac
  >- (qexists_tac `R` >> simp[] >> first_assum ACCEPT_TAC)
  >- (qexists_tac `env` >> simp[]) >>
  qexistsl_tac [`env0`, `es0`] >> simp[]
QED
