Theory stmtSimLogArgsRun
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimProps exprLowering
  stmtSimLogArgs stmtSimLogArgsGrowth exprReasonOperand exprOperandVar vyperTypeSystem
  exprSimWordArgs supportedTypes  exprSimOps
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath list
  loweringSlice exprLoweringProps freshWrites fragExec emitHelperProps varsExt compileEnv
  vyperInterpreter vyperState vyperTyping vyperExprNoControl
  vyperEvalExprPreservesScopesDom
Libs
  monadsyntax


Theorem log_scalar_base[local]:
  supported_scalar_type ty ==> ?bt. ty = BaseT bt
Proof
  Cases_on `ty` >> simp[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def]
QED

Theorem log_scalar_word_or_bytestring[local]:
  !ty. supported_scalar_type ty ==> is_word_type ty \/ is_bytestring_type ty
Proof
  Cases >> simp[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >>
  simp[supported_word_type_def, supported_string_type_def, is_word_type_def,
    is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[supported_word_type_def, supported_string_type_def, is_word_type_def,
    is_bytestring_type_def]
QED

Theorem log_scalar_post_value_type[local]:
  supported_scalar_type (expr_type e) ==> post_value_type cenv e = expr_type e
Proof
  strip_tac >> drule log_scalar_word_or_bytestring >> strip_tac >> simp[]
QED

(* ===== Source sequencing ===== *)

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

Theorem ignore_bind_bind_return:
  ignore_bind (bind a k) (return ()) =
    bind a (\v. ignore_bind (k v) (return ()))
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
  Cases_on `a x` >> rename1 `a x = (r1, st1)` >> Cases_on `r1` >> simp[]
QED

Theorem stmt_state_rel_any_gas_obs[local]:
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx (es with gas_obs := gs) s
Proof
  strip_tac >>
  `s with <|vs_gas_readings := s.vs_gas_readings;
            vs_inst_idx := s.vs_inst_idx|> = s` by
    simp[venomStateTheory.venom_state_component_equality] >>
  metis_tac[msg_gas_state_frame]
QED

(* The error results the arguments of a log may end in. *)
Definition log_args_res_ok_def:
  log_args_res_ok (r : value list + exception) <=>
    !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)
End

Theorem log_head_admissible[local]:
  gas_admissible (eval_exprs cx (e::args)) log_args_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rw[gas_admissible_def] >> Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `eval_exprs cx (e::args) (es with gas_obs := gs) = (INR ex, ee)` by
    simp[eval_exprs_cons_bind, Once bind_def] >>
  first_x_assum drule >> simp[log_args_res_ok_def]
QED

Theorem log_tail_admissible[local]:
  gas_admissible (eval_exprs cx (e::args)) log_args_res_ok es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
            (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  gas_admissible (eval_exprs cx args) log_args_res_ok (mid with gas_obs := [])
Proof
  rw[gas_admissible_def] >>
  rename1 `eval_exprs cx args _ = (res2, ee2)` >>
  simp[log_args_res_ok_def] >> rpt strip_tac >> gvs[] >>
  `eval_exprs cx (e::args) (es with gas_obs := xs ++ gs) = (INR exc, ee2)` by
    (simp[eval_exprs_cons_bind, Once bind_def] >> simp[bind_def, return_def]) >>
  first_x_assum drule >> simp[log_args_res_ok_def]
QED

(* ===== Counted evaluation of the arguments ===== *)

(* The arguments, in order: each one's fragment from the readings its
   actual path selects; an argument's error exits, and after the last one
   every value is where log_args_post puts it. *)
Theorem compile_log_eval_all_gas:
  !args ctx func cenv cx R es sa xs sb s0 env env0 es0 ops.
    (!e tail es. R (e::tail) es ==>
       expr_sim ctx func cenv cx (expr_type e) e es /\
       !v es1. bind (eval_expr cx e) (read_result cx) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    (!tail es gs. R tail es ==> R tail (es with gas_obs := gs)) /\
    R args es /\ EVERY supported_scalar_type (MAP expr_type args) /\
    ~exprs_can_mutate cenv args /\ compile_log_eval_all cenv args sa = (ops,sb) /\
    xs = ZIP (MAP FST ops, MAP expr_type args) /\
    gas_admissible (eval_exprs cx args) log_args_res_ok es /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    expr_sim_inv cenv cx env0 es0 /\ well_typed_exprs env args /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
      (\res ee t. ?vs. res = INL vs /\
         log_args_post ctx func cenv cx es sa sb s0 ee xs vs t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                               value_has_type tv v) (MAP expr_type args) vs /\
         EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sb z) /\
                    (!lab. FST p <> Label lab)) xs)
      (\res ee r. expr_exit res r)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[compile_log_eval_all_nil] >>
      `gas_path ctx func s0 0 (OK s0)` by
        (irule (cj 1 gas_path_rules) >> simp[]) >>
      simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INL []`, `es`, `OK s0`] >>
      simp[gas_marked_exec_def, gas_marked_path_def, Once evaluate_def,
           return_def, log_args_post_def, wb_frame_refl,
           stmt_state_rel_any_gas_obs]) >>
  rpt gen_tac >> strip_tac >> gvs[expr_can_mutate_def] >>
  qpat_x_assum `compile_log_eval_all _ (_::_) _ = _` mp_tac >>
  simp[compile_log_eval_all_unsaved_cons] >> strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  rename1 `compile_log_eval_all cenv args sm = (ys,sb)` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at sm z)` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     simp[] >> metis_tac[compile_lower_value_var]) >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
   sm.cs_next_id <= sb.cs_next_id` by
    (drule_all compile_log_eval_all_grows >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by metis_tac[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[log_head_admissible] >>
  `well_typed_expr env e /\ well_typed_exprs env args` by
    fs[vyperTypeSystemTheory.well_typed_expr_def] >>
  `!lab. x <> Label lab` by
    (drule_all lower_compile_expr_not_label >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `post_value_type cenv e = expr_type e` by
    (drule_all log_scalar_post_value_type >> simp[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `x`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  rewrite_tac[eval_exprs_cons_bind] >>
  simp[gas_outcome_def] >> strip_tac
  >- suspend "head_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fin`] >>
  rewrite_tac[ignore_bind_bind_return] >>
  irule gas_exempt_cert_error_value >> first_assum ACCEPT_TAC
QED

Resume compile_log_eval_all_gas[head_summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- suspend "head_value" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexists_tac `marks` >> disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_log_eval_all_gas[head_value]:
  gvs[] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (fn th => assume_tac th >>
              strip_assume_tac (REWRITE_RULE [gas_marked_exec_def] th)) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
   (INL v, es_end with gas_obs := [])` by
    (qpat_assum `!tail. _ (es with gas_obs := _) = _`
       (qspec_then `[]` mp_tac) >> rewrite_tac[listTheory.APPEND_NIL]) >>
  `R (e::args) (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[] >>
  `R args (es_end with gas_obs := []) /\
   ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
        value_has_type tv v` by metis_tac[] >>
  `~t.vs_halted` by metis_tac[gas_marked_path_exec, gas_path_normal] >>
  `gas_admissible (eval_exprs cx args) log_args_res_ok (es_end with gas_obs := [])` by
    (irule log_tail_admissible >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (`(do r <- eval_expr cx e; read_result cx r od)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v, es_end with gas_obs := [])` by
       (CONV_TAC (DEPTH_CONV ETA_CONV) >> first_assum ACCEPT_TAC) >>
     drule forced_eval_expr_preserves_scopes_dom >> simp[]) >>
  qpat_x_assum `!ctx func cenv cx R. _`
    (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `R`, `es_end with gas_obs := []`,
                  `sm`, `sb`, `t`, `env`, `env0`, `es0`, `ys`] mp_tac) >>
  impl_tac >- (fs[] >> metis_tac[]) >>
  simp[gas_outcome_def] >> strip_tac
  >- suspend "tail_summary" >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks2 _ _` >>
  qexists_tac `marks ++ marks2` >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks2 (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fin`] >>
  rewrite_tac[ignore_bind_bind_return] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`es_end`, `t`, `v`] >> simp[] >>
  rewrite_tac[ignore_bind_bind_return] >>
  irule gas_exempt_cert_error_values >> first_assum ACCEPT_TAC
QED

Resume compile_log_eval_all_gas[tail_summary]:
  rename1 `gas_summary_at _ _ marks2 _ _ _ _` >>
  qexists_tac `marks ++ marks2` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ marks2 _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- suspend "tail_value" >>
  rename1 `gas_marked_exec _ _ (eval_exprs cx args) _ marks2 res2 es_end2 r2` >>
  `?ex. res2 = INR ex` by (Cases_on `res2` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end2`, `r2`] >> simp[] >>
  irule gas_marked_exec_bind_normal >>
  qexistsl_tac [`es_end`, `t`, `v`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED

Resume compile_log_eval_all_gas[tail_value]:
  gvs[] >>
  rename1 `gas_marked_exec _ _ (eval_exprs cx args) _ marks2 (INL vs) es_end2 (OK t2)` >>
  `~t2.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_exprs cx args) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `MAP FDOM es_end.scopes = MAP FDOM es_end2.scopes` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_exprs cx args) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` strip_assume_tac o CONJUNCT1) >>
     drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  `gas_marked_exec F (ctx,func) (return (v::vs))
     (es_end2 with gas_obs := [], t2) [] (INL (v::vs)) es_end2 (OK t2)` by
    (simp[gas_marked_exec_def, gas_marked_path_def, return_def] >>
     irule (cj 1 gas_path_rules) >> simp[]) >>
  qexistsl_tac [`INL (v::vs)`, `es_end2`, `OK t2`] >>
  conj_tac
  >- (irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`es_end`, `t`, `v`] >> simp[] >>
      irule (SIMP_RULE std_ss [APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal)) >>
      qexistsl_tac [`es_end2`, `t2`, `vs`] >> fs[]) >>
  simp[] >> rpt conj_tac
  >- (`?bt. expr_type e = BaseT bt` by (irule log_scalar_base >> fs[]) >>
      irule log_args_post_cons >> simp[] >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`es_end with gas_obs := []`, `sm`, `t`] >> simp[])
  >- (fs[EVERY_MEM] >> metis_tac[not_fresh_at_mono])
QED

Finalise compile_log_eval_all_gas
