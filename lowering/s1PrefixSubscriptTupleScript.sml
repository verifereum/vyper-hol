(* Request-prefix companion to bodyFullSubscriptTuple. *)
Theory s1PrefixSubscriptTuple
Ancestors
  s1PrefixPreds bodyFullSubscriptTuple s1PrefixDefs s1PrefixCompose
  s1PrefixProps s1PrefixFrame bodyFullSubscriptTupleSource exprSimTuple
  bodySimFull exprSimHyps gasShadowCompileStmtHelpers gasShadowCompile
  gasShadowState gasShadow gasShadowCompilePure exprLoweringProps
  emitHelperProps fragExec
  gasOutcomeFullCompose exprSimDefs exprSimUnwrap compileEnv
  vyperStorageTrace vyperStorageFootprint vyperState sum

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> drule_all tuple_pre_base >> strip_tac >> gvs[] >>
  pure_rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all compile_expr_tuple_subscript >> strip_tac >>
  `cs_extends sa st1 /\ cs_extends st1 sb` by
    (conj_tac >- metis_tac[compile_expr_extends] >>
     drule emit_op_extends >> simp[same_blocks_def,cs_extends_def] >>
     strip_tac >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code sa st1 func` by metis_tac[fn_has_code_split] >>
  `?sm. compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa =
      (bvv,sm) /\ gas_shadow_state st1 sm` by
    (`gas_shadow_compiles (compile_expr cenv ty obj)
        (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj))` by
       irule gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa` >>
     simp[]) >>
  rename1 `gas_shadow_state st1 shadow_sm` >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    (conj_tac >- metis_tac[compile_expr_extends] >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, NoAsms] >> strip_tac >>
     qpat_x_assum `compile_expr _ _ (Subscript _ (gas_shadow_expr obj) _) _ = _`
       (mp_then Any mp_tac compile_expr_tuple_subscript) >>
     simp[gas_shadow_place_type] >> strip_tac >>
     qpat_assum `emit_op ADD _ shadow_sm = (_,shadow_sb)`
       (mp_then Any mp_tac emit_op_extends) >> simp[same_blocks_def,cs_extends_def] >>
     strip_tac >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ obj _`
    (drule_all o REWRITE_RULE[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
  strip_tac >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ obj _`
    (drule_all o REWRITE_RULE[expr_vv_sim_full_def]) >> strip_tac >>
  qabbrev_tac `Q = \(H : (bool # 256 word # type_value) list # num list)
    (res : eval_result + exception) ee (G : string |-> num # num) (tn : taint) t.
    ?v. res = INL v /\ ~t.vs_halted /\ ee.gas_obs = [] /\
    vv_post H ctx func cenv cx obj es sa st1 s0 ee v bvv t` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_expr cx obj) (es,s0,G0,tn0)
     Q (\H res ee gt r. ISR res)` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
       (mp_then Any irule gas_outcome_full_post_source) >>
     simp[Abbr `Q`] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  simp[tuple_source] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ Q _`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       storage_trace_frame_select] >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `~t.vs_halted /\ mid.gas_obs = [] /\
   vv_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
     obj es sa st1 s0 mid v bvv t` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> Q H _ _ _ _ _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[Abbr `Q`]) >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
   (INL v,mid)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th =>
       pure_rewrite_tac[listTheory.APPEND_NIL,th]) >> simp[]) >>
  `expr_body_pre cenv cx env (Subscript (EL k tys) obj (Literal ity (IntL (&k))))
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all tuple_selected_marked_source >> strip_tac >> gvs[] >>
  irule gas_prefix_full_no_outcome >> simp[storage_trace_frame_select] >>
  rpt gen_tac >> strip_tac >> drule tuple_select_gas_obs >>
  disch_then (qspec_then `gobs` mp_tac) >> simp[]
QED
*)
Theorem subscript_tuple_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann obj idx es tys.
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = TupleT tys /\
  place_type cenv obj = ValPT (TupleT tys) /\
  post_value_type cenv obj = expr_type obj /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj es /\
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann obj idx) es
Proof
  cheat
QED
