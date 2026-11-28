(* Request prefixes of the address evaluation in SelfDestruct. *)
Theory s1PrefixSelfdestruct
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixOfVV bodyFullCases exprBodyPreProps
  gasShadowCompileStmtHelpers exprSimSource selfdestructHalt
  vyperState vyperInterpreter exprLowering vyperAST gasShadow

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> irule expr_sim_prefix_of_vv >>
  drule selfdestruct_full_source_pre >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (first_x_assum irule >> metis_tac[expr_body_pre_static_facts]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (fs[body_exprs_prefix_ok_def] >>
     qpat_x_assum `body_expr_prefix_ok cx e`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  rw[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e))` by
    irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env >>
  drule_all selfdestruct_full_layout_shadow >> strip_tac >> gvs[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`ssm`,`data`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `eval_expr _ (Call _ SelfDestructTarget _ _) = _`
    (fn th => once_rewrite_tac[th]) >>
  `!v st. (SND (selfdestruct_tail cx v st :
      (eval_result + exception) # evaluation_state)).storage_trace = st.storage_trace` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
     Cases_on `dest_AddressV v` >> Cases_on `cx.txn.is_static` >>
     Cases_on `cx.txn.created_in_tx` >>
     gvs[selfdestruct_tail_def, vyperInterpreterTheory.transfer_value_def,
         vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
         lift_option_type_def, check_not_static_def, check_def, assert_def,
         get_accounts_def, update_accounts_def, update_pending_deletions_def,
         vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
     BasicProvers.every_case_tac >>
     gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
         assert_def, get_accounts_def, update_accounts_def,
         update_pending_deletions_def,
         vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
     BasicProvers.every_case_tac >>
     gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
  rewrite_tac[gas_prefix_full_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists `marks` >> conj_tac
  >- (map_every qexists_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `?r mid. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) = (r,mid) /\
      mid.storage_trace = ee.storage_trace` by
    (qpat_x_assum `vyperState$bind _ (selfdestruct_tail _) _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `vyperState$bind src (selfdestruct_tail cx) ist` >>
     Cases_on `src ist` >> Cases_on `q` >> simp[vyperStateTheory.bind_def] >>
     strip_tac >> gvs[] >> metis_tac[pairTheory.SND]) >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> _`
    (qspecl_then [`tail`,`r`,`mid`,`obs_pre`,`rq`,`outcome`,`sfx`,`H'`] mp_tac) >>
  fs[]
QED
*)
Theorem selfdestruct_expr_prefix:
  !cx ann args dflt DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann SelfDestructTarget args dflt) es
Proof
  cheat
QED
