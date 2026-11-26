(* Source cuts for the linked ECRecover operand list. *)
Theory bodyECRecoverForcedTailMods
Ancestors
  bodyWriteSubscriptSourceMods bodyFullPredsMods exprBodyPreProps
  exprSimWordArgs exprSimSource gasContext vyperTypeEvalCaseProofs
  vyperTypeExprSoundness vyperInterpreter vyperState list exprSimDefs
  bodyFullPostsMods vyperContext vyperAST
Libs monadsyntax

val list_ok = ``\rr : value list + exception.
  case rr of INL vs => T | INR ex => expr_res_ok (INR ex)``;

Theorem ecrecover_head_admissible_mods:
  gas_admissible (eval_exprs cx (e::rest)) ^list_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rewrite_tac[gas_admissible_def, eval_exprs_cons_action] >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def]
QED

Theorem ecrecover_forced_tail_mods:
  body_exprs_full_ok_mods mods exps cx (e::rest) /\
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  gas_admissible (eval_exprs cx (e::rest)) ^list_ok es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := marks ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
  mid.gas_obs = [] /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  body_exprs_full_ok_mods mods exps cx rest /\
  expr_sim_inv_mods mods cenv cx env mid /\ body_const_cells_agree_mods mods cx env mid /\
  value_has_type tv v /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  gas_admissible (eval_exprs cx rest) ^list_ok mid
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := marks) = (INL v,mid)` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[th])) >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := marks) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := marks)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  drule_then (assume_tac o SRULE []) (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >>
  drule_then strip_assume_tac (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.eval_expr_read_INL) >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  gvs[value_runtime_typed_def] >>
  conj_tac
  >- (qpat_x_assum `body_exprs_full_ok_mods _ _ _ (_::_)`
        (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
      first_x_assum irule >> goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_admissible (eval_exprs _ (_::_)) _ _` mp_tac >>
  rewrite_tac[gas_admissible_def, eval_exprs_cons_action] >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >- simp[] >>
  first_x_assum (qspec_then `marks ++ gs` mp_tac) >>
  simp[bind_def] >> disch_then irule >> goal_assum (drule_at Any)
QED
