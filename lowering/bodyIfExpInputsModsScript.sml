(* Source inputs for the linked conditional-expression lowering. *)
Theory bodyIfExpInputsMods
Ancestors
  bodyFullPredsMods bodyBranchCellFrameMods bodyNormalHeadTailMods
  bodySimStmtFacts bodyCopyAtomicRhsTypeMods exprBodyPreProps
  exprBodyPreTypingProps exprBodyPreCallSafetyProps vyperTypeExprResult
  vyperTypeEvalCaseProofs vyperTypeEvalSoundness supportedExprTraverse
  allocLimits vyperTypeCallStackSoundness vyperTypeCallGraph loweringPosts
  exprSimHypsDefs vyperTypeSystem vyperInterpreter vyperState vyperAST
  vyperTypeExprSoundness list
Libs
  monadsyntax

Theorem ifexp_body_pre_children_mods:
  expr_body_pre_mods mods ce cx env (IfExp t c a b) es ==>
  expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
  expr_body_pre_mods mods ce cx env c es /\
  !es'. expr_sim_inv_mods mods ce cx env es' ==>
    expr_body_pre_mods mods ce cx env a es' /\
    expr_body_pre_mods mods ce cx env b es'
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, int_calls_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, expr_has_evm_run_thm,
       supported_expr_exists_def, EVERY_APPEND] >>
  strip_tac >>
  drule_then assume_tac call_evaluation_safe_append_left >>
  drule_then assume_tac call_evaluation_safe_append_right >>
  simp[] >> metis_tac[call_evaluation_safe_append_left,
                      call_evaluation_safe_append_right]
QED

Theorem ifexp_full_ok_value_vv_mods[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env st /\ expr_body_pre_mods mods ce cx env e st ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e st /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e st
Proof
  strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem ifexp_read_landing_mods[local]:
  bind (eval_expr cx e) (read_result cx) st = (INL v,mid) ==>
  ?raw. eval_expr cx e st = (INL raw,mid) /\ read_result cx raw mid = (INL v,mid)
Proof
  simp[bind_def, AllCaseEqs()] >> metis_tac[read_result_state]
QED

Theorem ifexp_cells_at_landing_mods[local]:
  well_typed_expr env e /\ body_const_cells_agree_mods mods cx env st /\
  eval_expr cx e st = (INL raw,mid) ==>
  body_const_cells_agree_mods mods cx env mid
Proof
  strip_tac >>
  `?res. eval_stmt cx (Expr e) st = (res,mid)` by
    (simp[Once evaluate_def, bind_def, type_check_def, assert_def, return_def, raise_def] >>
     Cases_on `is_HashMapRef raw` >> simp[]) >>
  `type_stmt env NoneT (Expr e) = SOME env` by
    simp[type_stmt_def, well_typed_expr_not_hashmap_place] >>
  irule body_const_cells_agree_mods_stmt >>
  qexistsl_tac [`env`,`st`,`res`,`NoneT`,`Expr e`] >> simp[]
QED

Theorem ifexp_pre_gas_obs_mods[local]:
  expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) <=>
  expr_body_pre_mods mods ce cx env e es
Proof
  simp[expr_body_pre_mods_def, expr_sim_inv_mods_def]
QED

Theorem ifexp_raw_typed_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e es = (INL raw,ee) ==>
  eval_result_typed (env,cx,ee) raw (Type (expr_type e))
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  qspecl_then [`cx`,`e`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`,`es`,`INL raw`,`ee`] mp_tac) >>
  fs[runtime_consistent_def]
QED

Theorem ifexp_read_types_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  (?rty. evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\ value_has_type rty v) /\
  (!ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv ==>
    value_has_type ptv v)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  `value_runtime_typed env (expr_type e) v` by
    (first_x_assum (qspec_then `v` mp_tac) >> simp[]) >>
  `env.type_defs = get_tenv cx` by
    (irule env_consistent_type_defs_get_tenv >> qexists_tac `ee` >>
     drule expr_sim_inv_mods_env >> simp[]) >>
  `value_runtime_typed env (post_value_type ce e) v` by
    (Cases_on `post_value_type ce e = expr_type e` >> simp[] >>
     `?ty fid args drv. e = Call ty (IntCall fid) args drv` by
       metis_tac[post_value_type_not_int_call] >> gvs[] >>
     Cases_on `is_word_type ty \/ is_bytestring_type ty` >>
     gvs[post_value_type_def, expr_type_def] >>
     irule (REWRITE_RULE [ETA_THM] copy_intcall_read_lowered_mods) >>
     fs[expr_body_pre_mods_def] >>
     qexistsl_tac [`cx`,`es`,`ee`,`mods`] >> simp[]) >>
  gvs[value_runtime_typed_def]
QED

Theorem ifexp_arm_inputs_mods:
  body_expr_full_ok_mods mods exps cx c /\
  (!st raw st'. eval_expr cx c st = (INL raw,st') ==> body_expr_full_ok_mods mods exps cx a) /\
  (!st raw st'. eval_expr cx c st = (INL raw,st') ==> body_expr_full_ok_mods mods exps cx b) /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env (IfExp t c a b) es ==>
  expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx (BaseT BoolT) c es /\
  !gs v es1.
    bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
    body_const_cells_agree_mods mods cx env es1 /\
    expr_body_pre_mods mods ce cx env a es1 /\ expr_body_pre_mods mods ce cx env b es1 /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty a es1 /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty b es1 /\
    (!e gs' raw ee. (e = a \/ e = b) /\
      eval_expr cx e (es1 with gas_obs := gs') = (INL raw,ee) ==>
      eval_result_typed (env,cx,ee) raw (Type (expr_type e))) /\
    !e gs' v' es2 rty.
      (e = a \/ e = b) /\ evaluate_type (get_tenv cx) t = SOME rty /\
      bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs') = (INL v',es2) ==>
      value_has_type rty v' /\
      !ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv ==>
        value_has_type ptv v'
Proof
  strip_tac >> drule_then strip_assume_tac ifexp_body_pre_children_mods >> simp[] >>
  conj_tac
  >- (drule_all_then strip_assume_tac ifexp_full_ok_value_vv_mods >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre_mods mods ce cx env c (es with gas_obs := gs)` by simp[ifexp_pre_gas_obs_mods] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  drule_then strip_assume_tac ifexp_read_landing_mods >>
  `body_const_cells_agree_mods mods cx env es1` by
    (irule ifexp_cells_at_landing_mods >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[] >> drule expr_body_pre_mods_well_typed >> simp[]) >>
  `expr_body_pre_mods mods ce cx env a es1 /\ expr_body_pre_mods mods ce cx env b es1` by simp[] >>
  `body_expr_full_ok_mods mods exps cx a /\ body_expr_full_ok_mods mods exps cx b` by metis_tac[] >>
  simp[] >>
  conj_tac
  >- (irule (cj 2 (REWRITE_RULE [IMP_CONJ_THM] ifexp_full_ok_value_vv_mods)) >>
      metis_tac[]) >>
  conj_tac
  >- (irule (cj 2 (REWRITE_RULE [IMP_CONJ_THM] ifexp_full_ok_value_vv_mods)) >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule ifexp_raw_typed_mods >>
      goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
      qexistsl_tac [`ce`,`mods`] >> gvs[ifexp_pre_gas_obs_mods]) >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre_mods mods ce cx env e (es1 with gas_obs := gs')` by gvs[ifexp_pre_gas_obs_mods] >>
  drule_all_then strip_assume_tac ifexp_read_types_mods >> gvs[]
QED
