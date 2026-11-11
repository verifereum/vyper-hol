(* Actual semantic value facts at a successful typed Return read. *)
Theory externalReturnSiteSemantics
Ancestors externalReturnSiteProbe valueTypingMemoryProps exprSimHypsDefs
  vyperTypeEvalSoundness vyperTypeArgFits vyperTyping vyperTypeExprSoundness
  vyperTypeSystem vyperTypeInvariants vyperInterpreter vyperState

Theorem return_site_value_semantics:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
  type_widens_to (get_tenv cx) (expr_type e) ret /\
  ?atv dtv. evaluate_type (get_tenv cx) (expr_type e) = SOME atv /\
    evaluate_type (get_tenv cx) ret = SOME dtv /\
    value_has_type atv v /\ value_has_type dtv v /\
    val_wf dtv v /\ safe_cast dtv v = SOME v
Proof
  rpt strip_tac >>
  `well_typed_expr env e /\
   type_widens_to env.type_defs (expr_type e) ret` by
    (gvs[type_stmt_def, AllCaseEqs()]) >>
  `env_consistent env cx es /\ state_well_typed es /\
   accounts_well_typed es.accounts /\ context_well_typed cx /\
   functions_well_typed cx` by gvs[expr_sim_inv_def] >>
  drule_all eval_expr_read_type_sound >> simp[] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  gvs[value_runtime_typed_def] >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  metis_tac[value_has_type_memory_wf, safe_cast_well_typed]
QED

Theorem return_site_destination_wf:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  evaluate_type (get_tenv cx) ret = SOME dtv ==>
  val_wf dtv v
Proof
  rpt strip_tac >> drule_all return_site_value_semantics >>
  strip_tac >> gvs[]
QED

Theorem return_site_destination_cast:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  evaluate_type (get_tenv cx) ret = SOME dtv ==>
  safe_cast dtv v = SOME v
Proof
  metis_tac[return_site_cast]
QED

(* The next two are exprSimHyps' ifexp_intcall_read_cast and
   ifexp_intcall_read_physical_typed without its expr_body_pre premise, which
   a Return consumer does not have. *)
Theorem return_intcall_read_cast[local]:
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,params,dflts,ret,bd) /\
  (do r <- eval_expr cx (Call ty (IntCall (src,fn)) args drv);
      read_result cx r od) es = (INL v,es') ==>
  ?rtv rv. evaluate_type (get_tenv cx) ret = SOME rtv /\ safe_cast rtv rv = SOME v
Proof
  strip_tac >>
  qpat_x_assum `(do r <- eval_expr _ _; read_result _ r od) _ = _`
    (assume_tac o ONCE_REWRITE_RULE [evaluate_def]) >>
  fs[ignore_bind_def] >>
  rpt (dxrule vyperStatePreservationTheory.bind_split >> strip_tac >> gvs[]) >>
  gvs[lift_option_type_def, return_def, raise_def, read_result_def] >>
  Cases_on `evaluate_type (get_tenv cx) ret` >> gvs[raise_def, return_def] >>
  rename1 `safe_cast rtv rv` >>
  Cases_on `safe_cast rtv rv` >> gvs[raise_def, return_def] >>
  metis_tac[]
QED

Theorem return_intcall_physical_typed:
  expr_sim_inv ce cx env es /\
  well_typed_expr env (Call ty (IntCall fid) args drv) /\
  (do r <- eval_expr cx (Call ty (IntCall fid) args drv);
      read_result cx r od) es = (INL v,es') ==>
  ?stv. evaluate_type (get_tenv cx)
    (lowered_value_type ce (Call ty (IntCall fid) args drv)) = SOME stv /\
    value_has_type stv v
Proof
  strip_tac >> PairCases_on `fid` >>
  `env_context_consistent env cx` by
    gvs[expr_sim_inv_def, env_consistent_def] >>
  fs[expr_sim_inv_def, well_typed_expr_def,
     exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  qpat_x_assum `!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==> _` drule >>
  disch_then SUBST1_TAC >>
  `fn_sigs_consistent env.fn_sigs cx` by
    gvs[env_context_consistent_def] >>
  fs[fn_sigs_consistent_def] >>
  qpat_x_assum `!src fn sig. FLOOKUP env.fn_sigs (src,fn) = SOME sig ==> _` drule >>
  strip_tac >>
  drule_all return_intcall_read_cast >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[vyperTypingTheory.safe_cast_result_well_typed]
QED

(* The callee's declared return type widens to the call's annotation. *)
Theorem return_intcall_lowered_widens:
  expr_sim_inv ce cx env es /\
  well_typed_expr env (Call ty (IntCall fid) args drv) ==>
  type_widens_to (get_tenv cx)
    (lowered_value_type ce (Call ty (IntCall fid) args drv)) ty
Proof
  strip_tac >> PairCases_on `fid` >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  pop_assum (SUBST1_TAC o GSYM) >>
  gvs[expr_sim_inv_def, well_typed_expr_def, exprLoweringTheory.lowered_value_type_def,
      vyperASTTheory.expr_type_def] >>
  metis_tac[type_widens_to_def]
QED
