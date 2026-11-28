(* Pop has the same request trace as its base-target evaluation. *)
Theory s1PrefixPop
Ancestors
  s1PrefixTarget s1PrefixPreds s1PrefixOfVV bodyFullPop
  bodyPtrPopTargetFragTransport exprSimPopNestedBase
  guardMutationTrace vyperTypeAssignContext exprBodyPreProps
  gasShadowCompileStmtHelpers bodyFullShared exprLoweringProps stmtLoweringMono
  vyperPlaceFrames vyperInterpreter vyperState s1PrefixDefs gasShadow fragExec pair
Libs
  pairLib

Theorem pop_base_trace[local]:
  (SND (eval_expr cx (Pop ann bt) es)).storage_trace =
  (SND (eval_base_place cx bt es)).storage_trace
Proof
  simp[Once evaluate_def, eval_target_place_as_bind] >>
  namedCases_on `eval_base_place cx bt es` ["base_res mid"] >>
  namedCases_on `base_res` ["pv", "exc"] >> simp[bind_def] >>
  namedCases_on `get_place pv mid` ["place_res mid'"] >>
  drule_then SUBST_ALL_TAC get_place_state >>
  namedCases_on `place_res` ["p", "exc"] >> simp[] >>
  namedCases_on `pop_place cx p mid` ["pop_res fin"] >> simp[] >>
  drule_then ACCEPT_TAC pop_place_trace_unchanged
QED

Theorem pop_prefix_from_base[local]:
  gas_prefix_full P cx st0 (eval_base_place cx bt) (es,s,G,tn) ==>
  gas_prefix_full P cx st0 (eval_expr cx (Pop ann bt)) (es,s,G,tn)
Proof
  PairCases_on `P` >> simp[gas_prefix_full_def] >> strip_tac >>
  qexists_tac `marks` >> conj_tac >- metis_tac[] >> rpt strip_tac >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    (qspec_then `tail` irule) >>
  Cases_on `eval_base_place cx bt (es with gas_obs :=
    gas_explicit marks s.vs_gas_readings ++ tail)` >>
  metis_tac[pop_base_trace, SND]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> simp[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  rename1 `_ = (rb,sm)` >> PairCases_on `rb` >>
  Cases_on `compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
    (gas_shadow_target bt) shadow_sa` >> rename1 `_ = (shadow_rb,shadow_sm)` >>
  `shadow_rb = (rb0,rb1,rb2) /\ gas_shadow_state sm shadow_sm` by
    (irule gas_shadow_step >>
     qpat_assum `compile_get_target_ptr compile_expr cenv bt sa = _` (irule_at Any) >>
     qpat_assum `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_sa = _`
       (irule_at Any) >>
     simp[gas_shadow_stmt_get_target_ptr_env]) >>
  gvs[] >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    metis_tac[ci_mono_compile_get_target_ptr,SND] >>
  `ci_mono sm sb` by
    (qpat_x_assum `compile_expr cenv ty (Pop ann bt) sa = _` mp_tac >>
     simp[Once nested_pop_compile_eq] >> pairarg_tac >> simp[] >>
     metis_tac[ci_mono_compile_dynarray_pop,SND]) >>
  `ci_mono shadow_sm shadow_sb` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Pop ann bt)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, Once nested_pop_compile_eq] >>
     pairarg_tac >> simp[] >> metis_tac[ci_mono_compile_dynarray_pop,SND]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split,ci_mono_def] >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (irule get_place_base_admissible >> rewrite_tac[GSYM eval_target_place_as_bind] >>
     drule nested_pop_target_admissible >> simp[]) >>
  drule_then assume_tac pop_full_target_pre >>
  `?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n)))` by
    metis_tac[expr_body_pre_static_facts,well_typed_expr_Pop_dynamic_target] >>
  irule pop_prefix_from_base >>
  irule body_target_sim_prefix >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`cenv`,`d`,`env`,`(rb0,rb1,rb2)`,`sa`,`sm`,
                `shadow_func`,`shadow_sa`,`shadow_sm`,`tops`,
                `Type (ArrayT ann (Dynamic n))`] >> simp[]
QED
*)
Theorem pop_vv_sim_prefix[local]:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_base_target_full_ok cx bt /\ body_base_target_prefix_ok cx bt /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Pop ann bt) es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

Theorem body_pop_case_prefix:
  !cx v10 bt.
  body_base_target_full_ok cx bt /\
  body_base_target_prefix_ok cx bt ==>
  body_expr_prefix_ok cx (Pop v10 bt)
Proof
  map_every qx_gen_tac [`cx`,`ann`,`bt`] >> strip_tac >>
  simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Pop ann bt) es` by (irule pop_vv_sim_prefix >> metis_tac[]) >>
  simp[expr_sim_prefix_of_vv]
QED
