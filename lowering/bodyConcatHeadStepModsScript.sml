(* A reached Concat operand and its copy, on a single linked run. *)
Theory bodyConcatHeadStepMods
Ancestors
  bodyConcatCutsMods list
  bodyConcatCompileCutsMods bodyConcatHeadSourceMods bodyConcatChildFrameMods
  bodyConcatFrameLawsMods bodyConcatCopyFrameMods bodyConcatBytesCopyMods
  bodyConcatFixedCopyMods gasOutcomeFullPostMods exprBodyPreTypingProps
  exprBodyPreCallSafetyProps exprSimDefs vyperState exprSimFullBundleProps
  bodyFullPostsMods bodyFullPredsMods exprOperandVar
  vyperStorageTrace vyperStorageFootprint
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeInvariants
  vyperExprNoControl gasContext
Libs monadsyntax

Theorem concat_operand_admissible[local]:
  expr_body_pre_mods mods cenv cx env e es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by simp[] >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ (_ with gas_obs := _)`
    (strip_assume_tac o MATCH_MP expr_body_pre_mods_runtime_typing) >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  `no_type_error_result (INR y : value + vyperState$exception)` by
    (qpat_assum `bind _ _ _ = (INR _,_)`
       (mp_then Any mp_tac (REWRITE_RULE [ETA_AX] eval_expr_read_type_sound)) >>
     disch_then (qspec_then `env` mp_tac) >>
     fs[runtime_consistent_def,gas_obs_type_invariants] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `no_control_exc y` by
    (qpat_assum `bind _ _ _ = (INR _,_)` mp_tac >>
     simp[NoAsms,bind_def,AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control,read_result_no_control]) >>
  Cases_on `y` >> gvs[expr_res_ok_def,no_control_exc_def,no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem concat_head_step_mods:
  !e args sb shadow_sa shadow_sb es sa s G tn bs P.
    concat_loop_entry_mods (mods,exps,cx,env,src,tops,st0,cenv,pure)
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) scratch anchor
      (e::args) (sb,shadow_sa,shadow_sb) (es,sa,s,G,tn) bs P ==>
    concat_head_cut_mods (mods,exps,cx,env,src,tops,st0,cenv,pure)
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) scratch anchor
      e args (sb,shadow_sa,shadow_sb) (es,sa,s,G,tn) bs P
Proof
  PairCases_on `scratch` >> PairCases_on `anchor` >>
  rewrite_tac[concat_loop_entry_mods_def,concat_loop_code_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `EVERY _ (e::args)`
    (map_every assume_tac o CONJUNCTS o BETA_RULE o REWRITE_RULE[EVERY_DEF]) >>
  drule_all_then strip_assume_tac concat_cons_compile_cuts_mods >>
  rename1 `lower_value _ cenv _ e sa = (op,sc)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (op,shadow_sc)` >>
  rename1 `compile_concat _ _ args _ _ _ s2 = ((),sb)` >>
  rename1 `compile_concat _ _ (MAP gas_shadow_expr args) _ _ _ shadow_s2 = ((),shadow_sb)` >>
  rename1 `arm sc = ((),s2)` >>
  `expr_body_pre_mods mods cenv cx env e es` by
    (first_x_assum irule >> simp[]) >>
  rewrite_tac[concat_head_cut_mods_def] >>
  qexistsl_tac [`op`,`sc`,`shadow_sc`,`s2`,`shadow_s2`] >>
  asm_rewrite_tac[] >> conj_tac
  >- suspend "outcome" >>
  suspend "success"
QED

Resume concat_head_step_mods[outcome]:
  `body_expr_full_ok_mods mods exps cx e` by
    (qpat_assum `body_exprs_full_ok_mods _ _ _ (_::_)`
       (ACCEPT_TAC o cj 1 o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def])) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_full_ok_mods _ _ _ e`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!df l0 d0 pg src tops ctx shctx f shf ce env ty ee.
                  _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
       (irule o GEN_ALL o cj 1 o SPEC_ALL o REWRITE_RULE [IMP_CONJ_THM]) >>
     rpt conj_tac >> rpt (goal_assum (drule_at Any))) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule concat_operand_admissible >> goal_assum (drule_at Any)) >>
  qpat_assum `expr_sim_full_code _ (sa,sc,shadow_sa,shadow_sc)`
    (strip_assume_tac o MATCH_MP expr_sim_full_code_fields) >>
  qpat_assum `concat_live_mods _ _ _ bs`
    (strip_assume_tac o REWRITE_RULE [concat_live_mods_def]) >>
  qpat_assum `expr_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sc`,`shadow_sa`,`shadow_sc`,`op`,`s`,`G`,`tn`] mp_tac o
     REWRITE_RULE [expr_sim_full_mods_def]) >>
  (impl_tac >- (asm_rewrite_tac[] >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> concat_horizon_mods _ _ _`
        (mp_tac o REWRITE_RULE[concat_horizon_mods_def]) >> simp[])) >>
  disch_then assume_tac >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[concat_head_post_mods_def,expr_sim_full_endpoint_def,AC CONJ_ASSOC CONJ_COMM]
QED

Resume concat_head_step_mods[success]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  drule_all_then strip_assume_tac concat_head_read_source_mods >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME tv` >>
  `?xs. mid.storage_trace = es.storage_trace ++ xs` by
    (qpat_assum `bind _ _ _ = (INL v,_)`
       (mp_then Any mp_tac storage_trace_frame_prefix) >>
     simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  `storage_trace_domain cx st0 es.storage_trace` by
    (irule storage_trace_domain_prefix >> qexists `xs` >> fs[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` drule) >>
     pure_rewrite_tac[concat_horizon_mods_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `pure ==> ~expr_has_effect e` by fs[EXISTS_DEF] >>
  `!z. op = Var z ==> not_fresh_at sc z` by
    (qpat_assum `lower_value _ cenv _ e sa = _`
       (mp_then Any mp_tac compile_lower_value_var) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       concat_live_mods (func,cenv,lo)
         (scratch0,scratch1,scratch2,scratch3,scratch4,scratch5,scratch6) (mid,sc,t,G1,tn1) bs /\
       concat_old_frame_mods (func,cenv,lo,pure)
         (scratch0,scratch1,scratch2,scratch3,scratch4,scratch5,scratch6)
         (es,sa,s,G,tn) (mid,sc,t,G1,tn1) /\
       concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (mid,sc,t,G1,tn1) /\
       local_ptrs_reserved cenv sc /\ return_buf_frame d cenv sc t /\
       (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z) /\
       (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     drule_all_then strip_assume_tac concat_child_frame_mods >>
     asm_rewrite_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> concat_live_mods _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` drule) >> strip_tac >>
  `concat_old_frame_mods (func,cenv,lo,pure)
     (scratch0,scratch1,scratch2,scratch3,scratch4,scratch5,scratch6)
     (anchor0,anchor1,anchor2,anchor3,anchor4) (mid,sc,t,G1,tn1)` by
    (irule concat_old_frame_compose_mods >>
     qpat_assum `concat_old_frame_mods _ _ (es,sa,s,G,tn) (mid,sc,t,G1,tn1)` (irule_at Any) >>
     asm_rewrite_tac[] >> FAIL_TAC "reservation at the anchor") >>
  FAIL_TAC "assemble reached copy"
QED

Finalise concat_head_step_mods
