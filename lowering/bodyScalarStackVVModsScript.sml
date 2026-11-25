(* Unforcing a scalar stack result preserves the linked execution witness. *)
Theory bodyScalarStackVVMods
Ancestors
  bodyFullPostsMods exprSimStack exprSimMemDefs exprSimDefs
  gasOutcomeFullMods gasExemptCertMods gasStorage loweringPosts stmtSimProps
  bodyPtrDefs context exprLowering compileEnv vyperInterpreter vyperState

Theorem stack_unforce_outcome_mods[local]:
  (!s tv t. eval_expr cx e s = (INL tv,t) ==> ?v. tv = Value v) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,f,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) Q R /\
  (!H v ee g n u. Q H (INL v) ee g n u ==> Q' H (INL (Value v)) ee g n u) /\
  (!H ex ee g n u. Q H (INR ex) ee g n u ==> Q' H (INR ex) ee g n u) /\
  (!H v ee gt r. R H (INL v) ee gt r ==> R' H (INL (Value v)) ee gt r) /\
  (!H ex ee gt r. R H (INR ex) ee gt r ==> R' H (INR ex) ee gt r) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,f,PG) mods cx st0
    (eval_expr cx e) (es,s,G,tn) Q' R'
Proof
  strip_tac >> drule eval_expr_force_value >> strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_full_mods_def]) >>
  REWRITE_TAC[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> reverse conj_tac
      >- (qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
          asm_rewrite_tac[]) >>
      fs[gas_bad_storage_at_def] >> gen_tac >>
      qmatch_goalsub_abbrev_tac `eval_expr cx e st` >>
      Cases_on `bind (eval_expr cx e) (read_result cx) st` >>
      first_x_assum drule >> strip_tac >>
      qpat_x_assum `!tail. ~storage_trace_domain _ _ _`
        (qspec_then `tail` mp_tac) >> gvs[Abbr `st`])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`case res of INL v => INL (Value v) | INR ex => INR ex`,
                   `ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- (gen_tac >> first_x_assum irule >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> strip_tac >> first_x_assum drule >>
      Cases_on `res` >> simp[] >> strip_tac >> simp[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  conj_tac >- (irule gas_exempt_cert_mods_unforce_result >> simp[]) >>
  qexists_tac `H` >> asm_rewrite_tac[]
QED

Theorem stack_word_vv_post_mods[local]:
  is_word_type (post_value_type cenv e) /\
  expr_post_mods H ctx f cenv cx e es sa sb s0 ee v op u ==>
  vv_post_mods H ctx f cenv cx e es sa sb s0 ee (Value v) (StackValue a op) u
Proof
  simp[expr_post_mods_def, expr_post_def, vv_post_mods_def, vv_holds_mods_def,
       vv_holds_def, vv_at_def, vv_place_ptr_mods_def, vv_place_ptr_def,
       vv_own_def, read_result_def, return_def, vv_storage_live_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem scalar_stack_vv_sim_full_mods:
  !DF lo d ctx sh PG f sf cenv cx ty e es.
    is_word_type (post_value_type cenv e) /\
    expr_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es /\
    (!sa. ?a op sb. compile_expr cenv ty e sa = (StackValue a op,sb)) /\
    (!s tv t. eval_expr cx e s = (INL tv,t) ==> ?v. tv = Value v) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es
Proof
  rw[expr_vv_sim_full_mods_def] >>
  qpat_x_assum `!sa. ?a op sb. _` (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
    (op,shadow_sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  drule_all_then assume_tac eval_expr_force_admissible >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`op`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule stack_unforce_outcome_mods >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[])
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      simp[ptr_vv_ok_def, vv_location_def, read_result_def, return_def] >>
      conj_tac >- (irule stack_word_vv_post_mods >> simp[]) >>
      irule vv_store_bound_stack_value >> simp[]) >>
  rpt strip_tac >> gvs[expr_exit_success_map, halt_exit_def] >>
  ONCE_REWRITE_TAC[INST_TYPE [beta |-> ``:value``] expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED
