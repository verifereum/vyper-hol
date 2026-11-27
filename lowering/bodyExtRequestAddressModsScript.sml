(* The linked ExtCall address slice and its reached continuation. *)
Theory bodyExtRequestAddressMods
Ancestors
  bodySliceWordEntryMods bodyWriteSubscriptSourceMods bodyFullPredsMods
  bodyForcedStorageFrameMods
  exprBodyPreProps exprWordOperand exprSimSend exprBopSimProps exprSimWordArgs
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  gasExemptCertMods stmtSimForRounds haltExitProj stmtSimProps exprSafeOperand
  exprSimFullBundleProps bodyFullIfExpReach bodyFullPostsMods vyperStorageTrace
  exprSimDefs loweringPosts compileEnv vyperState vyperStorageFootprint
Libs monadsyntax

Triviality address_return_bind:
  bind (return x) f = f x
Proof
  simp[bind_def,return_def,FUN_EQ_THM]
QED

Triviality address_list_action:
  eval_exprs cx [addr] =
  bind (bind (eval_expr cx addr) (read_result cx)) (\v. return [v])
Proof
  simp[eval_exprs_cons_action, eval_exprs_nil, bind_def, return_def, FUN_EQ_THM]
QED

val word_post = ``\e es sa sb s0 ee v op t G0 tn0 G tn
    (H:(bool # 256 word # type_value) list # num list).
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_store_bound cx (expr_type e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  ~t.vs_halted /\ ee.gas_obs = [] /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)``;

val entry = ``\es sa s0 G0 tn0.
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val outcome = ``\(source : evaluation_state -> eval_result evaluation_result).
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 source``;

val exit_post = ``\(H:(bool # 256 word # type_value) list # num list)
    (res:eval_result + vyperState$exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem ext_request_address_bind_mods:
  body_exprs_full_ok_mods mods exps cx [addr] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env addr es /\
  expr_type addr = BaseT AddressT /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
    (gas_shadow_expr addr) shadow_sa = (ao,shadow_sm) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sm,shadow_sa,shadow_sm) /\
  ^entry es sa s0 G0 tn0 /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  gas_admissible (bind (eval_expr cx addr) (read_result cx)) expr_res_ok es /\
  (!vs. storage_trace_frame (k vs)) /\
  (!obs1 v target aw mid G1 tn1 t.
    eval_exprs cx [addr] (es with gas_obs := obs1) = (INL [v],mid) /\
    dest_AddressV v = SOME target /\ eval_operand ao t = SOME aw /\ w2w aw = target /\
    safe_operand sm ao /\ expr_sim_inv_mods mods cenv cx env mid /\
    body_const_cells_agree_mods mods cx env mid /\
    storage_trace_domain cx st0 mid.storage_trace /\ ^entry mid sm t G1 tn1 /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       ^word_post addr es sa sm s0 mid v ao t G0 tn0 G1 tn1 H) ==>
    ^outcome (k [v]) (mid,t,G1,tn1) Q ^exit_post) ==>
  ^outcome (bind (eval_exprs cx [addr]) k) (es,s0,G0,tn0) Q ^exit_post
Proof
  BETA_TAC >> strip_tac >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ [_]`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ addr`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (BaseT AddressT) addr es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (BaseT AddressT) addr es` by
    (qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _` irule >>
     simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  fs[expr_sim_full_code_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qexists_tac `func` >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`ao`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  REWRITE_TAC[address_list_action] >> ONCE_REWRITE_TAC[bind_assoc] >>
  BETA_TAC >> REWRITE_TAC[address_return_bind] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- irule bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >~ [`!v. storage_trace_frame (k [v])`] >- simp[] >>
  qexists_tac `\H res ee G tn t. ?v. res = INL v /\
    ^word_post addr es sa sm s0 ee v ao t G0 tn0 G tn H` >>
  BETA_TAC >> conj_tac >- suspend "continue" >> suspend "post"
QED

Resume ext_request_address_bind_mods[continue]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?v. _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       ^word_post addr es sa sm s0 mid v ao t G0 tn0 G1 tn1 H` by
    (BETA_TAC >> qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?v'. _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     gvs[] >> first_assum ACCEPT_TAC) >>
  pop_assum (assume_tac o BETA_RULE) >>
  `is_word_type (expr_type addr)` by simp[is_word_type_def] >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qabbrev_tac `obs = gas_explicit marks s0.vs_gas_readings` >>
  `bind (eval_expr cx addr) (read_result cx) (es with gas_obs := obs) = (INL v,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn frame =>
       qpat_assum `!tail. bind (eval_expr cx addr) _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,frame])))) >>
  `expr_body_pre_mods mods cenv cx env addr (es with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  `value_has_type (BaseTV AddressT) v` by
    (qpat_assum `value_runtime_typed _ _ v` mp_tac >>
     qpat_assum `expr_type addr = _` (fn th => PURE_REWRITE_TAC [th]) >>
     simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def,vyperValueTheory.evaluate_type_def]) >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ mid` (mp_then Any assume_tac expr_sim_inv_mods_env) >>
  drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (rpt strip_tac >> drule_all exprSimSourceTheory.env_consistent_var_type_evaluates >>
     simp[vyperTypeSystemTheory.well_formed_type_def]) >>
  drule_all_then strip_assume_tac lower_value_word_shape >>
  `safe_operand sm ao` by simp[safe_operand_def] >>
  `post_value_type cenv addr = BaseT AddressT` by
    (qpat_assum `expr_type addr = _` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
     irule post_value_type_word >> first_assum ACCEPT_TAC) >>
  `eval_operand ao t = SOME (typed_val_to_w256 (BaseTV AddressT) v)` by
    (irule expr_val_rel_typed >> qexistsl_tac [`cx`,`BaseT AddressT`] >>
     simp[is_word_type_def,vyperValueTheory.evaluate_type_def] >>
     qpat_assum `expr_post_mods (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
     qpat_assum `expr_val_rel _ _ v ao t` mp_tac >>
     qpat_assum `post_value_type cenv addr = _` (fn th => PURE_REWRITE_TAC [th]) >> simp[]) >>
  `eval_exprs cx [addr] (es with gas_obs := obs) = (INL [v],mid)` by
    simp[address_list_action,Once bind_def,return_def] >>
  `^entry mid sm t G1 tn1 /\
   bind (eval_expr cx addr) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (BETA_TAC >> irule (BETA_RULE slice_word_next_entry_mods) >>
     unabbrev_all_tac >> asm_rewrite_tac[] >>
     qexistsl_tac [`G0`,`ao`,`sa`,`tn0`] >> asm_rewrite_tac[] >> simp[] >>
     qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     fs[] >>
     qpat_assum `expr_store_bound cx (expr_type addr) v ao t` mp_tac >>
     qpat_assum `expr_type addr = _` (fn th => PURE_REWRITE_TAC[th]) >> simp[]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `^entry mid sm t G1 tn1` (strip_assume_tac o BETA_RULE) >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  qpat_assum `!obs1 v aw mid G1 tn1 t. _`
    (qspecl_then [`obs`,`v`,`typed_val_to_w256 (BaseTV AddressT) v`,`mid`,`G1`,`tn1`,`t`]
       MATCH_MP_TAC) >>
  asm_rewrite_tac[] >> irule address_typed_dest >> first_assum ACCEPT_TAC
QED

Resume ext_request_address_bind_mods[post]:
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G tn t. childQ H res ee G tn t /\
     (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)`, `childR`] >>
  reverse (rpt conj_tac)
  >- (irule gas_outcome_full_mods_post_path >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[] >> rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[])
  >- (simp[Abbr `childR`] >> gen_tac >> Cases >> simp[expr_exit_def] >>
      rpt strip_tac >>
      ONCE_REWRITE_TAC[INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                       INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  simp[Abbr `childQ`] >> rpt strip_tac >> qexists_tac `v` >>
  `post_value_type cenv addr = expr_type addr` by
    (irule post_value_type_word >> simp[is_word_type_def]) >>
  fs[] >>
  qpat_assum `expr_type addr = BaseT AddressT`
    (fn th => PURE_ONCE_REWRITE_TAC[GSYM th]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise ext_request_address_bind_mods
