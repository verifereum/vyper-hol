(* Force the source operand of an ordinary Slice, retaining its full post. *)
Theory bodySliceOrdinarySourceBindMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodySliceWordEntryMods
  bodyWriteSubscriptSourceMods exprSimSliceCompose exprSimFullBundleProps
  bodyForcedStorageFrameMods bodyFullIfExpReach gasOutcomeFullPostMods
  gasOutcomeFullBindMods gasOutcomeFullPostPathMods gasExemptCertMods
  gasContext haltExitProj stmtSimProps stmtSimDefs stmtSimForRounds exprSimSource exprSimDefs
  exprSimHypsDefs vyperStorageTrace vyperStorageFootprint vyperState
  vyperTypeExprSoundness vyperValue compileEnv loweringPosts
Libs monadsyntax

val forced = ``\e. bind (eval_expr cx e) (read_result cx)``;
val outcome = ``\(source : evaluation_state -> eval_result evaluation_result).
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 source``;

val child = ``\e.
  lower_value compile_expr cenv ty e sa = (op,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shm) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sm,sha,shm) /\
  sa.cs_next_var <= sm.cs_next_var``;

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
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val post = ``\e v ec G tn t (H:(bool # 256 word # type_value) list # num list).
  expr_post_mods H ctx func cenv cx e es sa sm s0 ec v op t /\
  expr_store_bound cx (post_value_type cenv e) v op t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ec G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  ~t.vs_halted /\ ec.gas_obs = [] /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)``;

val cut = ``\e marks v ec G tn t.
  (!tail. ^forced e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL v,ec with gas_obs := tail)) /\
  storage_trace_domain cx st0 ec.storage_trace /\
  (!H. valid_horizon cx st0 H ec.storage_trace ==> ^post e v ec G tn t H)``;

val exit_weaken = ``!(H : (bool # 256 word # type_value) list # num list)
  (res : eval_result + vyperState$exception) ee
  (gt : (string |-> num # num) # taint) r. expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==> R H res ee gt r``;

Triviality slice_source_head_sim:
  body_exprs_full_ok_mods mods exps cx (e::rest) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _` irule >>
     simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Triviality slice_reached_source:
  body_exprs_full_ok_mods mods exps cx (e::rest) /\
  expr_body_pre_mods mods cenv cx env e es /\ body_const_cells_agree_mods mods cx env es /\
  ^forced e (es with gas_obs := obs) = (INL v,ec) ==>
  body_exprs_full_ok_mods mods exps cx rest /\ expr_sim_inv_mods mods cenv cx env ec /\
  body_const_cells_agree_mods mods cx env ec /\
  value_runtime_typed env (expr_type e) v /\ MAP FDOM ec.scopes = MAP FDOM es.scopes
Proof
  BETA_TAC >> strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  drule_then (assume_tac o SRULE []) eval_read_preserves_scopes_dom >>
  simp[] >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ (_::_)` mp_tac >>
  simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
  qpat_x_assum `_ ==> body_exprs_full_ok_mods mods exps cx rest` irule >>
  rpt (goal_assum (drule_at Any))
QED

Triviality slice_source_post_type:
  (is_bytestring_type (expr_type e) \/ (?m. expr_type e = BaseT (BytesT (Fixed m)))) /\
  value_runtime_typed env (expr_type e) v ==>
  post_value_type cenv e = expr_type e
Proof
  strip_tac >- simp[] >>
  fs[value_runtime_typed_def] >>
  `m <= 32` by gvs[vyperValueTheory.evaluate_type_def,AllCaseEqs()] >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule (Q.SPEC `cenv` post_value_type_word) >> simp[]
QED

Theorem slice_ordinary_source_bind_mods:
  body_exprs_full_ok_mods mods exps cx [e;start;len] /\
  (is_bytestring_type (expr_type e) \/ (?m. expr_type e = BaseT (BytesT (Fixed m)))) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  ^child e /\ ^entry es sa s0 G0 tn0 /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  gas_admissible (bind (^forced e) next) expr_vv_res_ok es /\
  (!v. storage_trace_frame (next v)) /\ ^exit_weaken /\
  (!marks v ec G tn t.
    ^cut e marks v ec G tn t /\ ^entry ec sm t G tn /\
    post_value_type cenv e = expr_type e /\
    body_exprs_full_ok_mods mods exps cx [start;len] /\
    expr_sim_inv_mods mods cenv cx env ec /\ body_const_cells_agree_mods mods cx env ec /\
    value_runtime_typed env (expr_type e) v /\ MAP FDOM ec.scopes = MAP FDOM es.scopes /\
    gas_admissible (next v) expr_vv_res_ok ec ==>
    ^outcome (next v) (ec,t,G,tn) Q R) ==>
  ^outcome (bind (^forced e) next) (es,s0,G0,tn0) Q R
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (irule slice_source_head_sim >> qexistsl_tac [`env`,`exps`,`mods`,`[start;len]`,`src`,`tops`] >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     fs[expr_sim_full_code_def] >> qexists_tac `func` >> simp[]) >>
  drule_then assume_tac slice_gas_admissible_expr_head >>
  qpat_x_assum `expr_sim_full_code _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_full_code_def]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then assume_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- ACCEPT_TAC bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >~ [`!v. storage_trace_frame (next v)`] >- first_assum ACCEPT_TAC >>
  qexists_tac `\H res ec G tn t. ?v. res = INL v /\ ^post e v ec G tn t H` >>
  conj_tac >- suspend "continue" >> suspend "post"
QED

Resume slice_ordinary_source_bind_mods[continue]:
  qx_genl_tac [`marks`,`res`,`ec`,`G`,`tn`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ec.storage_trace) ec.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ec.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `ec with gas_obs := [] = ec` by simp[evaluation_state_component_equality] >>
  `^forced e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ec)` by
    (BETA_TAC >> qpat_assum `ec with gas_obs := [] = ec` (fn frame =>
       qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
        (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,frame])))) >>
  `body_exprs_full_ok_mods mods exps cx [start;len] /\ expr_sim_inv_mods mods cenv cx env ec /\
   body_const_cells_agree_mods mods cx env ec /\ value_runtime_typed env (expr_type e) v /\
   MAP FDOM ec.scopes = MAP FDOM es.scopes` by
    (irule (BETA_RULE slice_reached_source) >> asm_rewrite_tac[] >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     qpat_assum `(_ : value evaluation_result) = (INL v,ec)` (ACCEPT_TAC o BETA_RULE)) >>
  pop_assum strip_assume_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule slice_source_post_type >> asm_rewrite_tac[] >>
     qexistsl_tac [`env`,`v`] >> first_assum ACCEPT_TAC) >>
  `^entry ec sm t G tn /\
   ^forced e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ec)` by
    (BETA_TAC >> irule (BETA_RULE slice_word_next_entry_mods) >>
     asm_rewrite_tac[] >> qexistsl_tac [`G0`,`op`,`sa`,`tn0`] >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ec.storage_trace ==> _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  pop_assum (strip_assume_tac o BETA_RULE) >>
  `gas_admissible (next v) expr_vv_res_ok ec` by
    (qpat_assum `gas_admissible (bind (bind (eval_expr cx e) _) next) _ es`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >>
     disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,`v`,`ec`] mp_tac) >> simp[]) >>
  disj1_tac >> qexists_tac `v` >> pure_rewrite_tac[REFL_CLAUSE,AND_CLAUSES] >>
  qpat_assum `!marks v ec G tn t. _ ==> gas_outcome_full_mods _ _ _ _ (next v) _ _ _` irule >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexists_tac `marks` >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ec.storage_trace ==> ?w. INL v = INL w /\ _`
    (drule_then strip_assume_tac) >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Resume slice_ordinary_source_bind_mods[post]:
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ec G tn t. childQ H res ec G tn t /\
     (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)`, `childR`] >>
  reverse (rpt conj_tac)
  >- (irule gas_outcome_full_mods_post_path >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[] >> rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[])
  >- (simp[Abbr `childR`] >> qx_genl_tac [`H`,`res`,`ee`,`gt`,`r`] >>
      Cases_on `res` >> simp[expr_exit_def] >> strip_tac >> first_x_assum irule >>
      ONCE_REWRITE_TAC[INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                       INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  simp[Abbr `childQ`] >> rpt strip_tac >> qexists_tac `v` >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise slice_ordinary_source_bind_mods
