(* Compose one linked forced-word run with a reached continuation. *)
Theory bodyReachedWordBindMods
Ancestors
  bodyFullPostsMods bodyFullIfExpReach exprSimFullBundleProps
  stmtSimForRounds gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasOutcomeFullPostPathMods gasExemptCertMods gasContext
  vyperStorageTrace vyperStorageFootprint vyperState exprSimDefs
Libs monadsyntax

Triviality reached_word_head_admissible:
  gas_admissible (bind source next) expr_res_ok es ==>
  gas_admissible (source : evaluation_state -> value evaluation_result) expr_res_ok es
Proof
  simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum irule >> qexistsl_tac [`ee`,`gs`] >> simp[bind_def]
QED

(* Shared source quotation only, not an object-logic predicate. *)
val word_post = ``
  expr_post_mods (H : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx e es sa sb s0 ee v op t /\
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

Theorem reached_word_bind_mods:
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  is_word_type (expr_type e) /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa = (op,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (bind (eval_expr cx e) (read_result cx))
    (next : value -> evaluation_state -> value evaluation_result)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
     (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==> R H res ee gt r) /\
  (!marks v ee G tn t.
     (!tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> ^word_post) /\
     gas_admissible (next v) expr_res_ok ee ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 (next v) (ee,t,G,tn) Q R) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next)
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >> fs[expr_sim_full_code_def] >>
  drule_then assume_tac reached_word_head_admissible >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`!v. storage_trace_frame (next v)`] >- first_assum ACCEPT_TAC >>
  qexists_tac `\H res ee G tn t. ?v. res = INL v /\ ^word_post` >>
  conj_tac >- suspend "continue" >>
  suspend "post"
QED

Resume reached_word_bind_mods[continue]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `gas_admissible (next v) expr_res_ok ee` by
    (`ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
     qpat_assum `gas_admissible (bind (bind (eval_expr cx e) _) next) _ es`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >>
     disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,`v`,`ee`] mp_tac) >>
     simp[]) >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  first_x_assum irule >> simp[] >> conj_tac
  >- (qexists_tac `marks` >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> ?w. res = INL w /\ _`
    (drule_then strip_assume_tac) >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Resume reached_word_bind_mods[post]:
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G tn t. childQ H res ee G tn t /\
     (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)`, `childR`] >>
  reverse (rpt conj_tac)
  >- (irule gas_outcome_full_mods_post_path >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[] >> rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[])
  >- (simp[Abbr `childR`] >> gen_tac >> Cases >> simp[expr_exit_def] >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  simp[Abbr `childQ`] >> rpt strip_tac >> qexists_tac `v` >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise reached_word_bind_mods
