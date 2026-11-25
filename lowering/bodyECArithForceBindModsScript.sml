(* Bind a reached linked operand read, retaining its full value post. *)
Theory bodyECArithForceBindMods
Ancestors
  bodyFullPostsMods bodyFullIfExpReach exprSimFullBundleProps
  bodyForcedStorageFrameMods gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasOutcomeFullPostPathMods gasExemptCertMods haltExitProj stmtSimProps exprSimDefs
  vyperStorageTrace vyperStorageFootprint
Libs monadsyntax

val forced = ``bind (eval_expr cx e) (read_result cx)``;
val operand_post = ``
  expr_post_mods (H : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_store_bound cx (post_value_type cenv e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val headroom = ``!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u``;
val parent_exit = ``\(H : (bool # 256 word # type_value) list # num list) (res : eval_result + exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem ec_arith_force_bind_mods:
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa = (op,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible ^forced expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!marks v ee G tn t.
     (!tail. ^forced (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\ ~t.vs_halted /\ ee.gas_obs = [] /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> ^operand_post) /\ ^headroom ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0 (next v) (ee,t,G,tn) Q ^parent_exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (bind ^forced next) (es,s0,G0,tn0) Q ^parent_exit
Proof
  strip_tac >> fs[expr_sim_full_code_def] >>
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
  >- ACCEPT_TAC bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >~ [`!v. storage_trace_frame (next v)`] >- first_assum ACCEPT_TAC >>
  qexists_tac `\H res ee G tn t. (?v. res = INL v /\ ^operand_post) /\
                                ~t.vs_halted /\ ee.gas_obs = [] /\ ^headroom` >>
  conj_tac >- suspend "continue" >>
  suspend "post"
QED

Resume ec_arith_force_bind_mods[continue]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> pure_rewrite_tac[REFL_CLAUSE, AND_CLAUSES] >>
  qpat_assum `!marks v ee G tn t. _` irule >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qexists_tac `marks` >> first_assum ACCEPT_TAC)
  >- (qx_gen_tac `H` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[]) >>
  first_assum ACCEPT_TAC
QED

Resume ec_arith_force_bind_mods[post]:
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G tn t. childQ H res ee G tn t /\ ^headroom`, `childR`] >>
  reverse (rpt conj_tac)
  >- (irule gas_outcome_full_mods_post_path >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[] >> rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[])
  >- (simp[Abbr `childR`] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  simp[Abbr `childQ`] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC
QED

Finalise ec_arith_force_bind_mods
