(* Reuse the linked VV run, retaining its actual marked path for the
   successful RawCreate operand continuation. The read itself is pure. *)
Theory bodyCreateRawHeadMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyMemoryDefs
  gasOutcomeFullMods gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  bodyInvSplit bodyFullShadowBodyInv bodyPtrDefs loweringPosts valueEncoding
  supportedTypes codegenRel gasShadowState gasExplicitSites allocaHistory contextRawReachable list
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPath fragExec gasSummary
  exprSimMemorySource exprSimAttribute reasonSourceProps exprSimDefs
  stmtSimProps haltExitProj
  vyperInterpreter vyperState vyperStorageTrace vyperStorageFootprint
  gasShadow gasContext exprLowering compileEnv venomState

(* Keep the witness outside the horizon quantifier: the continuation receives
   a replay equation and a path with the very same marks. *)
Theorem raw_head_retain_marks[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R ==>
  ?marks. gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn)
    (\H res ee G' tn' t. Q H res ee G' tn' t /\ ee.gas_obs = [] /\ ~t.vs_halted /\
       (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
         (res,ee with gas_obs := tail)) /\
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G',tn')) R
Proof
  rewrite_tac[gas_outcome_full_mods_def] >> strip_tac >>
  qexists_tac `marks` >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> asm_rewrite_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      asm_rewrite_tac[] >> qx_gen_tac `H` >> strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >> simp[] >>
      disj1_tac >> gvs[] >>
      drule gas_origin_ptr_path_projections >> strip_tac >>
      drule gas_origin_path_erase >> strip_tac >>
      drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem raw_head_read_success[local]:
  vv_holds_mods cenv cx ty raw vv ee t ==>
  ?v. read_result cx raw ee = (INL v,ee)
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def]
  >- (strip_tac >> drule reason_vv_read_success >> simp[]) >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode`
  >- (simp[immutable_holds_mods_def] >>
      rpt strip_tac >> drule immutable_holds_read >> simp[]) >>
  simp[] >> strip_tac >> drule reason_vv_read_success >> simp[]
QED

val raw_head_post = ``
  vv_post_mods (H : (bool # bytes32 # type_value) list # num list)
    ctx func cenv cx code es sa a s ee raw vv t /\
  vv_store_bound cx (post_value_type cenv code) (lowered_value_type cenv code) ee raw vv t /\
  t.vs_current_bb = a.cs_current_bb /\ t.vs_inst_idx = LENGTH a.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t /\
  ptr_vv_ok cx (post_value_type cenv code) raw vv ee G1 tn1 t /\
  (!v. raw = Value v /\ ~is_word_type (post_value_type cenv code) /\
       ~is_bytestring_type (post_value_type cenv code) ==>
       vv_own cenv cx (post_value_type cenv code) sa a ee raw vv t /\
       (!tag p. vv = LocatedValue tag p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?v. read_result cx raw ee = (INL v,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv code) = SOME rt /\
              eval_operand (vv_operand vv) t = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
                val_in_memory rt v (w2n w) mem)) /\
  (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type cenv code) ==>
           ptr_buf_ok cenv code op G1 t) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
           ptr_buf_ok cenv code p.ptr_operand G1 t) /\
  ghost_kept_at lo cenv es sa G tn s G1 tn1``;

val raw_head_exit = ``\(H : (bool # bytes32 # type_value) list # num list)
                          (res:value + exception) ef
                          (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ef res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem raw_head_pure_continue[local]:
  read_result cx raw ee = (INL v,ee) /\ ee.gas_obs = [] /\ ~t.vs_halted /\
  (!w. storage_trace_frame (next w)) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (next v) (ee,t,G,tn) Q ^raw_head_exit ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (read_result cx raw) next) (ee,t,G,tn) Q ^raw_head_exit
Proof
  strip_tac >> drule_then assume_tac read_result_gas_obs >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`,`t'`,`v'`] >> BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (read_result _ _)`]
  >- simp[storage_trace_frame_read_result]
  >- first_assum ACCEPT_TAC >>
  qexists_tac `\H res mid G' tn' u. res = INL v /\ mid = ee /\ G' = G /\ tn' = tn /\ u = t` >>
  BETA_TAC >> reverse conj_tac
  >- (irule gas_outcome_full_mods_pure >> simp[] >>
      qexistsl_tac [`G`,`ee`,`INL v`,`t`,`tn`] >>
      simp[cj 1 gas_origin_ptr_path_rules, evaluation_state_component_equality]) >>
  rpt gen_tac >> strip_tac >> disj1_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  first_x_assum (drule_then strip_assume_tac) >> gvs[]
QED

Theorem raw_create_head_read_cut_mods:
  body_const_cells_agree_mods mods cx env es /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods cenv cx env code es /\ body_expr_full_ok_mods mods exps cx code /\
  compile_expr cenv (expr_type code) code sa = (vv,a) /\
  compile_expr (gas_shadow_env T cenv) (expr_type code) (gas_shadow_expr code) sh = (vv,sha) /\
  gas_shadow_state sa sh /\ gas_shadow_state a sha /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa a func /\ fn_has_code sh sha shadow_func /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_expr cx code) expr_vv_res_ok es /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!marks raw v ee t G1 tn1.
    ee.gas_obs = [] /\ ~t.vs_halted /\ storage_trace_domain cx st0 ee.storage_trace /\
    (!tail. eval_expr cx code (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL raw,ee with gas_obs := tail)) /\
    read_result cx raw ee = (INL v,ee) /\
    (!tail. bind (eval_expr cx code) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> ^raw_head_post /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1)) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (next v) (ee,t,G1,tn1) Q ^raw_head_exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (bind (eval_expr cx code) (read_result cx)) next)
    (es,s,G,tn) Q ^raw_head_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ code`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type code) code es` by
    (qpat_assum `!df lo d pg src tops ctx sh fn sfn ce en ty es.
        _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
       (qspecl_then [`DF`,`lo`,`d`,`PG`,`src`,`tops`,`ctx`,`shadow_ctx`,`func`,
                     `shadow_func`,`cenv`,`env`,`expr_type code`,`es`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> first_assum ACCEPT_TAC) >>
  qhdtm_x_assum `expr_vv_sim_full_mods` (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`a`,`sh`,`sha`,`vv`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `cut_marks` assume_tac o MATCH_MP raw_head_retain_marks) >>
  rewrite_tac[bind_assoc] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_expr cx code) _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >- (gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_result]) >>
  qexists_tac `childQ` >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`,expr_exit_def] >>
      once_rewrite_tac [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "continue"
QED

Resume raw_create_head_read_cut_mods[continue]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  rename1 `vv_post_mods _ ctx func cenv cx code es sa a s ee raw vv t` >>
  `?v. read_result cx raw ee = (INL v,ee)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule_then ACCEPT_TAC raw_head_read_success) >>
  disj1_tac >> qexists_tac `raw` >> simp[] >>
  irule raw_head_pure_continue >> simp[] >>
  qpat_assum `!marks raw v ee t G1 tn1. _ ==> _`
    (qspecl_then [`cut_marks`,`raw`,`v`,`ee`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (
    asm_rewrite_tac[] >> conj_tac
    >- (drule read_result_gas_obs >> simp[Once bind_def]) >>
    qx_gen_tac `H` >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
      (drule_then strip_assume_tac) >> gvs[])) >>
  simp[]
QED

Finalise raw_create_head_read_cut_mods
