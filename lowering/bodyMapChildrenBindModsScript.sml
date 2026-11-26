(* Sequence a linked mapping base and its index before selecting the result. *)
Theory bodyMapChildrenBindMods
Ancestors
  bodyFullPostsMods bodyFullIfExpReach gasOutcomeFullMods gasOutcomeFullBindMods
  gasOutcomeFullPostMods gasExemptCertMods exprSimSubscriptMap exprSimSubscriptArraySource
  bodyFullTargetSubscript stmtSimForRounds haltExitProj exprSimMapDefs exprSimDefs
  bodyMemoryDefs exprLoweringProps freshWrites gasContext gasShadow gasShadowState
  vyperInterpreter vyperState vyperAST vyperStorageTrace vyperStorageFootprint
  fragExec fragGasOriginPtr contextRawReachable venomState venomInst list

Theorem map_bind_keep_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 f (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 f (es,s,G,tn)
    (\H res ee G' tn' t. Q H res ee G' tn' t /\
      ?marks. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (OK t,G',tn')) R
Proof
  rewrite_tac[gas_outcome_full_mods_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >> rpt (goal_assum (drule_at Any)) >> simp[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >> simp[] >> qexists_tac `marks` >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem map_key_bind_admissible[local]:
  (!ex. A (INR ex : eval_result + exception) ==> expr_res_ok (INR ex)) /\
  gas_admissible (bind key next) A mid ==>
  gas_admissible key expr_res_ok mid
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def]
QED

Theorem map_bind_horizon[local]:
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := obs) = (res,fin) /\
  valid_horizon cx st0 H fin.storage_trace ==>
  valid_horizon cx st0 H mid.storage_trace
Proof
  strip_tac >>
  qpat_assum `bind _ _ _ = _`
    (mp_then (Pat `_ = _`) mp_tac valid_horizon_frame) >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result]
QED

(* These two posts are the normal arms of the existing linked simulations,
   kept here as the continuation interface without adding HOL definitions. *)
val base_post = ``\(H : (bool # 256 word # type_value) list # num list) res ee G tn t. ?tr slot kt vt tp p.
  res = INL (HashMapRef tr slot kt vt) /\
  storage_mapping_region cx tr slot (HashMapT kt vt) /\
  bvv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand t = SOME slot /\
  stmt_state_rel H ctx func cenv cx ee t /\
  immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
       off+sz <= b \/ b+sz' <= off) ==>
     mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
  locals_kept cenv es ee s0 t /\ (~expr_has_effect obj ==> pure_frame cenv func es sa s0 t) /\
  return_buf_frame d cenv sa t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val key_post = ``\(H : (bool # 256 word # type_value) list # num list) res ee G tn t. ?v. res = INL v /\
  expr_post_mods H ctx func cenv cx idx mid sm sn t1 ee v iop t /\
  expr_store_bound cx (post_value_type cenv idx) v iop t /\
  t.vs_current_bb = sn.cs_current_bb /\ t.vs_inst_idx = LENGTH sn.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  t1.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv idx) v iop G tn t /\
  (~is_word_type (post_value_type cenv idx) ==> ptr_buf_ok cenv idx iop G t) /\
  ghost_kept_at lo cenv mid sm G1 tn1 t1 G tn``;

val expr_failure = ``\(H : (bool # 256 word # type_value) list # num list) (res : eval_result + exception) ee
  (gt : (string |-> num # num) # taint) q. expr_exit res q /\ halt_exit H cx ee res q /\
   (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s)``;

Theorem mapping_children_bind_mods:
  ~subscript_reads_base cx obj idx /\
  (!ex. A (INR ex) ==> expr_res_ok (INR ex)) /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) A es /\
  compile_expr cenv ty obj sa = (bvv,sm) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa = (bvv,shadow_sm) /\
  lower_value compile_expr cenv (expr_type idx) idx sm = (iop,sn) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type idx)
    (gas_shadow_expr idx) shadow_sm = (iop,shadow_sn) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_state sn shadow_sn /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  fn_has_code sm sn func /\ fn_has_code shadow_sm shadow_sn shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  expr_map_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty obj es /\
  (!obs br mid. eval_expr cx obj (es with gas_obs := obs) = (INL br,mid) ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type idx) idx mid) /\
  (!bobs br mid t1 G1 tn1 kobs v fin t2 G2 tn2.
    (!tail. eval_expr cx obj (es with gas_obs := bobs ++ tail) = (INL br,mid with gas_obs := tail)) /\
    (!tail. bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := kobs ++ tail) =
            (INL v,fin with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ storage_trace_domain cx st0 fin.storage_trace /\
    mid.gas_obs = [] /\ fin.gas_obs = [] /\ ~t1.vs_halted /\ ~t2.vs_halted /\
    gas_admissible (select_result cx (expr_type obj) br (ValueSubscript v)) A fin /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==> valid_horizon cx st0 H mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> ^base_post H (INL br) mid G1 tn1 t1) /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==> ^key_post H (INL v) fin G2 tn2 t2) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (select_result cx (expr_type obj) br (ValueSubscript v))
      (fin,t2,G2,tn2) Q ^expr_failure) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_expr cx (Subscript ann obj idx)) (es,s0,G0,tn0) Q ^expr_failure
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!ex. A (INR ex) ==> expr_map_res_ok (INR ex)` by
    (rpt strip_tac >> first_x_assum drule >> simp[expr_map_res_ok_def,expr_res_ok_def]) >>
  `gas_admissible (eval_expr cx obj) expr_map_res_ok es` by
    (irule subscript_result_base_admissible >> qexistsl_tac [`A`,`ann`,`idx`] >> simp[]) >>
  drule eval_expr_subscript_bind >>
  disch_then (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  qhdtm_x_assum `expr_map_sim_full_mods` (mp_tac o REWRITE_RULE [expr_map_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_then (assume_tac o MATCH_MP map_bind_keep_path) >>
  suspend "base_bind"
QED

Resume mapping_children_bind_mods[base_bind]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_expr cx obj) _ baseQ baseR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
      irule gas_exempt_cert_mods_bind_result >> goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_select,storage_trace_frame_bind_all,
           evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "key_entry" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_expr _ _) _ baseQ baseR` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `baseR`] >> gen_tac >> Cases >> simp[expr_exit_def]
QED

Resume mapping_children_bind_mods[key_entry]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t1`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `baseQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res = INL (HashMapRef _ _ _ _)` SUBST_ALL_TAC >>
  qabbrev_tac `br = HashMapRef tr slot kt vt` >>
  qabbrev_tac `bobs = gas_explicit marks s0.vs_gas_readings` >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_expr cx obj (es with gas_obs := bobs) = (INL br,mid)` by
    (qpat_assum `!tail. eval_expr cx obj (es with gas_obs := _ ++ tail) = _`
       (qspec_then `[]` mp_tac) >> rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[th]) >>
     simp[NoAsms,Abbr `bobs`,Abbr `br`]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type idx) idx mid` by
    (qpat_assum `!obs br mid. _ ==> expr_sim_full_mods _ _ _ _ _ _` drule >> simp[]) >>
  `gas_admissible (bind (bind (eval_expr cx idx) (read_result cx))
       (\v. select_result cx (expr_type obj) br (ValueSubscript v))) A mid` by
    (qpat_assum `gas_admissible (bind (eval_expr cx obj) _) A es`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >>
     BETA_TAC >> disch_then (drule_then mp_tac) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok mid` by
    (irule map_key_bind_admissible >>
     qexistsl_tac [`A`, `\v. select_result cx (expr_type obj) br (ValueSubscript v)`] >>
     asm_rewrite_tac[]) >>
  suspend "key_run"
QED

Resume mapping_children_bind_mods[key_run]:
  disj1_tac >> qexists_tac `br` >> conj_tac >- simp[Abbr `br`] >>
  `!fn inst s. frag_reachable ctx func t1 fn inst s ==> dalloca_fmp_headroom inst s` by
    (match_mp_tac (GEN_ALL gas_origin_ptr_path_dalloca_fmp_headroom) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t1,G1,tn1)` (irule_at Any) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `return_buf_frame d cenv sm t1` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sm`,`sn`,`shadow_sm`,`shadow_sn`,`iop`,`t1`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> simp[])) >> strip_tac >>
  suspend "key_bind"
QED

Resume mapping_children_bind_mods[key_bind]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (bind (eval_expr cx idx) _) _ keyQ keyR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
      irule gas_exempt_cert_mods_bind_value >> goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_select] >>
  qexists_tac `\H res ee G tn t. keyQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "select" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ _) _) _ keyQ keyR` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `keyR`,Abbr `baseR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[expr_exit_def] >> metis_tac[expr_exit_INR_retype,halt_exit_INR_type]
QED

Resume mapping_children_bind_mods[select]:
  qx_genl_tac [`marks2`,`res`,`fin`,`G2`,`tn2`,`t2`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `keyQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  qabbrev_tac `kobs = gas_explicit marks2 t1.vs_gas_readings` >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  `gas_admissible (select_result cx (expr_type obj) br (ValueSubscript v)) A fin` by
    (qpat_assum `gas_admissible (bind (bind (eval_expr _ _) _) _) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >>
     BETA_TAC >> disch_then (drule_then mp_tac) >> simp[]) >>
  `bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := kobs) = (INL v,fin)` by
    (qpat_assum `!tail. bind (eval_expr _ _) _ _ = _` (qspec_then `[]` mp_tac) >>
     rewrite_tac[APPEND_NIL] >>
     qpat_assum `fin with gas_obs := [] = fin` (fn th => rewrite_tac[th]) >>
     simp[NoAsms,Abbr `kobs`]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` by
    (rpt strip_tac >> drule_all map_bind_horizon >> simp[]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==> ^key_post H (INL v) fin G2 tn2 t2` by
    (BETA_TAC >> gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> ^base_post H (INL br) mid G1 tn1 t1` by
    (BETA_TAC >> gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms,Abbr `br`]) >>
  qpat_assum `!bobs br mid t1 G1 tn1 kobs v fin t2 G2 tn2. _ ==> _` irule >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G1`,`bobs`,`kobs`,`mid`,`t1`,`tn1`] >>
  conj_tac
  >- (qpat_assum `!tail. eval_expr cx obj (es with gas_obs := _ ++ tail) = _` mp_tac >>
      simp[NoAsms,Abbr `bobs`,Abbr `br`]) >>
  conj_tac
  >- (qpat_assum `!tail. bind (eval_expr cx idx) _ _ = _` mp_tac >>
      simp[NoAsms,Abbr `kobs`]) >>
  RULE_ASSUM_TAC BETA_RULE >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise mapping_children_bind_mods
