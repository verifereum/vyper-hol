(* The raw qualified-Assign RHS stops at compile_expr, before unwrap. *)
Theory bodyQualifiedPlaceRawRhsMods
Ancestors
  bodyQualifiedPlaceRhsPostMods bodyAssignNameLinkedSetup bodyWriteSubscriptSourceMods
  bodyAssignLocalPlaceRoutesMods compileEnv gasShadow fragGasPath freshWrites
  bodyBranchCellFrameMods bodyFullIfExpReach bodyFullPostsMods bodyFullPredsMods
  reasonSourceProps exprSimAttribute exprSimMemorySource exprSimUnwrapProps exprBodyPreProps
  exprOperandVar exprLoweringProps bodyMemoryDefs loweringPosts
  stmtSimProps haltExitProj exprSimDefs gasOutcomeFullMods gasStorage gasExemptCertMods
  gasShadowCompileHelpers gasShadowCompileStmtBase vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState

Theorem raw_rhs_post_read[local]:
  vv_post_mods H ctx func cenv cx e es sa sr s0 mid pv vv u ==>
  ?v. read_result cx pv mid = (INL v,mid)
Proof
  simp[vv_post_mods_def] >> strip_tac >>
  qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
  Cases_on `vv` >> simp[vv_holds_mods_def]
  >- (strip_tac >> drule reason_vv_read_success >> simp[]) >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode`
  >- (simp[immutable_holds_mods_def] >>
      rpt strip_tac >> drule immutable_holds_read >> simp[]) >>
  simp[] >> strip_tac >> drule reason_vv_read_success >> simp[]
QED

val raw_exit =
  ``\(H : (bool # 256 word # type_value) list # num list)
      (res : 'a + exception) ee (gt : (string |-> (num # num)) # taint) r.
      expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

fun rhs_exit ty = inst [alpha |-> ty] raw_exit;
val vv_exit = rhs_exit ``:eval_result``;
val value_exit = rhs_exit ``:value``;

(* read_result changes neither the source state nor the machine path.
   Select the source value at the canonical horizon before proving the
   postcondition at every horizon on the same path. *)
Theorem raw_rhs_counted_read[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx e) (es,s0,G0,tn0) Q ^vv_exit /\
  (!H res mid G tn u. Q H res mid G tn u ==>
    ?pv v. res = INL pv /\ read_result cx pv mid = (INL v,mid)) /\
  (!marks H pv v mid G tn u.
    (eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL pv,mid)) /\ read_result cx pv mid = (INL v,mid) /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G0,tn0) marks (OK u,G,tn) /\ Q H (INL pv) mid G tn u ==>
    P H (INL v) mid G tn u) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) P ^value_exit
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac
      >- (irule gas_bad_storage_at_bind_left >> simp[storage_trace_frame_read_result]) >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> asm_rewrite_tac[])
  >- suspend "counted" >>
  disj2_tac >> disj2_tac >>
  simp[force_ignore_bind_action] >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  reverse conj_tac >- (qexists_tac `H` >> asm_rewrite_tac[]) >>
  irule gas_exempt_cert_mods_error_result >> first_assum ACCEPT_TAC
QED

Resume raw_rhs_counted_read[counted]:
  disj2_tac >> disj1_tac >>
  Cases_on `res` >- suspend "normal" >>
  rename1 `INR exc` >>
  qexistsl_tac [`INR exc`,`ee`,`r`,`G'`,`tn'`] >>
  simp[Once bind_def] >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[]
  >- (qpat_assum `!H res mid G tn u. Q H res mid G tn u ==> _`
        (drule_then strip_assume_tac) >> gvs[]) >>
  disj2_tac >> metis_tac[expr_exit_INR_type,halt_exit_INR_type]
QED

Resume raw_rhs_counted_read[normal]:
  rename1 `INL pv` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >>
  disch_then (CONJUNCTS_THEN2 kall_tac
    (qx_choose_then `t` (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac))) >>
  qpat_assum `!H res mid G tn u. Q H res mid G tn u ==> _`
    (drule_then (qx_choosel_then [`raw`,`v`] strip_assume_tac)) >> gvs[] >>
  drule_then (assume_tac o SIMP_RULE (srw_ss()) []) read_result_gas_obs >>
  qexistsl_tac [`INL v`,`ee`,`OK t`,`G'`,`tn'`] >>
  conj_tac >- simp[Once bind_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >>
  simp[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_assum `!tail. read_result _ _ _ = _` (qspec_then `[]` assume_tac) >>
  qpat_assum `!marks H pv v mid G tn u. _ ==> P _ _ _ _ _ _`
    (drule_all_then ACCEPT_TAC)
QED

Finalise raw_rhs_counted_read[local]

Theorem qualified_place_raw_rhs_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  body_expr_full_ok_mods mods exps cx e /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  assign_place_rhs_code_mods cenv bt e sa = (SOME vv,sr) /\
  assign_place_rhs_code_mods (gas_shadow_env T cenv) (gas_shadow_target bt)
    (gas_shadow_expr e) shadow_sa = (SOME vv,shadow_sr) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sr func /\ fn_has_code shadow_sa shadow_sr shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst t. frag_reachable ctx func s0 fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res mid Gu tu u. ?v. res = INL v /\
      qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
        es sa shadow_sa sr shadow_sr (SOME vv) s0 G0 tn0 H v mid Gu tu u)
    ^value_exit
Proof
  strip_tac >> strip_tac >>
  `compile_expr cenv (expr_type e) e sa = (vv,sr)` by
    (qpat_x_assum `assign_place_rhs_code_mods cenv bt e sa = _` mp_tac >>
     Cases_on `compile_expr cenv (expr_type e) e sa` >>
     simp[assign_place_rhs_code_mods_def,comp_bind_def,comp_return_def]) >>
  drule_all_then (qx_choose_then `sh` strip_assume_tac) assign_name_shadow_raw_rhs_mods >>
  `shadow_sr = sh` by
    (qpat_x_assum `assign_place_rhs_code_mods _ (gas_shadow_target _) _ _ = _` mp_tac >>
     simp[assign_place_rhs_code_mods_def,gas_shadow_expr_type,gas_shadow_is_empty_value_expr,
          gas_shadow_target_to_expr,gas_shadow_expr_can_mutate,comp_bind_def,comp_return_def]) >>
  qpat_x_assum `shadow_sr = sh` (SUBST_ALL_TAC o SYM) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_full_ok_mods _ _ _ _`
       (mp_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     strip_tac >> qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es. _ ==> _`
       (drule_all_then (mp_tac o SIMP_RULE bool_ss [FORALL_AND_THM])) >> simp[]) >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sr`,`shadow_sa`,`shadow_sr`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mk_asm "open_run") >>
  irule raw_rhs_counted_read >> asm "open_run" (irule_at Any) >> BETA_TAC >>
  reverse conj_tac
  >- (rpt strip_tac >> qexists_tac `tv` >> simp[] >> drule_then ACCEPT_TAC raw_rhs_post_read) >>
  suspend "entry_post"
QED

Resume qualified_place_raw_rhs_mods[entry_post]:
  rpt gen_tac >> strip_tac >>
  asm_x "open_run" kall_tac >>
  qpat_x_assum `INL pv = INL tv` (SUBST_ALL_TAC o SRULE []) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    simp[Once bind_def] >>
  `expr_body_pre_mods mods cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `body_const_cells_agree_mods mods cx env
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qpat_assum `compile_expr cenv _ e sa = _`
    (mp_then Any strip_assume_tac (cj 1 compile_expr_grows)) >>
  qpat_assum `compile_expr cenv _ e sa = _`
    (mp_then (Pos hd) (drule_then assume_tac) (cj 1 compiler_compile_var)) >>
  `local_ptrs_reserved cenv sr` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `return_buf_frame d cenv sr u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `wb_frame cenv es mid sa s0 u` by
    (pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_then assume_tac gas_origin_ptr_path_erase >>
  drule_then (assume_tac o cj 1) gas_path_normal >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >> metis_tac[]) >>
  `!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC gas_origin_ptr_path_dalloca_fmp_headroom) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sr x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sr x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  qexists_tac `v` >> simp[qualified_place_rhs_post_mods_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`gas_explicit marks s0.vs_gas_readings`,`tv`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a. tv = Value a /\ _ ==> vv_own _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `v0` mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (assume_tac o cj 1) >>
      qpat_x_assum `tv = Value v0` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  qpat_x_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _`
    (drule_all_then strip_assume_tac) >> gvs[]
QED

Finalise qualified_place_raw_rhs_mods
