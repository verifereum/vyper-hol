(* Counted left-to-right operand runs for strict word-layout binary operators. *)
Theory bodyBopWordOperandsMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullIfExpReach bodyInvCodeProps
  bodyWriteSubscriptSourceMods exprSimFullBundleProps bodyMemoryDefs
  exprBopSimProps gasContext stmtSimForRounds exprBodyPreProps
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  gasExemptCertMods gasStorage gasShadowState gasShadow
  exprLoweringProps loweringPosts bodyPtrDefs freshWrites
  vyperStorageTrace vyperStorageFootprint vyperState compileEnv
  fragExec list exprSimDefs contextRawReachable ptrDiscipline unitMemInv
  exprSimHypsDefs vyperTypeSystem vyperTypeBuiltins vyperTypeCallGraph
  vyperTypeCallStackSoundness supportedExprTraverse allocLimits
Libs monadsyntax

Theorem bop_operand_pres_mods[local]:
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_body_pre_mods mods cenv cx env e1 es /\
  !mid. expr_sim_inv_mods mods cenv cx env mid ==>
        expr_body_pre_mods mods cenv cx env e2 mid
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, well_typed_builtin_app_def,
       int_calls_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, EVERY_APPEND] >>
  strip_tac >>
  drule_then assume_tac call_evaluation_safe_append_left >>
  drule_then assume_tac call_evaluation_safe_append_right >>
  fs[constSubstCorrectTheory.frame_well_typed_exprs_cons]
QED

Theorem bop_child_value_sim_mods[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >> qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (first_x_assum irule >> simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem bop_forced_storage_frame[local]:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx))
Proof
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result]
QED

Theorem bop_admissible_head[local]:
  gas_admissible (bind src next) expr_res_ok es ==>
  gas_admissible (src : evaluation_state -> value evaluation_result) expr_res_ok es
Proof
  simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum irule >> qexistsl_tac [`ee`,`gs`] >> simp[bind_def]
QED

(* These quotations abbreviate the matching post and exit formulas in the
   specifications below; they introduce no constants in the object logic. *)
val op_post = ``
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

val op_exit = ``expr_exit (res : value + vyperState$exception) r /\
  halt_exit (H : (bool # 256 word # type_value) list # num list) cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem bop_bind_word_run_mods[local]:
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  is_word_type (expr_type e) /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa = (op,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!H res ee gt r. ^op_exit ==> R H res ee gt r) /\
  (!marks v ee G tn t.
     (!tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> ^op_post) ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 (next v) (ee,t,G,tn) Q R) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next)
    (es,s0,G0,tn0) Q R
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
  >~ [`storage_trace_frame (bind _ _)`] >- simp[bop_forced_storage_frame]
  >~ [`!v. storage_trace_frame (next v)`] >- first_assum ACCEPT_TAC >>
  qexists_tac `\H res ee G tn t. ?v. res = INL v /\ ^op_post` >>
  conj_tac >- suspend "continue" >>
  suspend "post"
QED

Resume bop_bind_word_run_mods[continue]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  first_x_assum irule >> simp[] >> conj_tac
  >- (qexists_tac `marks` >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> ?w. res = INL w /\ _`
    (drule_then strip_assume_tac) >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Resume bop_bind_word_run_mods[post]:
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

Finalise bop_bind_word_run_mods

Theorem bop_operands_cps_exit_mods:
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  bop <> In /\ bop <> NotIn /\
  body_exprs_full_ok_mods mods exps cx [e1;e2] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e1) shadow_sa =
    (x,shadow_s1) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e2) shadow_s1 =
    (y,shadow_s2) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,shadow_sa,shadow_s1) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s1,s2,shadow_s1,shadow_s2) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= s1.cs_next_var /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H res ee gt r. ^op_exit ==> R H res ee gt r) /\
  (!left v1 mid G1 tn1 t right v2 fin G2 tn2 u.
    (!tail. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
      (INL v1,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post_mods H ctx func cenv cx e1 es sa s1 s0 mid v1 x t /\
      expr_store_bound cx (expr_type e1) v1 x t /\
      t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
      ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\ ~t.vs_halted /\ mid.gas_obs = [] /\
      (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)) /\
    (!tail. bind (eval_expr cx e2) (read_result cx)
      (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
      (INL v2,fin with gas_obs := tail)) /\
    storage_trace_domain cx st0 fin.storage_trace /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      expr_post_mods H ctx func cenv cx e2 mid s1 s2 t fin v2 y u /\
      expr_store_bound cx (expr_type e2) v2 y u /\
      u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      t.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx fin G2 tn2 u /\
      ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 u /\
      ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\ ~u.vs_halted /\ fin.gas_obs = [] /\
      (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z)) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0
      (\ee. (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 ee,ee))
      (fin,u,G2,tn2) Q R) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >> drule_then strip_assume_tac bop_operand_pres_mods >>
  fs[Once body_exprs_full_ok_mods_def] >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    (irule bop_child_value_sim_mods >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     fs[expr_sim_full_code_def] >> qexists_tac `func` >> simp[]) >>
  qpat_x_assum `gas_admissible _ _ _`
    (assume_tac o PURE_REWRITE_RULE [REWRITE_RULE [ETA_AX] eval_expr_bop_bind]) >>
  pure_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (drule bop_admissible_head >> simp[]) >>
  irule bop_bind_word_run_mods >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- simp[storage_trace_frame_bind_all,bop_forced_storage_frame,storage_trace_frame_def,
          exprBopSimDefsTheory.bop_result_def] >>
  qexistsl_tac [`d`,`x`,`sa`,`s1`,`shadow_func`,`shadow_sa`,`shadow_s1`,`expr_type e1`] >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  suspend "left_cut"
QED

Resume bop_operands_cps_exit_mods[left_cut]:
  qx_genl_tac [`left`,`v1`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit left s0.vs_gas_readings) = (INL v1,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn frame =>
      qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
        (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL,frame])))) >>
  `expr_body_pre_mods mods cenv cx env e1
     (es with gas_obs := gas_explicit left s0.vs_gas_readings) /\
   body_const_cells_agree_mods mods cx env
     (es with gas_obs := gas_explicit left s0.vs_gas_readings)` by
    simp[bodyBranchCellFrameModsTheory.body_const_cells_agree_mods_branch_updates] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  `body_expr_full_ok_mods mods exps cx e2` by
    (drule (REWRITE_RULE [ETA_AX] exprSimSourceTheory.eval_expr_read_INL) >> strip_tac >>
     qpat_assum `_ ==> body_exprs_full_ok_mods mods exps cx [e2]` mp_tac >>
     (impl_tac >- (rpt (goal_assum (drule_at Any)))) >>
     simp[Once body_exprs_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e2 mid` by
    (irule bop_child_value_sim_mods >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  suspend "right_start"
QED

Resume bop_operands_cps_exit_mods[right_start]:
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    (qpat_assum `gas_admissible (bind (bind (eval_expr cx e1) _) _) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >> BETA_TAC >>
     disch_then (drule_then mp_tac) >> simp[] >>
     disch_then (ACCEPT_TAC o MATCH_MP bop_admissible_head)) >>
  `return_buf_frame d cenv s1 t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     fs[expr_post_mods_def,expr_post_def]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at s1 z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  irule bop_bind_word_run_mods >> simp[] >>
  suspend "right_cut"
QED

Resume bop_operands_cps_exit_mods[right_cut]:
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[storage_trace_frame_def,exprBopSimDefsTheory.bop_result_def] >>
  qexistsl_tac [`d`,`y`,`s1`,`s2`,`shadow_func`,`shadow_s1`,`shadow_s2`,`expr_type e1`] >>
  simp[] >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      fs[expr_post_mods_def,expr_post_def]) >>
  qx_genl_tac [`right`,`v2`,`fin`,`G2`,`tn2`,`u`] >> strip_tac >>
  qpat_assum `!l v m g n t r w f g' n' u. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (qspecl_then [`left`,`v1`,`mid`,`G1`,`tn1`,`t`,`right`,`v2`,`fin`,`G2`,`tn2`,`u`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (rpt gen_tac >> strip_tac >> first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      simp[] >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Finalise bop_operands_cps_exit_mods
