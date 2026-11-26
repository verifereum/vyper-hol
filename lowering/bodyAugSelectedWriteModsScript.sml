(* The store uses the selected place and the actual post-RHS state. *)
Theory bodyAugSelectedWriteMods
Ancestors
  bodyAugReadOnlyFrameMods augAssignFullCurrentSource augAssignFullCodeStages
  bodyFullShared stmtSimLogCompose bodySimStmtFacts bodyFullUnwrapRun
  wordArgsPtr exprBodyPreProps immutableRegionTypingProps
  bodyFullSubscriptLiveImmSelect immutableDeployAssignMemoryFrame
  vyperFiniteStoragePreservation vyperEvalExprPreservesScopesDom
  vyperStorageTrace gasOutcomeFullMods stmtSimDeclStore
  bodyWriteTargetStageMods vyperPlaceStatePreservation stmtSimAugAssignPlaceMemory
  exprSimWordArgs freshWrites vyperState bodyFullPostsMods loweringPosts
  vyperValue vyperTyping allocLimits targetOverlapAccess bodySimAugPlaceLoad
  vyperSubscriptOverlap vyperImmutableAccessFrame bodyImmutableAugAssignStore
  bodyInvCodeProps vyperTypeEnv vyperTypeInvariants exprSimSource
  bodyInvSplit vyperValueOperation context bodyFullShadowBodyInv exprSimProps compileEnv
  list stmtSimForArrayFrame targetPlaceSim moduleVariableKeyProps supportedNameRoot
  stmtSimAugAssign vyperStorageFootprint gasContext exprLoweringProps bodyFullTargetDefs

Theorem aug_selected_write_admissible[local]:
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  (!gs. eval_stmt cx (AugAssign ty bt bop e) (es with gas_obs := prefix ++ gs) =
        write_place cx p v (ee with gas_obs := gs)) /\
  ee.gas_obs = [] ==>
  gas_admissible (write_place cx p v) (stmt_res_ok lctx) ee
Proof
  strip_tac >> drule_all aug_place_replay_admissible >> simp[]
QED

Theorem aug_selected_scopes_dom[local]:
  eval_target_place cx bt (es with gas_obs := reads) = (INL p,mid) /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := rhsReads) = (INL rhs,ee) ==>
  MAP FDOM mid.scopes = MAP FDOM es.scopes /\ MAP FDOM ee.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >> conj_tac
  >- (drule eval_target_place_preserves_scopes_dom >> simp[]) >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  drule read_result_state >> disch_then SUBST_ALL_TAC >>
  drule eval_expr_preserves_scopes_dom >> simp[]
QED

Theorem aug_selected_write_frame[local]:
  stmt_state_rel H ctx func cenv cx es s0 /\
  stmt_state_rel H ctx func cenv cx mid u /\
  wb_frame cenv es mid sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
  expr_post_mods H ctx func cenv cx e mid s1 s2 u ee rhs rhsop q /\
  ghost_kept_at lo cenv mid s1 Gu tu u Gq tq /\
  storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee Gq tq q /\
  target_ptr_ok cenv (PlaceR p) r Gq tq q /\
  MAP FDOM mid.scopes = MAP FDOM es.scopes /\ MAP FDOM ee.scopes = MAP FDOM mid.scopes /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s2 /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s2.cs_next_var <= s3.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
  (!x. FST r = Var x ==> not_fresh_at s2 x) /\
  return_buf_frame d cenv s2 q /\ return_buf_sep d cenv es s0 /\
  (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) w) /\
  alloca_history func q /\
  state_frame w = state_frame (q with vs_inst_idx := w.vs_inst_idx) /\
  tnw.t_mem = tq.t_mem /\ tnw.t_stor = tq.t_stor /\
  tnw.t_trans = tq.t_trans /\ tnw.t_imm = tq.t_imm /\
  (!x. not_fresh_at s2 x ==> lookup_var x w = lookup_var x q /\
    FLOOKUP Gw x = FLOOKUP Gq x /\ op_taint tnw (Var x) = op_taint tq (Var x)) /\
  fn_has_code s2 s3 func /\ s3.cs_current_bb = s2.cs_current_bb /\
  s3.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 s3 /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts s2 s3) /\
  q.vs_current_bb = s2.cs_current_bb /\ q.vs_inst_idx = LENGTH s2.cs_current_insts /\
  w.vs_inst_idx = LENGTH s3.cs_current_insts ==>
  stmt_state_rel H ctx func cenv cx ee w /\ immutable_frame_mods func cenv cx ee w /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gw tnw w /\
  target_ptr_ok cenv (PlaceR p) r Gw tnw w /\ eval_operand (FST r) w = eval_operand (FST r) q /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gw tnw /\ wb_frame cenv es ee sa s0 w /\
  alloca_frame cenv es sa s0 cenv ee w /\ return_buf_frame d cenv s3 w /\
  return_buf_sep d cenv ee w /\ alloca_history func w
Proof
  strip_tac >> qpat_x_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then assume_tac expr_post_state >>
  `wb_frame cenv mid ee s1 u q` by drule_then ACCEPT_TAC expr_post_frame >>
  `wb_frame cenv es ee sa s0 q` by
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl_tac [`mid`,`s1`,`u`] >> simp[]) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ es s0`))) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gq tq` by suspend "ghost" >>
  `sa.cs_next_var <= s2.cs_next_var` by decide_tac >>
  drule_all_then strip_assume_tac (GEN_ALL augassign_read_only_frame_mods) >>
  simp[] >> conj_tac
  >- (irule log_wb_alloca_frame >> simp[] >> conj_tac
      >- (qexists_tac `ee` >> simp[]) >>
      goal_assum (drule_at Any)) >>
  irule return_buf_sep_locals_kept >> simp[] >>
  qexistsl_tac [`H`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >> simp[] >>
  metis_tac[wb_frame_vars]
QED

Resume aug_selected_write_frame[ghost]:
  `!n b sz. local_region cenv mid.scopes u n b sz <=> local_region cenv es.scopes s0 n b sz` by
    (rpt gen_tac >> sym_tac >> irule wb_frame_local_regions >> conj_tac
     >- simp[] >> conj_tac
     >- (qexistsl_tac [`mid`,`sa`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b` by
    fs[wb_frame_def] >>
  irule ghost_kept_at_trans >> qexistsl_tac [`Gu`,`mid`,`u`,`s1`,`tu`] >> simp[]
QED

Finalise aug_selected_write_frame

Theorem aug_selected_nested_nonword[local]:
  evaluate_type tenv root_ty = SOME rtv /\ mem_path_offset rtv (h::t) = SOME (k,ptv) ==>
  ~is_word_type root_ty
Proof
  strip_tac >> Cases_on `root_ty` >> simp[is_word_type_def] >>
  rpt strip_tac >> gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `h` >> gvs[mem_path_offset_def, mem_step_offset_def, is_word_type_def] >>
  rename1 `mem_step_offset _ (ValueSubscript x)` >> Cases_on `x` >> gvs[mem_step_offset_def]
QED

Theorem aug_selected_no_write[local]:
  ~aug_assign_overlap cenv bt e /\
  MEM ref (nonconstant_reads cenv.ce_modules (expr_accesses cenv.ce_modules (target_to_expr bt))) /\
  ~var_is_prim_word cenv ref ==>
  ~MEM (WriteAcc ref) (expr_accesses cenv.ce_modules e)
Proof
  simp[aug_assign_overlap_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem aug_selected_memory_source[local]:
  eval_target_place cx bt (es with gas_obs := reads) = (INL (MemoryPlace id path),mid) /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := rhsReads) = (INL rhs,ee) /\
  ~aug_assign_overlap cenv bt e /\
  cenv.ce_var_type id = SOME root_ty /\ evaluate_type (get_tenv cx) root_ty = SOME rtv /\
  mem_path_offset rtv path = SOME (k,ptv) /\
  lookup_scopes id mid.scopes = SOME entry /\ evaluate_subscripts entry.type entry.value path = INL old ==>
  ?ent now. lookup_scopes id ee.scopes = SOME ent /\ evaluate_subscripts ent.type ent.value path = INL now
Proof
  strip_tac >> `lookup_scopes id (mid with gas_obs := rhsReads).scopes = SOME entry` by simp[] >>
  Cases_on `path`
  >- (drule_all (REWRITE_RULE [ETA_AX] aug_place_rhs_entry_type) >>
      simp[evaluate_subscripts_def] >> metis_tac[]) >>
  `~is_word_type root_ty` by drule_all_then ACCEPT_TAC aug_selected_nested_nonword >>
  `target_root bt = NameTarget id` by metis_tac[eval_target_place_memory_root, place_access_root] >>
  `~MEM (WriteAcc (LocalRef id)) (expr_accesses cenv.ce_modules e)` by
    (irule aug_selected_no_write >> conj_tac
     >- simp[var_is_prim_word_def, target_place_type_def] >>
     qexists_tac `bt` >> simp[target_root_local_nonconstant_read]) >>
  `~MEM (WriteAcc (LocalRef id)) (accesses_expr e)` by fs[expr_accesses_def, MEM_APPEND] >>
  drule_all (REWRITE_RULE [ETA_AX] aug_place_rhs_memory_entry) >> simp[] >> metis_tac[]
QED

Theorem aug_selected_immutable_tag[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  FLOOKUP env.bare_globals (owner,id) = SOME root_ty /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) ==>
  evaluate_type (get_tenv cx) root_ty = SOME itv
Proof
  strip_tac >> drule_then assume_tac expr_sim_inv_mods_env >>
  fs[env_consistent_def, env_immutables_consistent_def] >>
  qpat_assum `!src id ty tv v. _ ==> evaluate_type _ ty = SOME tv`
    (qspecl_then [`owner`,`id`,`root_ty`,`itv`,`old`] mp_tac) >> simp[]
QED

Theorem aug_selected_immutable_key[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env mid /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) ==>
  (!tops. ALOOKUP mods owner = SOME tops ==> ~constant_decl id tops) /\
  ?tops root_ty. ALOOKUP cenv.ce_modules owner = SOME tops /\
    FLOOKUP env.bare_globals (owner,id) = SOME root_ty /\
    cenv.ce_module_var_type (owner,id) = SOME root_ty
Proof
  strip_tac >> drule_then assume_tac contract_inv_cenv_modules >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  `?bytes. immutable_region_mods mods owner id off bytes` by metis_tac[] >>
  reverse conj_tac
  >- (drule_all_then strip_assume_tac immutable_region_mods_type >> simp[]) >>
  qpat_x_assum `immutable_region_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
  `MEM (VariableDecl vis Immutable id ty slot) tops` by simp[] >>
  drule_then assume_tac contract_inv_unqualified_variable_keys >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by metis_tac[] >>
  `supported_variable_decl tops (NONE,id) = SOME (vis,Immutable,ty,slot)` by
    metis_tac[supported_variable_decl_distinct_mem] >>
  simp[] >> strip_tac >>
  `constant_decl id tops` by fs[] >>
  `MEM id (MAP FST (module_consts_env tops []))` by metis_tac[constant_decl_mem_consts] >>
  drule distinct_module_consts_env_names_constant >>
  disch_then (qspec_then `id` mp_tac) >> simp[]
QED

Theorem aug_selected_immutable_nested[local]:
  contract_inv mods exps ctx cenv cx /\
  target_root bt = TopLevelNameTarget (owner,id) /\
  ~aug_assign_overlap cenv bt e /\ ~is_word_type root_ty /\
  cenv.ce_module_var_type (owner,id) = SOME root_ty /\
  (!tops. ALOOKUP mods owner = SOME tops ==> ~constant_decl id tops) /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) = (INL rhs,ee) /\
  ALOOKUP mid.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) ==>
  ?cur_imms. ALOOKUP ee.immutables cx.txn.target = SOME cur_imms /\
             FLOOKUP (get_source_immutables owner cur_imms) id = SOME (itv,old)
Proof
  strip_tac >> drule_then assume_tac contract_inv_cenv_modules >>
  `~MEM (WriteAcc (StateRef (owner,id))) (expr_accesses mods e)` by
    (qpat_assum `cenv.ce_modules = mods` (SUBST1_TAC o SYM) >>
     irule aug_selected_no_write >> reverse conj_tac
     >- (qexists_tac `bt` >> simp[] >> irule target_root_state_nonconstant_read >> simp[]) >>
     simp[var_is_prim_word_def,target_place_type_def] >>
     Cases_on `cenv.ce_hashmap_info (owner,id)` >> simp[] >>
     rename1 `_ = SOME entry` >> PairCases_on `entry` >> simp[]) >>
  drule_then strip_assume_tac (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >>
  drule_then SUBST_ALL_TAC read_result_state >>
  rename1 `eval_expr cx e (mid with gas_obs := gs) = (INL raw,ee)` >>
  `FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
      NONE => FEMPTY | SOME obs => get_source_immutables owner obs) id = SOME (itv,old)` by
    (mp_tac (BETA_RULE (Q.SPECL [`cx`,`e`,`mid with gas_obs := gs`,
       `INL raw`,`ee`,`mods`,`owner`,`id`] eval_expr_immutable_access_frame)) >>
     simp[] >> impl_tac
     >- (rpt gen_tac >> strip_tac >> drule_all immutable_index_callable_closed_mods >> simp[]) >>
     simp[]) >>
  pop_assum mp_tac >> Cases_on `ALOOKUP ee.immutables cx.txn.target` >> simp[]
QED

Theorem aug_selected_immutable_current[local]:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env mid /\ expr_sim_inv_mods mods cenv cx env ee /\
  target_root bt = TopLevelNameTarget (owner,id) /\ ~aug_assign_overlap cenv bt e /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) = (INL rhs,ee) /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  ALOOKUP mid.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) /\
  mem_path_offset itv path = SOME (k,ptv) /\ evaluate_subscripts itv old path = INL cur ==>
  ?tops cur_imms now selected. ALOOKUP cenv.ce_modules owner = SOME tops /\
    ALOOKUP ee.immutables cx.txn.target = SOME cur_imms /\
    FLOOKUP (get_source_immutables owner cur_imms) id = SOME (itv,now) /\
    evaluate_subscripts itv now path = INL selected
Proof
  strip_tac >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ mid`
    (mp_then (Pat `expr_sim_inv_mods _ _ _ _ _`) (qspecl_then [`owner`,`off`,`id`,`exps`,`ctx`] mp_tac)
      aug_selected_immutable_key) >>
  simp[] >> strip_tac >>
  `evaluate_type (get_tenv cx) root_ty = SOME itv` by
    (irule aug_selected_immutable_tag >> qexistsl_tac [`cenv`,`env`,`mid`,`id`,`imms`,`mods`,`old`,`owner`] >> simp[]) >>
  Cases_on `path`
  >- (qpat_assum `expr_sim_inv_mods _ _ _ _ ee` (assume_tac o MATCH_MP expr_sim_inv_mods_env) >>
      drule_all_then strip_assume_tac env_consistent_bare_global_ready_src >>
      Cases_on `ALOOKUP ee.immutables cx.txn.target`
      >- gvs[get_source_immutables_def] >>
      gvs[] >> rename1 `ALOOKUP ee.immutables cx.txn.target = SOME imms2` >>
      Cases_on `FLOOKUP (get_source_immutables owner imms2) id` >> gvs[] >>
      rename1 `FLOOKUP (get_source_immutables owner imms2) id = SOME ent` >> PairCases_on `ent` >>
      `evaluate_type (get_tenv cx) root_ty = SOME ent0` by
        (irule aug_selected_immutable_tag >> qexistsl_tac [`cenv`,`env`,`ee`,`id`,`imms2`,`mods`,`ent1`,`owner`] >> simp[]) >>
      gvs[evaluate_subscripts_def]) >>
  drule_all_then assume_tac aug_selected_nested_nonword >>
  drule_all_then strip_assume_tac aug_selected_immutable_nested >>
  simp[] >> metis_tac[]
QED

Theorem aug_selected_preceding_horizons[local]:
  eval_target_place cx bt (es with gas_obs := reads) = (INL p,mid) /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := rhsReads) = (INL rhs,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H mid.storage_trace /\ valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `bind _ _ _ = _` (mp_then (Pat `_ _ = _`) mp_tac valid_horizon_frame) >>
     simp[augassign_rhs_trace_frame]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `eval_target_place _ _ _ = _` (mp_then (Pat `_ _ = _`) mp_tac valid_horizon_frame) >>
  simp[cj 8 evaluate_storage_trace_frame]
QED

(* Common word-store inputs, all at the same successful operator endpoint.
   A store continuation receives its own concrete compiler equation below. *)
val selected_write_resources = ``
  stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx ee w /\
  immutable_frame_mods func cenv cx ee w /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gw tnw w /\
  return_buf_frame d cenv s3 w /\ return_buf_sep d cenv ee w /\
  alloca_history func w /\ (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
  s0.vs_alloca_next <= w.vs_alloca_next /\
  (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x w = SOME z) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP w.vs_allocas aid = SOME b) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gw tnw /\ alloca_frame cenv es sa s0 cenv ee w``;

val selected_write_common = ``
  gas_admissible (write_place cx p value) (stmt_res_ok lctx) ee /\
  expr_sim_inv_mods mods cenv cx env ee /\
  target_ptr_ok cenv (PlaceR p) r Gw tnw w /\
  eval_operand result w = SOME (typed_val_to_w256 ptv value) /\ op_taint tnw result = {} /\
  (!x. result = Var x ==> not_fresh_at s3 x) /\ local_ptrs_reserved cenv s3 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at s3 x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at s3 x) /\
  ~w.vs_halted /\ w.vs_current_bb = s3.cs_current_bb /\ w.vs_inst_idx = LENGTH s3.cs_current_insts /\
  fn_has_code s3 sf func /\ is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv value /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ^selected_write_resources)``;

val selected_write_outcome = ``
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (write_place cx p value) (ee,w,Gw,tnw) stmtQ stmtR``;

Theorem augassign_selected_write_mods:
  contract_inv mods exps ctx cenv cx /\
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  (!gs. eval_stmt cx (AugAssign ty bt bop e) (es with gas_obs := prefix ++ gs) =
        write_place cx p value (ee with gas_obs := gs)) /\ ee.gas_obs = [] /\
  eval_target_place cx bt (es with gas_obs := reads) = (INL p,mid) /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := rhsReads) = (INL rhs,ee) /\
  expr_body_pre_mods mods cenv cx env e (mid with gas_obs := rhsReads) /\
  expr_sim_inv_mods mods cenv cx env mid /\ ~aug_assign_overlap cenv bt e /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sT s0 mid
         (PlaceR p) (Type ty) r G0 tn0 Gtarget tnt t /\
       stmt_state_rel H ctx func cenv cx mid u /\
       wb_frame cenv es mid sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
       (!id path. p = MemoryPlace id path ==>
          ?entry old. lookup_scopes id mid.scopes = SOME entry /\
                     evaluate_subscripts entry.type entry.value path = INL old)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post_mods H ctx func cenv cx e mid s1 s2 u ee rhs rhsop q /\
       ghost_kept_at lo cenv mid s1 Gu tu u Gq tq /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee Gq tq q) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sT /\ local_ptrs_reserved cenv s2 /\
  ci_mono sa sT /\ ci_mono sT s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sf /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
  (!x. FST r = Var x ==> not_fresh_at s2 x) /\
  (!x z. not_fresh_at sT x /\ lookup_var x t = SOME z ==> lookup_var x u = SOME z) /\
  return_buf_frame d cenv s2 q /\ return_buf_sep d cenv es s0 /\
  (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) w) /\
  alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ u.vs_alloca_next <= q.vs_alloca_next /\
  eval_operand (FST r) t = SOME addr /\ eval_operand (FST r) q = SOME addr /\
  target_ptr_ok cenv (PlaceR p) r Gq tq q /\
  (op_prov Gtarget (FST r) = NONE ==> op_prov Gq (FST r) = NONE) /\
  state_frame w = state_frame (q with vs_inst_idx := w.vs_inst_idx) /\
  tnw.t_mem = tq.t_mem /\ tnw.t_stor = tq.t_stor /\ tnw.t_trans = tq.t_trans /\ tnw.t_imm = tq.t_imm /\
  (!x. not_fresh_at s2 x ==> lookup_var x w = lookup_var x q /\
    FLOOKUP Gw x = FLOOKUP Gq x /\ op_taint tnw (Var x) = op_taint tq (Var x)) /\
  s3.cs_current_bb = s2.cs_current_bb /\ s3.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 s3 /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts s2 s3) /\
  q.vs_current_bb = s2.cs_current_bb /\ q.vs_inst_idx = LENGTH s2.cs_current_insts /\
  ~w.vs_halted /\ w.vs_current_bb = s3.cs_current_bb /\ w.vs_inst_idx = LENGTH s3.cs_current_insts /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  eval_operand result w = SOME (typed_val_to_w256 ptv value) /\ op_taint tnw result = {} /\
  (!x. result = Var x ==> not_fresh_at s3 x) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME ptv /\ value_has_type ptv value /\
  FST (SND r) = SOME loc /\
  (if loc = LocCode then compile_ptr_store cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST r) result
   else emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
                  [FST r; result]) s3 = ((),sf) /\
  (!tr slot root rtv path delta res ff.
     p = StoragePlace tr slot ptv /\ MEM (StorageRoot tr root rtv) ee.storage_trace /\
     storage_subregion rtv path delta ptv /\ slot = n2w root + n2w delta /\
     write_place cx p value ee = (res,ff) /\ stmt_res_ok lctx res /\
     emit_void (if tr then TSTORE else SSTORE) [FST r;result] s3 = ((),sf) /\
     eval_operand (FST r) w = SOME slot /\ op_taint tnw (FST r) = {} /\
     ^selected_write_common ==> ^selected_write_outcome) /\
  (!id path entry old res ff.
     p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INL old /\
     place_ptr_rel cenv cx w (PlaceR p) addr (SOME LocMemory) (Type ty) /\
     store_lays_out ptv ptv value /\ write_place cx p value ee = (res,ff) /\ stmt_res_ok lctx res /\
     emit_void MSTORE [FST r;result] s3 = ((),sf) /\ eval_operand (FST r) w = SOME addr /\
     ^selected_write_common ==> ^selected_write_outcome) /\
  (!owner id path tops imms itv now off k ff.
     p = ImmutablePlace owner id path /\ cenv.ce_is_ctor /\
     ALOOKUP cenv.ce_modules owner = SOME tops /\ ALOOKUP ee.immutables cx.txn.target = SOME imms /\
     FLOOKUP (get_source_immutables owner imms) id = SOME (itv,now) /\
     FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
     mem_path_offset itv path = SOME (k,ptv) /\ write_place cx p value ee = (INL (),ff) /\
     compile_imm_store_word cenv.ce_imm_alloca (FST r) result s3 = ((),sf) /\
     eval_operand (FST r) w = SOME (n2w (off+k)) /\ op_taint tnw (FST r) = {} /\
     op_prov Gw (FST r) = NONE /\ ^selected_write_common ==> ^selected_write_outcome) ==>
  ^selected_write_outcome
Proof
  strip_tac >>
  drule_all_then assume_tac aug_selected_write_admissible >>
  drule_all_then strip_assume_tac aug_selected_scopes_dom >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ^selected_write_resources /\ target_ptr_ok cenv (PlaceR p) r Gw tnw w /\
       eval_operand (FST r) w = SOME addr` by suspend "resources" >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule_all_then strip_assume_tac aug_selected_preceding_horizons >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ target_ptr_ok _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `^selected_write_common` by suspend "common" >>
  Cases_on `write_place cx p value ee` >> rename1 `write_place cx p value ee = (wr,ff)` >>
  `stmt_res_ok lctx wr` by
    (qpat_assum `gas_admissible (write_place _ _ _) _ _`
       (qspec_then `[]` mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
     asm_rewrite_tac[] >> disch_then (qspecl_then [`wr`,`ff`] mp_tac) >> simp[]) >>
  Cases_on `p`
  >- suspend "slot"
  >- suspend "memory" >>
  suspend "immutable"
QED

Resume augassign_selected_write_mods[resources]:
  qx_gen_tac `H` >> strip_tac >>
  drule_all_then strip_assume_tac aug_selected_preceding_horizons >>
  qpat_assum `!K. valid_horizon _ _ K es.storage_trace ==> _` (drule_then assume_tac) >>
  qpat_assum `!K. valid_horizon _ _ K mid.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
   s1.cs_next_var <= s2.cs_next_var /\ s2.cs_next_var <= s3.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  drule_all_then strip_assume_tac (GEN_ALL aug_selected_write_frame) >>
  `s0.vs_alloca_next <= w.vs_alloca_next` by
    (qpat_assum `state_frame w = _` mp_tac >> simp[stateFrameTheory.state_frame_def] >>
     rpt strip_tac >> decide_tac) >>
  fs[wb_frame_def]
QED

Resume augassign_selected_write_mods[common]:
  `sa.cs_next_var <= s3.cs_next_var /\ s2.cs_next_var <= s3.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv s3` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at s3 x` by
    metis_tac[not_fresh_at_mono] >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at s3 x` by
    metis_tac[not_fresh_at_mono] >>
  simp[] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> _ /\ target_ptr_ok _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume augassign_selected_write_mods[slot]:
  rename1 `write_place cx (StoragePlace tr slot tv) value ee = (wr,ff)` >>
  drule_then strip_assume_tac write_target_storage_view_mods >>
  `ptv = tv /\ addr = slot /\ loc = slot_loc tr` by fs[] >> gvs[] >>
  `emit_void (if tr then TSTORE else SSTORE) [FST r;result] s3 = ((),sf)` by
    (Cases_on `tr` >> fs[slot_loc_def]) >>
  drule_then strip_assume_tac eval_target_place_observed_region >>
  rename1 `MEM (StorageRoot tr root root_tv) mid.storage_trace` >>
  rename1 `storage_subregion root_tv path delta ptv` >>
  `?events. ee.storage_trace = mid.storage_trace ++ events` by
    (qpat_assum `bind _ _ _ = _` (mp_then (Pat `_ _ = _`) mp_tac storage_trace_frame_prefix) >>
     simp[augassign_rhs_trace_frame]) >>
  `MEM (StorageRoot tr root root_tv) ee.storage_trace` by simp[MEM_APPEND] >>
  `op_taint tnw (FST r) = {}` by fs[target_ptr_ok_def] >>
  qpat_assum `!root rtv path delta. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (qspecl_then [`root`,`root_tv`,`path`,`delta`] mp_tac) >> simp[]
QED

Resume augassign_selected_write_mods[memory]:
  rename1 `write_place cx (MemoryPlace id path) value ee = (wr,ff)` >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  `place_ptr_rel cenv cx t (PlaceR (MemoryPlace id path)) addr (SOME loc) (Type ty)` by
    (fs[write_target_location_mods_def] >> gvs[]) >>
  `loc = LocMemory` by fs[place_ptr_rel_def] >>
  `?root_ty rtv k. cenv.ce_var_type id = SOME root_ty /\ evaluate_type (get_tenv cx) root_ty = SOME rtv /\
                  mem_path_offset rtv path = SOME (k,ptv)` by (fs[place_ptr_rel_def] >> gvs[]) >>
  qpat_assum `!id' path'. MemoryPlace id path = MemoryPlace id' path' ==> _`
    (qspecl_then [`id`,`path`] (strip_assume_tac o REWRITE_RULE[])) >>
  drule_all_then strip_assume_tac (GEN_ALL aug_selected_memory_source) >>
  `place_ptr_rel cenv cx w (PlaceR (MemoryPlace id path)) addr (SOME LocMemory) (Type ty)` by
    suspend "mem_ptr" >>
  `store_lays_out ptv ptv value` by metis_tac[store_lays_out_typed] >>
  `emit_void MSTORE [FST r;result] s3 = ((),sf)` by fs[] >>
  qpat_assum `!id' path' entry old res ff'. _ /\ lookup_scopes _ ee.scopes = _ /\ _ ==> _`
    (qspecl_then [`id`,`path`,`ent`,`now`,`wr`,`ff`] mp_tac) >> simp[]
QED

Resume augassign_selected_write_mods[mem_ptr]:
  qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `!x z. not_fresh_at sT x /\ lookup_var x t = SOME z ==> lookup_var x w = SOME z` by
    (fs[expr_post_mods_def, expr_post_def, ci_mono_def] >>
     rpt gen_tac >> strip_tac >>
     `not_fresh_at s1 x /\ not_fresh_at s2 x` by metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
     metis_tac[]) >>
  irule aug_place_memory_ptr_frame >> qexistsl_tac [`t`,`sT`] >> simp[] >> gvs[]
QED

Resume augassign_selected_write_mods[immutable]:
  rename1 `write_place cx (ImmutablePlace owner id path) value ee = (wr,ff)` >>
  drule_then strip_assume_tac write_target_immutable_view_mods >>
  `ptv' = ptv /\ loc = LocCode /\ addr = n2w (off+k)` by fs[] >> gvs[] >>
  drule_all_then strip_assume_tac aug_selected_immutable_current >>
  drule_all_then strip_assume_tac immutable_augassign_path_write_source >>
  `op_taint tnw (FST r) = {}` by fs[target_ptr_ok_def] >>
  `op_prov Gw (FST r) = NONE` by
    (drule_all (GEN_ALL aug_readonly_saved_operand_mods) >> simp[] >>
     qpat_assum `state_frame w = _` mp_tac >> simp[stateFrameTheory.state_frame_def]) >>
  `compile_imm_store_word cenv.ce_imm_alloca (FST r) result s3 = ((),sf)` by
    fs[compile_ptr_store_def] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Finalise augassign_selected_write_mods
