(* Borrowed ABI operands retain their actual child-read endpoint. *)
Theory bodyAbiEncodeHeadBorrowMods
Ancestors
  bodyAbiEncodePackedPostMods bodyFullPredsMods bodyFullPostsMods
  bodyQualifiedSnapshotReadMods bodySavedRhsSlotLiveMods
  bodyCopyReadPhysicalTypeMods createCtorSnapshotByteRetagMods
  bodyFullExtCallPosTransport exprPtrUnwrapStorageShape
  exprBodyPreProps exprBodyPreTypingProps exprBodyPreCallSafetyProps
  bodyBranchCellFrameMods bodyNormalHeadTailMods bodyWriteSubscriptSourceMods
  bodySimStmtFacts stmtSimDefs exprSimUnwrap
  gasOutcomeFullPostMods gasOutcomeFullPostPathMods gasShadowCompileConvert
  gasShadowCompileHelpers exprSimFullBundleProps fragGasOriginPtr
  exprLowering exprLoweringProps compileEnv bodyMemoryDefs targetPureSourceFrame
  loweringPosts bodyPtrDefs exprSimMemDefs vyperState vyperTypeSystem
  bodyForcedStorageFrameMods vyperStorageFootprint vyperStorageTrace
  vyperEvalExprPreservesScopesDom vyperTypeExprSoundness vyperTypeInvariants
  vyperInterpreter vyperTypeExprResult exprSimMemorySource bodyFullIfExpReach
  exprOperandVar aggregateEvaluatedLayout gasPathPtrExec fragExec valueTypingMemoryProps
  gasContext context
Libs monadsyntax

Theorem borrow_row_read[local]:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  ~is_word_type (lowered_value_type cenv e) /\
  ~is_word_type (post_value_type cenv e) /\
  (post_value_type cenv e = lowered_value_type cenv e \/
    is_bytestring_type (post_value_type cenv e) /\
    is_bytestring_type (lowered_value_type cenv e)) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pt /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
  value_has_type pt v /\ value_has_type rt v /\ val_wf rt v /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds_mods cenv cx (post_value_type cenv e) raw vv ee t /\
  vv_at cenv cx (post_value_type cenv e) sa sm ee raw vv t /\
  ptr_vv_ok cx (post_value_type cenv e) raw vv ee G tn t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee raw vv t ==>
  ?r. read_result cx r ee = (INL v,ee) /\
    vv_holds_mods cenv cx (lowered_value_type cenv e) r
      (ext_call_arg_value (lowered_value_type cenv e) vv) ee t /\
    vv_at cenv cx (lowered_value_type cenv e) sa sm ee r
      (ext_call_arg_value (lowered_value_type cenv e) vv) t /\
    ptr_vv_ok cx (lowered_value_type cenv e) r
      (ext_call_arg_value (lowered_value_type cenv e) vv) ee G tn t /\
    vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee r
      (ext_call_arg_value (lowered_value_type cenv e) vv) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `post_value_type cenv e = lowered_value_type cenv e`
  >- (qexists_tac `raw` >> fs[] >> namedCases_on `vv` ["tag op","tag p"]
      >- fs[ext_call_arg_value_def] >>
      simp[ext_call_arg_value_def] >>
      conj_tac
      >- (qpat_x_assum `vv_holds_mods _ _ _ _ (LocatedValue tag p) _ _` mp_tac >>
          Cases_on `p.ptr_location = LocCode` >>
          simp[vv_holds_mods_def,vv_holds_def] >> metis_tac[]) >>
      conj_tac
      >- (qpat_x_assum `vv_at _ _ _ _ _ _ _ (LocatedValue tag p) _` mp_tac >>
          pure_rewrite_tac[vv_at_def] >> simp[]) >>
      conj_tac
      >- (qpat_x_assum `ptr_vv_ok _ _ _ (LocatedValue tag p) _ _ _ _` mp_tac >>
          pure_rewrite_tac[ptr_vv_ok_def] >> simp[]) >>
      qpat_x_assum `vv_store_bound _ _ _ _ _ (LocatedValue tag p) _` mp_tac >>
      simp[vv_store_bound_def]) >>
  `(?tag op. vv = StackValue tag op) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)` suffices_by
    (disch_tac >> qexists_tac `Value v` >>
     conj_tac >- simp[read_result_def,return_def] >>
     `is_bytestring_type (post_value_type cenv e) /\
      is_bytestring_type (lowered_value_type cenv e)` by fs[] >>
     irule ctor_snapshot_bytes_retag_mods >> simp[] >> metis_tac[]) >>
  Cases_on `vv` >> simp[] >>
  Cases_on `p.ptr_location = LocMemory` >> simp[] >>
  drule_all_then assume_tac compile_nonmemory_lowered_value_type >>
  drule_then assume_tac post_value_type_lowered >> gvs[]
QED

Theorem borrow_source_frame[local]:
  expr_body_pre_mods mods cenv cx env e es /\ body_const_cells_agree_mods mods cx env es /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) ==>
  expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  `body_const_cells_agree_mods mods cx env (es with gas_obs := gs)` by simp[] >>
  conj_tac
  >- (`vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
        simp[bind_def] >>
      drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >> simp[]) >>
  reverse conj_tac >- (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `?res. eval_stmt cx (Expr e) (es with gas_obs := gs) = (res,ee)` by
    (simp[Once evaluate_def, bind_def, type_check_def, assert_def, return_def, raise_def] >>
     Cases_on `is_HashMapRef raw` >> simp[]) >>
  `type_stmt env NoneT (Expr e) = SOME env` by
    simp[type_stmt_def, well_typed_expr_not_hashmap_place] >>
  irule body_const_cells_agree_mods_stmt >>
  goal_assum (drule_at (Pat `eval_stmt _ _ _ = _`)) >>
  qexistsl_tac [`env`,`NoneT`] >> simp[]
QED

Theorem abi_encode_head_borrow_mods:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  compile_snapshot_vv cenv F (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
  compile_snapshot_vv cenv F (ext_call_arg_value (lowered_value_type cenv e) vv) shm = (sv,shs) /\
  ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv)) /\
  ~is_word_type (lowered_value_type cenv e) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,ss,sha,shs) /\
  local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst t. frag_reachable ctx func s0 fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      abi_encode_saved_row_mods lo cenv cx sa ss e sv v sa sm ss vv F H ee G tn t /\
      (!x. vv_operand sv = Var x ==> not_fresh_at ss x) /\
      stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv ss t /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
      t.vs_current_bb = ss.cs_current_bb /\ t.vs_inst_idx = LENGTH ss.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\ (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ss = sm /\ shs = shm` by fs[compile_snapshot_vv_def,comp_return_def] >>
  qpat_x_assum `ss = sm` SUBST_ALL_TAC >>
  qpat_x_assum `shs = shm` SUBST_ALL_TAC >>
  `sv = ext_call_arg_value (lowered_value_type cenv e) vv` by
    fs[compile_snapshot_vv_def,comp_return_def] >>
  qpat_x_assum `sv = _` SUBST_ALL_TAC >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!df l d pg src ts ctx sh f sf ce env ty st.
                 _ ==> expr_sim_full_mods _ _ _ _ e _ /\ _` irule >>
     simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  pop_assum (strip_assume_tac) >>
  fs[expr_sim_full_code_def] >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qhdtm_x_assum `expr_vv_sim_full_mods`
    (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule qualified_snapshot_read_lift_mods >>
  qexistsl_tac [`cenv`,`d`,`sa`,`sm`,`vv`] >> BETA_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  suspend "read"
QED

Resume abi_encode_head_borrow_mods[read]:
  qx_genl_tac [`marks`,`raw`,`v`,`mid`,`G`,`tn`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL raw,mid)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  drule_all_then strip_assume_tac borrow_source_frame >>
  `vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by simp[bind_def] >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then assume_tac copy_lowered_fits_mods >>
  `~is_word_type (expr_type e)` by (drule arg_type_fits_word_type >> simp[]) >>
  drule_all_then
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac strip_assume_tac))
    copy_read_physical_type_gas_obs_mods >>
  qpat_assum `compile_expr cenv _ _ sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qexistsl_tac [`t`,`G`,`tn`] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `~t.vs_halted` by
    (drule_then strip_assume_tac gas_origin_ptr_path_projections >>
     drule gas_path_ptr_exec >> simp[exit_result_def]) >>
  conj_tac >- simp[gas_origin_ptr_path_rules] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `vyperState$bind _ _ _ = _` (mp_then Any mp_tac valid_horizon_frame) >>
     simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_all_then assume_tac saved_rhs_slot_live_mods >>
  qpat_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `wb_frame cenv es mid sa s0 t` by (simp[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d cenv sm t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr cenv _ e sa = _`
       (mp_then Any mp_tac (cj 1 compiler_compile_var)) >> simp[]) >>
  `!x. vv_operand (ext_call_arg_value (lowered_value_type cenv e) vv) = Var x ==>
         not_fresh_at sm x` by
    (Cases_on `vv` >> fs[ext_call_arg_value_def,vv_operand_def]) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_no_phi_mods) >>
     rpt strip_tac >> drule_all_then ACCEPT_TAC gas_origin_ptr_path_dalloca_fmp_headroom) >>
  qexists_tac `v` >> simp[] >> suspend "row"
QED

Resume abi_encode_head_borrow_mods[row]:
  `val_wf rt v` by (drule_then ACCEPT_TAC value_has_type_memory_wf) >>
  drule_all_then strip_assume_tac borrow_row_read >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  simp[abi_encode_saved_row_mods_def] >>
  `!tag p. vv = LocatedValue tag p /\ p.ptr_location <> LocMemory ==>
     lowered_value_type cenv e = expr_type e /\
     post_value_type cenv e = expr_type e /\ tag = expr_type e` by
    (rpt gen_tac >> disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac) >>
     `tag = post_value_type cenv e` by
       (qpat_x_assum `vv_holds_mods _ _ _ _ (LocatedValue _ _) _ _` mp_tac >>
        Cases_on `p.ptr_location = LocCode` >> simp[vv_holds_mods_def,vv_holds_def]) >>
     `lowered_value_type cenv e = expr_type e` by
       (drule_all_then ACCEPT_TAC compile_nonmemory_lowered_value_type) >>
     `post_value_type cenv e = expr_type e` by (drule_then ACCEPT_TAC post_value_type_lowered) >>
     simp[]) >>
  conj_tac
  >- (namedCases_on `vv` ["tag op0","tag p"]
      >- simp[NoAsms,ext_call_arg_value_def] >>
      Cases_on `p.ptr_location = LocMemory`
      >- (qpat_assum `p.ptr_location = LocMemory` (fn th => simp[NoAsms,ext_call_arg_value_def,th])) >>
      qpat_assum `!tag p. LocatedValue _ _ = _ /\ _ ==> _`
        (qspecl_then [`tag`,`p`] mp_tac) >>
      qpat_assum `p.ptr_location <> LocMemory`
        (fn th => simp[NoAsms,ext_call_arg_value_def,th]) >>
      strip_tac >> qpat_assum `tag = _` SUBST1_TAC >>
      qpat_assum `lowered_value_type _ _ = _` (fn th => simp[NoAsms,th])) >>
  conj_tac >- (qexists_tac `r` >> simp[]) >>
  namedCases_on `vv` ["tag op0","tag p"]
  >- (simp[NoAsms,ext_call_arg_value_def,vv_location_def] >> rpt strip_tac >>
      first_assum irule >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  qpat_assum `!tag p. LocatedValue _ _ = _ /\ _ ==> _`
    (qspecl_then [`tag`,`p`] mp_tac) >>
  simp[NoAsms,ext_call_arg_value_def,vv_location_def,vv_operand_def] >>
  Cases_on `p.ptr_location = LocMemory`
  >- (qpat_assum `p.ptr_location = LocMemory` (fn th => simp[NoAsms,th]) >>
      qpat_assum `!tag' p'. _ ==> ptr_buf_ok _ _ p'.ptr_operand _ _`
        (qspecl_then [`tag`,`p`] mp_tac) >>
      qpat_assum `p.ptr_location = LocMemory` (fn th => simp[NoAsms,th])) >>
  qpat_assum `p.ptr_location <> LocMemory` (fn th => simp[NoAsms,th]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `tag = expr_type e` SUBST_ALL_TAC >>
  conj_tac
  >- (qpat_assum `vv_storage_live _ _ (LocatedValue _ _) _ _`
        (ACCEPT_TAC o REWRITE_RULE [vv_storage_live_def])) >>
  strip_tac >>
  qpat_x_assum `cenv.ce_is_ctor /\ _ ==> ?value. _` mp_tac >>
  qpat_assum `post_value_type cenv e = expr_type e` (fn th =>
    qpat_assum `lowered_value_type cenv e = expr_type e` (fn th' =>
      simp[NoAsms,vv_location_def,vv_operand_def,th,GSYM th'])) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `val` (CONJUNCTS_THEN2 MP_TAC assume_tac)) >>
  qpat_assum `read_result cx raw mid = (INL v,mid)` (fn th => simp[NoAsms,th]) >>
  disch_then SUBST_ALL_TAC >>
  gen_tac >> strip_tac >>
  first_assum irule >> conj_tac >> first_assum ACCEPT_TAC
QED

Finalise abi_encode_head_borrow_mods
