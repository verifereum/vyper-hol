(* Run the actual positional child and its compiler-selected snapshot. *)
Theory bodyAbiEncodePosHeadRunMods
Ancestors
  bodyAbiEncodePosHeadPostMods bodyAbiEncodePackedPostMods bodyAbiEncodeHeadWordMods
  bodyAbiEncodeHeadBorrowMods bodyAbiEncodeHeadCopyMods
  bodyQualifiedSnapshotReadMods bodyCopyReadPhysicalTypeMods bodyInvCodeProps
  bodyExtPosAggregateCopyMods exprPtrUnwrapStorageShape bodyForcedStorageFrameMods
  exprBodyPreProps exprBodyPreTypingProps exprBodyPreCallSafetyProps
  exprReasonOperand exprSimUnwrap exprSimFullBundleProps
  gasShadowCompileBase gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  bodyFullIfExpReach bodyFullPredsMods bodyFullPostsMods
  vyperState vyperInterpreter vyperStorageTrace vyperStorageFootprint fragGasOriginPtr gasPathPtrExec
  aggregateEvaluatedLayout exprSimHypsDefs exprLowering compileEnv
  exprLoweringProps loweringPosts bodyPtrDefs gasShadow gasShadowState
  bodyMemoryDefs exprSimMemDefs fragExec context allocLimits
Libs monadsyntax

Triviality positional_snapshot_word_tag:
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,sm) ==>
  (is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) <=>
   is_word_type (lowered_value_type ce e))
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then assume_tac copy_lowered_fits_mods >>
  drule_then assume_tac arg_type_fits_word_type >>
  `reason_uniform_shape compile_expr ce (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >>
     fs[expr_sim_inv_mods_def]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
  qpat_assum `!sa vv sb. _ ==> reason_result_shape _ _ _` (drule_then assume_tac) >>
  Cases_on `vv` >> gvs[reason_result_shape_def,ext_call_arg_value_def,vv_type_def]
QED

Triviality positional_word_row:
  abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
    [e] [sv] sa ss es s0 G0 tn0 H (INL [v]) ee G tn t /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
  is_word_type (lowered_value_type ce e) /\
  is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  abi_encode_saved_row_mods lo ce cx sa ss e sv v sa sm ss vv copy H ee G tn t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?tag op. sv = StackValue tag op` by
    (Cases_on `unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) sm` >>
     fs[compile_snapshot_vv_def,comp_bind_def,comp_return_def] >> metis_tac[]) >>
  `sm.cs_next_var <= ss.cs_next_var /\ sm.cs_next_id <= ss.cs_next_id` by
    (qspecl_then [`ce`,`copy`,`ext_call_arg_value (lowered_value_type ce e) vv`,`sm`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[ci_mono_def]) >>
  qhdtm_assum `abi_encode_packed_post_mods`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_encode_packed_post_mods_def]) >>
  qhdtm_assum `abi_encode_saved_row_mods`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  simp[abi_encode_saved_row_mods_def] >>
  qexists_tac `raw` >> gvs[vv_at_def,expr_val_at_def]
QED

val head_post = ``abi_encode_pos_head_post_mods mods
  (DF : (bool # 256 word # type_value) list # num list -> dead)
  lo d ctx func ce cx env e sa sm ss vv sv copy es s0 G0 tn0``;
val head_exit = ``\(H : (bool # 256 word # type_value) list # num list)
  (res:value + exception) ee (gt:(string |-> (num # num)) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

Theorem abi_encode_pos_head_run_mods:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods ce cx env e es /\
  (copy /\ ~is_word_type (lowered_value_type ce e) ==>
    type_alloc_ok ce (lowered_value_type ce e)) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
  compile_snapshot_vv (gas_shadow_env T ce) copy
    (ext_call_arg_value (lowered_value_type ce e) vv) shm = (sv,shs) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,ss,sha,shs) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sm,sha,shm) /\
  fn_has_code sm ss func /\ local_ptrs_reserved ce sa /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst t. frag_reachable ctx func s0 fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    mods cx st0 (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    ^head_post ^head_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac contract_inv_cenv_modules >>
  qpat_assum `ce.ce_modules = mods` (once_rewrite_tac o single o SYM) >>
  drule_all_then assume_tac positional_snapshot_word_tag >>
  Cases_on `is_word_type (lowered_value_type ce e)`
  >- suspend "word" >>
  Cases_on `copy`
  >- suspend "copy" >>
  suspend "borrow"
QED

Resume abi_encode_pos_head_run_mods[word]:
  drule_all_then assume_tac
    (INST_TYPE [alpha |-> ``:exception``] abi_encode_head_word_mods) >>
  irule gas_outcome_full_mods_post_path >> first_assum (irule_at Any) >>
  simp[abi_encode_pos_head_post_mods_def] >> rpt gen_tac >>
  strip_tac >> gvs[] >>
  conj_tac >- drule_all_then ACCEPT_TAC positional_word_row >> first_assum ACCEPT_TAC
QED

Resume abi_encode_pos_head_run_mods[borrow]:
  qpat_assum `compile_snapshot_vv (gas_shadow_env T ce) _ _ shm = _`
    (assume_tac o REWRITE_RULE [compile_snapshot_vv_gas_shadow_env]) >>
  `~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv))` by fs[] >>
  drule_all_then assume_tac abi_encode_head_borrow_mods >>
  irule gas_outcome_full_mods_post_path >> first_assum (irule_at Any) >>
  simp[abi_encode_pos_head_post_mods_def] >> rpt gen_tac >>
  strip_tac >> gvs[] >>
  simp[abi_encode_packed_post_mods_def] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`sa`,`sm`,`ss`,`vv`,`F`] >> first_assum ACCEPT_TAC
QED

Resume abi_encode_pos_head_run_mods[copy]:
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx (expr_type e) e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx (expr_type e) e es` by
    (qhdtm_assum `body_expr_full_ok_mods`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!df l d pg src ts ctx sh f sf ce env ty st.
                   _ ==> expr_sim_full_mods _ _ _ _ e _ /\ _` irule >>
     simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  pop_assum strip_assume_tac >>
  fs[expr_sim_full_code_def] >>
  drule_then assume_tac exprSimMemorySourceTheory.forced_expr_admissible_raw >>
  qhdtm_x_assum `expr_vv_sim_full_mods`
    (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule qualified_snapshot_read_lift_mods >>
  qexistsl_tac [`ce`,`d`,`sa`,`sm`,`vv`] >> BETA_TAC >>
  reverse conj_tac >- gvs[] >>
  qx_genl_tac [`marks`,`raw`,`v`,`mid`,`G`,`tn`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL raw,mid)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  `vyperState$bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    simp[bind_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `vyperState$bind _ _ _ = _` (mp_then Any mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
        simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
     first_x_assum drule >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      vv_post_mods H ctx func ce cx e es sa sm s0 mid raw vv t /\
      ghost_inv_at_mods (DF H) lo d ce cx mid G tn t` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `~t.vs_halted` by
    (drule_then strip_assume_tac gas_origin_ptr_path_projections >>
     drule gas_path_ptr_exec >> simp[exit_result_def]) >>
  `~is_word_type (expr_type e)` by
    (drule_then assume_tac expr_body_pre_mods_inv >>
     drule_then assume_tac expr_body_pre_mods_well_typed >>
     drule_all_then assume_tac copy_lowered_fits_mods >>
     drule arg_type_fits_word_type >> simp[]) >>
  `ext_call_arg_value (lowered_value_type ce e) vv =
     vv_with_type (lowered_value_type ce e) vv` by
    (drule_all_then assume_tac ext_pos_copy_snapshot_retag >> first_assum ACCEPT_TAC) >>
  `vv_type (ext_call_arg_value (lowered_value_type ce e) vv) = lowered_value_type ce e` by
    (qpat_assum `ext_call_arg_value _ _ = _` (fn th =>
       Cases_on `vv` >> simp[ext_call_arg_value_def,vv_with_type_def,vv_type_def,th])) >>
  drule_all abi_encode_head_copy_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`u`,`Gu`,`tu`] >> gen_tac >> strip_tac >>
  conj_tac >- ((simp[])) >>
  simp[abi_encode_pos_head_post_mods_def] >> rpt gen_tac >>
  strip_tac >> gvs[] >>
  simp[abi_encode_packed_post_mods_def] >-
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then strip_assume_tac) >>
     conj_tac
     >- (qexistsl_tac [`sa`,`sm`,`ss`,`vv`,`T`] >> first_assum ACCEPT_TAC)
     >> first_assum ACCEPT_TAC)
  >- (qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] (OK u,Gu,tu)`
        (qspec_then `DF (storage_trace_horizon mid.storage_trace)` assume_tac) >>
      qpat_assum `!H'. valid_horizon _ _ H' _ ==> gas_origin_ptr_path _ _ _ _`
        (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
        (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_no_phi_mods) >>
      `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
        (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G,tn)` (fn path =>
         qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _` (fn safe =>
          qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
           ACCEPT_TAC (MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
             (LIST_CONJ [path,no_phi,safe])))))) >>
      qpat_assum `gas_origin_ptr_path _ (t,G,tn) [] (OK u,Gu,tu)` (fn path =>
       qpat_assum `!fn inst s. frag_reachable ctx func t fn inst s ==> _` (fn safe =>
        qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
         ACCEPT_TAC (MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
           (LIST_CONJ [path,no_phi,safe]))))))
QED

Finalise abi_encode_pos_head_run_mods
