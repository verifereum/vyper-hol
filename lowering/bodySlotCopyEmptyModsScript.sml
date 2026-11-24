(* A default aggregate with a length word writes just that word. *)
Theory bodySlotCopyEmptyMods
Ancestors
  bodyFullAssignLocalEmpty bodySlotCopyStateMods bodyFullPostsMods
  gasOutcomeFullPostMods bodyFullShadowBodyInv augAssignFullStoreGhost
  stmtSimAugAssignPlaceStorage tuplePlaceStep placeStore vyperPlaceFrames
  vyperPlaceWriteSoundness vyperTypeDefaults accountsRelProps sourceUnitExecution
  exprLoweringProps emitHelperProps bodyFullShared stateRelProj loweringSlice
  vyperTypeExprSoundness vyperTypeValues bodyPtrDefs venomState ptrDiscipline
  pred_set bodyInvSplit loweringStateRelDefs stmtLowering fragExec augAssignFullStore
  loweringPosts stmtSimDefs stmtSimProps bodySimFull exprSimDefs haltExitProj
  vyperStorageBackend vyperStorageFootprint venomInst emitHelper
  exprOpenPrimitives loweringShapeRules bodyMemoryDefs

Theorem slot_copy_empty_source_ok[local]:
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~cx.txn.is_static ==>
  ?ef. write_place cx (StoragePlace tr slot tv) (default_value tv) es = (INL (),ef)
Proof
  strip_tac >>
  `value_has_type tv (default_value tv)` by
    (drule default_value_has_type_thm >> simp[]) >>
  Cases_on `encode_value tv (default_value tv)`
  >- (`write_place cx (StoragePlace tr slot tv) (default_value tv) es =
       (INR (Error (TypeError "write_storage_slot encode")),es)` by
        simp[write_storage_place_eq] >>
      drule_all write_storage_place_no_type_error >>
      simp[no_type_error_result_def]) >>
  simp[write_storage_place_eq]
QED

Theorem slot_copy_empty_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  dead_lo_ok_mods (H : (bool # bytes32 # type_value) list # num list) D lo cenv cx /\
  ef.scopes = es.scopes /\ s.vs_call_ctx.cc_address = cx.txn.target ==>
  ghost_inv_at_mods D lo d cenv cx ef G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
    ((if tr then tstore slot 0w s else sstore slot 0w s) with vs_inst_idx := pc)
Proof
  strip_tac >> `stor_taint_ok_at D tn s` by fs[ghost_inv_at_mods_def] >>
  `stor_taint_ok_at D
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
    ((if tr then tstore slot 0w s else sstore slot 0w s) with vs_inst_idx := pc)` by
    (qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` kall_tac >>
     Cases_on `tr` >>
     gvs[dead_lo_ok_mods_def, stor_taint_ok_at_def, cx_dead_def,
         sstore_def, tstore_def, vfmStateTheory.lookup_account_def,
         combinTheory.APPLY_UPDATE_THM, key_update_def, SUBSET_DEF, pairTheory.FORALL_PROD] >>
     metis_tac[storage_dead_update_zero]) >>
  Cases_on `d` >> TRY (PairCases_on `x`) >> Cases_on `tr` >>
  gvs[ghost_inv_at_mods_def, return_buf_ptr_def, ptr_covers_def, op_taint_def,
      allocas_from_def, sstore_def, tstore_def, lookup_var_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem slot_copy_empty_immutable[local]:
  immutable_frame_mods func cenv cx es s /\ ef.scopes = es.scopes /\
  ef.immutables = es.immutables ==>
  immutable_frame_mods func cenv cx ef
    ((if tr then tstore slot 0w s else sstore slot 0w s) with vs_inst_idx := pc)
Proof
  strip_tac >> Cases_on `tr` >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def, immutables_rel_def, immutable_alloca_sep_def,
     local_region_def, lookup_var_def, sstore_def, tstore_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem slot_copy_empty_path[local]:
  compile_store_at_loc imm dst (Lit 0w) (SOME (if tr then LocTransient else LocStorage)) sa = ((),sb) /\
  eval_operand dst s = SOME w /\ op_taint tn dst = {} /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_call_ctx.cc_static ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK ((if tr then tstore w 0w s else sstore w 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts), G,
     if tr then tn with t_trans := key_update tn.t_trans w {}
     else tn with t_stor := key_update tn.t_stor w {}) /\
  alloca_history func
    ((if tr then tstore w 0w s else sstore w 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  qpat_assum `compile_store_at_loc _ _ _ _ _ = _`
    (mp_then Any mp_tac body_assign_empty_scalar_suffix) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `op_taint _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (mp_tac o Q.INST [`G` |-> `G`, `ctx` |-> `ctx`,
    `explicit` |-> `explicit`, `PG` |-> `PG`] o SPEC_ALL) >>
  Cases_on `tr` >> simp[] >> rpt strip_tac >> simp[]
QED

Theorem slot_copy_empty_header_mods:
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  has_length_word ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  compile_store_at_loc imm dst (Lit 0w) (SOME (if tr then LocTransient else LocStorage)) sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  eval_operand dst s = SOME slot /\ op_taint tn dst = {} /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    storage_place_observed H (StoragePlace tr slot tv) /\
    stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s /\
    return_buf_frame d cenv sa s /\ return_buf_sep d cenv es s /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
    alloca_frame c0 es0 sa0 s0 cenv es s) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (StoragePlace tr slot tv) (default_value tv)) (es,s,G,tn)
    (\H r ee G' tn' t.
      r = INL () /\ stmt_lands lctx sb r t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext cenv cenv ee.scopes /\
      t.vs_data_section = s.vs_data_section /\ t.vs_immutables = s.vs_immutables /\
      t.vs_memory = s.vs_memory /\
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ return_buf_sep d cenv ee t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' t /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G' tn' /\
      alloca_frame c0 es0 sa0 s0 cenv ee t)
    (\H r ee gt result.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) r gt result) /\
      halt_exit H cx ee r result /\
      (ctx_has_dalloca ctx ==>
       !t. (result = Halt t \/ ?ir. result = IntRet ir t) ==> allocas_below_fmp t))
Proof
  strip_tac >>
  `emit_void (if tr then TSTORE else SSTORE) [dst;Lit 0w] sa = ((),sb)` by
    (Cases_on `tr` >> fs[compile_store_at_loc_def]) >>
  Cases_on `cx.txn.is_static`
  >- suspend "static" >>
  `?ef. write_place cx (StoragePlace tr slot tv) (default_value tv) es = (INL (),ef)` by
    (irule slot_copy_empty_source_ok >> simp[] >> qexists_tac `ty` >> simp[]) >>
  drule_then assume_tac write_place_storage_trace >>
  drule_then assume_tac write_storage_place_scopes >>
  drule_then assume_tac write_storage_place_immutables >>
  qabbrev_tac `u = (if tr then tstore slot 0w s else sstore slot 0w s)
                    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `un = if tr then tn with t_trans := key_update tn.t_trans slot {}
                         else tn with t_stor := key_update tn.t_stor slot {}` >>
  irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`ef`,`INL ()`,`u`,`un`] >> simp[NoAsms] >>
  conj_tac >- (irule aug_place_storage_write_gas_obs >> simp[]) >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `ef.storage_trace = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. _ ==> storage_place_observed _ _ /\ _` (drule_then strip_assume_tac) >>
  suspend "normal"
QED

Resume slot_copy_empty_header_mods[static]:
  irule gas_outcome_full_mods_exit >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`es`,`Abort ExHalt_abort (halt_state (set_returndata [] s))`,
    `INR (Error (RuntimeError "write in static context"))`,`tn`] >>
  simp[exit_result_def, write_storage_place_eq] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. _ ==> storage_place_observed _ _ /\ _` (drule_then strip_assume_tac) >>
  `s.vs_call_ctx.cc_static` by
    (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[call_ctx_rel_def]) >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  conj_tac
  >- (irule storage_emit_static_origin_ptr >> simp[] >>
      goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> simp[] >>
      qexists_tac `0w` >> simp[eval_operand_def,op_taint_def]) >>
  simp[stmt_exit_ptr_def, expr_exit_def, halt_exit_not_halt]
QED

Resume slot_copy_empty_header_mods[normal]:
  `s.vs_call_ctx.cc_static = cx.txn.is_static /\ s.vs_call_ctx.cc_address = cx.txn.target` by
    (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[call_ctx_rel_def]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G,un) /\
   alloca_history func u` by
    (simp[Abbr `u`,Abbr `un`] >>
     irule slot_copy_empty_path >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_at_loc _ _ _ _ _ = _`)) >> simp[]) >>
  simp[] >> suspend "post"
QED

Resume slot_copy_empty_header_mods[post]:
  `stmt_state_rel H ctx func cenv cx ef u` by
    (simp[Abbr `u`,stmt_state_rel_inst_idx] >> irule place_store_empty_backend_state >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
     qexists_tac `ty` >> simp[]) >>
  `well_formed_type_value tv` by drule_then ACCEPT_TAC evaluate_type_well_formed_type_value >>
  `value_has_type tv (default_value tv)` by (drule default_value_has_type_thm >> simp[]) >>
  `storage_well_formed_on cx ef (FST H)` by
    (irule slot_copy_write_wf_mods >> conj_tac >- fs[valid_horizon_def] >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx (ef with gas_obs := []) G un u` by
    (simp[Abbr `u`,Abbr `un`] >> irule slot_copy_empty_ghost >> simp[] >>
     conj_tac >- (qexists_tac `H` >> simp[]) >> qexists_tac `es` >> simp[]) >>
  `immutable_frame_mods func cenv cx (ef with gas_obs := []) u` by
    (simp[Abbr `u`] >> irule slot_copy_empty_immutable >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  suspend "frames"
QED

Resume slot_copy_empty_header_mods[frames]:
  `~block_is_terminated sb` by
    (drule emit_void_terminated >> Cases_on `tr` >> simp[is_terminator_def]) >>
  `sa.cs_next_var = sb.cs_next_var /\ sa.cs_current_bb = sb.cs_current_bb` by gvs[emit_void_eq] >>
  `return_buf_frame d cenv sb u` by
    (irule return_buf_frame_frame >> goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
     Cases_on `tr` >> simp[Abbr `u`,lookup_var_def,sstore_def,tstore_def]) >>
  `ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G un` by simp[Abbr `un`,ghost_kept_at_storage_word_store] >>
  `return_buf_sep d cenv (ef with gas_obs := []) u` by
    (qpat_x_assum `return_buf_sep _ _ _ _` mp_tac >>
     Cases_on `d` >> TRY (PairCases_on `x`) >> Cases_on `tr` >>
     simp[Abbr `u`,return_buf_sep_def,local_region_def,lookup_var_def,
          allocas_from_def,sstore_def,tstore_def]) >>
  `alloca_frame c0 es0 sa0 s0 cenv ef u` by
    (qpat_x_assum `alloca_frame _ _ _ _ _ _ _` mp_tac >> Cases_on `tr` >>
     simp[Abbr `u`,alloca_frame_def,local_region_def,lookup_var_def,sstore_def,tstore_def]) >>
  `storage_well_formed_on cx (ef with gas_obs := []) (FST H)` by
    (qpat_x_assum `storage_well_formed_on _ ef _` mp_tac >>
     simp[storage_well_formed_on_def,boolTheory.FORALL_BOOL,get_storage_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (strip_tac >> qpat_assum `ctx_has_dalloca _ ==> allocas_below_fmp s` (drule_then assume_tac) >>
     Cases_on `tr` >> fs[Abbr `u`,allocas_below_fmp_def,sstore_def,tstore_def] >>
     first_assum ACCEPT_TAC) >>
  `~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_allocas = s.vs_allocas /\
   u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
   u.vs_memory = s.vs_memory /\ (!x. lookup_var x u = lookup_var x s)` by
    (Cases_on `tr` >> simp[Abbr `u`,lookup_var_def,sstore_def,tstore_def]) >>
  simp[stmt_lands_def,cenv_top_ext_refl]
QED

Finalise slot_copy_empty_header_mods
