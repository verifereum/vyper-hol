(* Writeback from an already selected storage/transient word place. *)
Theory bodyWriteSlotWordMods
Ancestors
  augAssignFullStore augAssignFullStoreGhost bodyBinopFragMemory
  bodyFullPostsMods gasOutcomeFullPostMods bodyFullShared bodyMemoryDefs
  bodyFullShadowBodyInv bodyInvSplit bodyPtrDefs bodySimFull
  exprLoweringProps loweringShapeRules exprOpenPrimitives exprSimWordArgs
  exprSimUnwrap stateRelProj accountsRelProps sourceUnitExecution
  stmtSimAugAssignPlaceStorage tuplePlaceStep tupleTargetStoreProps placeStore
  stmtSimProps stmtSimDefs loweringStateRelDefs loweringPosts
  vyperStorageFootprint vyperStorageBackend vyperState vyperValue vyperTypeValues
  exprSimDefs haltExitProj fragExec ptrDiscipline venomState venomInst
  pred_set finite_map list rich_list words

Theorem slot_word_immutable_frame[local]:
  immutable_frame_mods func cenv cx es s /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables ==>
  immutable_frame_mods func cenv cx ee
    ((if tr then tstore slot w s else sstore slot w s) with vs_inst_idx := pc)
Proof
  strip_tac >> Cases_on `tr` >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def, immutables_rel_def, immutable_alloca_sep_def,
     local_region_def, lookup_var_def, sstore_def, tstore_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem slot_word_linked_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  dead_lo_ok_mods (H : (bool # bytes32 # type_value) list # num list) D lo cenv cx /\
  ee.scopes = es.scopes /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  storage_dead H tr
    (update_storage slot w (if tr then contract_transient s else contract_storage s)) =
  storage_dead H tr (if tr then contract_transient s else contract_storage s) ==>
  ghost_inv_at_mods D lo d cenv cx ee G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
    ((if tr then tstore slot w s else sstore slot w s) with vs_inst_idx := pc)
Proof
  strip_tac >>
  `stor_taint_ok_at D tn s` by fs[ghost_inv_at_mods_def] >>
  (* Only the storage/transient part of dead_lo_ok matters to this update. *)
  `dead_lo_ok H D 0 (cenv with ce_is_ctor := F) cx` by
    fs[dead_lo_ok_mods_def, dead_lo_ok_def] >>
  `!k b. storage_dead H tr
      (update_storage slot w (if tr then contract_transient s else contract_storage s)) k b =
    storage_dead H tr (if tr then contract_transient s else contract_storage s) k b` by simp[] >>
  drule_all clean_storage_store_taint_ok_at >> strip_tac >>
  Cases_on `d` >> TRY (PairCases_on `x`) >> Cases_on `tr` >>
  gvs[ghost_inv_at_mods_def, return_buf_ptr_def, ptr_covers_def,
      op_taint_def, sstore_def, tstore_def, lookup_var_def, allocas_from_def,
      stor_taint_ok_at_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem slot_word_history[local]:
  alloca_history func s /\ fn_has_code sa sb func /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] sa = ((),sb) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  alloca_history func
    ((if tr then tstore slot w s else sstore slot w s)
     with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> gvs[emit_void_eq] >>
  qpat_assum `s.vs_inst_idx = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule (SRULE [] (Q.INST
    [`insts` |-> `[mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [dst;op] []]`]
    (SPEC_ALL alloca_history_no_alloca_slice))) >>
  Cases_on `tr` >> simp[sstore_def, tstore_def] >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def, IS_PREFIX_APPEND] >>
  strip_tac >> goal_assum (drule_at Any) >>
  simp[DROP_APPEND, mk_inst_def] >> qexists_tac `sa` >> simp[] >>
  ((qexists_tac `T` >> simp[] >> NO_TAC) ORELSE (qexists_tac `F` >> simp[]))
QED

Theorem slot_word_source_immutables[local]:
  write_place cx (StoragePlace tr slot tv) v es = (res,es') ==>
  es'.immutables = es.immutables
Proof
  simp[write_place_def] >>
  metis_tac[vyperImmutablesPreservationTheory.write_storage_slot_immutables]
QED

Theorem slot_word_writeback_mods:
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  MEM (StorageRoot tr offset tv0) es.storage_trace /\
  storage_subregion tv0 path delta tv /\ slot = n2w offset + n2w delta /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\
  write_place cx (StoragePlace tr slot tv) v es = (res,es') /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] sa = ((),sb) /\
  fn_has_code sa sb func /\
  eval_operand dst s = SOME slot /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  op_taint tn dst = {} /\ op_taint tn op = {} /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  u = ((if tr then tstore slot (typed_val_to_w256 tv v) s
        else sstore slot (typed_val_to_w256 tv v) s)
        with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  un = (if tr then tn with t_trans := key_update tn.t_trans slot {}
        else tn with t_stor := key_update tn.t_stor slot {}) /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s /\
    return_buf_frame d cenv sa s /\ return_buf_sep d cenv es s /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP s.vs_allocas aid = SOME b) /\
    ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
    alloca_frame c0 es0 sa0 s0 cenv es s) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (StoragePlace tr slot tv) v) (es,s,G,tn)
    (\H r ee G' tn' t.
      r = INL () /\ t = u /\ G' = G /\ tn' = un /\
      stmt_lands lctx sb r t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext cenv cenv ee.scopes /\
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ return_buf_sep d cenv ee t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' t /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G' tn' /\
      alloca_frame c0 es0 sa0 s0 cenv ee t)
    (\H r ee gt result.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) r gt result) /\
      halt_exit H cx ee r result /\
      (ctx_has_dalloca ctx ==>
       !t. (result = Halt t \/ ?ir. result = IntRet ir t) ==> allocas_below_fmp t))
Proof
  strip_tac >> Cases_on `cx.txn.is_static`
  >- suspend "static"
  >> `res = INL () /\ es'.scopes = es.scopes` by
       (drule_all tuple_target_storage_write_safe >>
        disch_then (qspecl_then [`tr`,`slot`,`es`] strip_assume_tac) >> gvs[]) >>
  drule_then assume_tac write_place_storage_trace >>
  drule_then assume_tac slot_word_source_immutables >>
  `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
  `type_slot_size tv = 1` by metis_tac[word_type_slot_size] >>
  irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`, `es'`, `res`, `u`, `un`] >> simp[NoAsms] >>
  conj_tac >- metis_tac[aug_place_storage_write_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  suspend "normal"
QED

Resume slot_word_writeback_mods[static]:
  `res = INR (Error (RuntimeError "write in static context")) /\ es' = es` by
    (qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
     simp[write_place_def, write_storage_slot_def, check_not_static_def,
          check_def, assert_def, ignore_bind_def, bind_def, raise_def]) >>
  irule gas_outcome_full_mods_exit >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`, `es`, `Abort ExHalt_abort (halt_state (set_returndata [] s))`, `res`, `tn`] >>
  simp[IgnAsm `u = _`, IgnAsm `un = _`, exit_result_def] >>
  conj_tac >- metis_tac[aug_place_storage_write_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H es'.storage_trace` by simp[] >>
  qpat_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `s.vs_call_ctx.cc_static` by
    (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[call_ctx_rel_def]) >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  conj_tac
  >- (irule storage_emit_static_origin_ptr >> simp[] >>
      goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> simp[]) >>
  simp[stmt_exit_ptr_def, expr_exit_def, halt_exit_not_halt]
QED

Resume slot_word_writeback_mods[normal]:
  `s.vs_call_ctx.cc_static = cx.txn.is_static /\
   s.vs_call_ctx.cc_address = cx.txn.target` by
    (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[call_ctx_rel_def]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `storage_place_observed H (StoragePlace tr slot tv)` by
    (irule aug_place_storage_rooted_observed >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `u = _` (fn th => rewrite_tac[th]) >>
      qpat_assum `un = _` (fn th => rewrite_tac[th]) >>
      irule storage_word_store_origin_ptr >> simp[] >>
      goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> simp[]) >>
  suspend "post"
QED

Resume slot_word_writeback_mods[post]:
  `stmt_state_rel H ctx func cenv cx es' u` by
    (simp[stmt_state_rel_inst_idx] >>
     irule place_store_word_backend_state >> metis_tac[]) >>
  `storage_well_formed_on cx es' (FST H)` by
    (irule aug_place_storage_store_wf >> metis_tac[]) >>
  `storage_well_formed_on cx (es' with gas_obs := []) (FST H)` by
    fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def] >>
  `ghost_inv_at_mods (DF H) lo d cenv cx (es' with gas_obs := []) G un u` by
    (qpat_assum `u = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `un = _` (fn th => rewrite_tac[th]) >>
     irule slot_word_linked_ghost >> simp[] >>
     conj_tac
     >- (qexists_tac `H` >> simp[] >>
         drule_all aug_place_region_storage_dead_stable >> simp[]) >>
     qexists_tac `es` >> simp[]) >>
  `immutable_frame_mods func cenv cx (es' with gas_obs := []) u` by
    (qpat_assum `u = _` (fn th => rewrite_tac[th]) >>
     irule slot_word_immutable_frame >> simp[] >> metis_tac[]) >>
  suspend "frames"
QED

Resume slot_word_writeback_mods[frames]:
  `~block_is_terminated sb` by
    (drule emit_void_terminated >> Cases_on `tr` >> simp[is_terminator_def]) >>
  `sa.cs_next_var = sb.cs_next_var /\ sa.cs_current_bb = sb.cs_current_bb` by
    gvs[emit_void_eq] >>
  `return_buf_frame d cenv sb u` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
     Cases_on `tr` >> simp[lookup_var_def, sstore_def, tstore_def]) >>
  `alloca_history func u` by
    (qpat_assum `u = _` (fn th => rewrite_tac[th]) >>
     irule slot_word_history >> simp[] >>
     qexistsl_tac [`dst`,`op`,`sa`] >> simp[]) >>
  `ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G un` by
    simp[ghost_kept_at_storage_word_store] >>
  `return_buf_sep d cenv (es' with gas_obs := []) u` by
    (qpat_x_assum `return_buf_sep _ _ _ _` mp_tac >>
     Cases_on `d` >> TRY (PairCases_on `x`) >> Cases_on `tr` >>
     simp[return_buf_sep_def, local_region_def,
          allocas_from_def, lookup_var_def, sstore_def, tstore_def]) >>
  `alloca_frame c0 es0 sa0 s0 cenv (es' with gas_obs := []) u` by
    (qpat_x_assum `alloca_frame _ _ _ _ _ _ _` mp_tac >>
     Cases_on `tr` >>
     simp[alloca_frame_def, local_region_def, lookup_var_def,
          sstore_def, tstore_def]) >>
  Cases_on `tr` >>
  fs[stmt_lands_def, cenv_top_ext_refl, lookup_var_def, sstore_def, tstore_def,
     allocas_below_fmp_def] >> metis_tac[]
QED

Finalise slot_word_writeback_mods
