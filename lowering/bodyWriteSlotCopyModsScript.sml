(* Endpoint facts for an aggregate write at a selected slot. *)
Theory bodyWriteSlotCopyMods
Ancestors
  bodyFullPostsMods exprLoweringProps loweringSlice placeStoreStorage
  bodyFullStoreSlotsPath bodyFullStoreSlotsFrame placeStoreSlots bodyPtrDefs
  stateRelProj bodyFullShadowBodyInv vyperStorageBackend finite_map list
  loweringStateRelDefs bodySimFull bodyMemoryDefs bodyInvSplit
  bodySlotCopyPositiveMods bodySlotCopyLimitsMods bodySlotCopyBytesMods
  bodySlotCopyNormalizeMods bodySlotCopyEmptyMods bodySlotCopySavedMods
  bodySlotCopySnapshotMods gasOutcomeFullZeroPrefixMods gasOutcomeFullPostMods
  stmtSimAugAssignPlaceStorage stmtSimDefs exprSimCopy typedMemoryCopy
  vyperStoragePlaceObserved vyperStoragePlaceRegion words arithmetic
  vyperStorageFootprint fragExec vyperPlaceFrames exprSimDefs haltExitProj
  stmtLoweringMono pair freshWrites stmtSimProps vyperTypeSystem vyperTypeArgFits
  vyperTypeValues vyperTyping valueEncodingTyping bodyFullShared wordArgsPtr
  bodyFullAbiEncodeOriginFloor fragGasOriginPtr compileEnv venomState
  loweringPosts valueEncodingProps ptrDiscipline

Theorem slot_copy_linked_immutable_preserved[local]:
  immutable_frame_mods func cenv cx ee s /\
  ef.immutables = ee.immutables /\ ef.scopes = ee.scopes /\
  t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  immutable_frame_mods func cenv cx ef t
Proof
  strip_tac >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ _` (drule_then mp_tac) >>
      pure_asm_rewrite_tac[immutables_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >> irule immutable_alloca_sep_fields >>
  qexistsl_tac [`s`, `ee`] >> simp[] >>
  rpt strip_tac >> qexists_tac `id` >>
  fs[local_region_def, local_ptrs_reserved_def] >> metis_tac[]
QED

(* Common continuation, independent of the representation that fed the store. *)
val slot_copy_ok =
  ``\(H : (bool # 256 word # type_value) list # num list) r ee G' tn' t.
      r = INL () /\ stmt_lands lctx sb r t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext cenv cenv ee.scopes /\ stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ return_buf_sep d cenv ee t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' t /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G' tn' /\
      alloca_frame cenv es0 sa0 s0 cenv ee t``;

val slot_copy_exit =
  ``\(H : (bool # 256 word # type_value) list # num list) r ee (gt : (string |-> num # num) # taint) result.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) r gt result) /\
      halt_exit H cx ee r result /\
      (ctx_has_dalloca ctx ==>
       !t. (result = Halt t \/ ?ir. result = IntRet ir t) ==> allocas_below_fmp t)``;

val slot_copy_frames =
  ``(!H. valid_horizon cx st0 H es.storage_trace ==>
      storage_place_observed H (StoragePlace tr dw dtv) /\
      stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx es G tn s /\ return_buf_sep d cenv es s) /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
    alloca_frame cenv es0 sa0 s0 cenv es s``;

val slot_copy_reserved =
  ``local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x)``;

val slot_copy_structs =
  ``acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
                              sz = type_memory_size rt) fields)``;

val slot_copy_memory =
  ``eval_operand src s = SOME sw /\ op_taint tn src = {} /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory tv v (w2n sw) mem) /\
    (type_memory_size tv <> 0 ==> ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
    w2n sw + type_memory_size tv < dimword (:256) /\
    (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next)``;

Theorem slot_copy_observed_bound[local]:
  storage_place_observed H (StoragePlace tr dw dtv) /\
  regions_consistent (FST H) /\ 0 < type_slot_size dtv ==>
  w2n dw + type_slot_size dtv <= dimword (:256)
Proof
  rw[storage_place_observed_def] >>
  drule_all_then strip_assume_tac place_store_root_layout >>
  drule_then assume_tac storage_subregion_bounds >>
  `w2n root + delta < dimword (:256)` by decide_tac >>
  `root + n2w delta = n2w (w2n root + delta)` by simp[GSYM word_add_n2w] >>
  simp[w2n_n2w,LESS_MOD] >> decide_tac
QED

Theorem slot_copy_ready_writeback[local]:
  ^slot_copy_structs /\ ^slot_copy_reserved /\ ^slot_copy_memory /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  value_has_type dtv v /\ well_formed_type_value dtv /\
  0 < type_slot_size tv /\ type_slot_size tv <= type_slot_size dtv /\
  encode_value tv v = SOME writes /\ encode_value dtv v = SOME writes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory dtv v (w2n sw) mem) /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ op_taint tn dst = {} /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  sa0.cs_next_var <= sa.cs_next_var /\
  storage_trace_domain cx st0 es.storage_trace /\
  ^slot_copy_frames /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (StoragePlace tr dw dtv) v) (es,s,G,tn) ^slot_copy_ok ^slot_copy_exit
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_inv s /\
    s.vs_call_ctx.cc_static = cx.txn.is_static /\
    w2n dw + type_slot_size tv <= dimword (:256)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     `regions_consistent (FST H0)` by fs[valid_horizon_def] >>
     `0 < type_slot_size dtv` by decide_tac >>
     drule_all_then assume_tac slot_copy_observed_bound >>
     `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
     `alloca_inv s` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     `s.vs_call_ctx.cc_static = cx.txn.is_static` by
       (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
        simp[call_ctx_rel_def]) >>
     simp[] >> decide_tac) >>
  Cases_on `cx.txn.is_static` >- suspend "static" >> suspend "normal"
QED

Resume slot_copy_ready_writeback[static]:
  `type_slot_size tv <> 0` by decide_tac >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`] (SPEC_ALL slot_copy_static_or_zero_mods)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >> simp[] >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  irule gas_outcome_full_mods_exit >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`es`,`Abort ExHalt_abort (halt_state (set_returndata [] t))`,
    `INR (Error (RuntimeError "write in static context"))`,`tf`] >>
  simp[exit_result_def,write_storage_place_eq,stmt_exit_ptr_def,expr_exit_def,halt_exit_not_halt]
QED

Resume slot_copy_ready_writeback[normal]:
  `sa.cs_next_var <= sb.cs_next_var` by
    (`ci_mono sa sb` by metis_tac[cj 1 ci_mono_compile_store_slots,SND] >> fs[ci_mono_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    storage_place_observed H (StoragePlace tr dw dtv) /\ storage_well_formed_on cx es (FST H) /\
    stmt_state_rel H ctx func cenv cx es s /\ dead_lo_ok_mods H (DF H) lo cenv cx /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s /\ return_buf_sep d cenv es s` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  mp_tac (Q.INST [`ee` |-> `es`] (SPEC_ALL slot_copy_positive_path_mods)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss] >>
    qexists_tac `storage_trace_horizon es.storage_trace` >> fs[storage_trace_domain_def])) >>
  disch_then (qx_choosel_then [`ef`,`t`,`Gf`,`tf`] (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`ef`,`INL ()`,`t`,`tf`] >> simp[NoAsms] >>
  conj_tac >- (irule aug_place_storage_write_gas_obs >> simp[]) >>
  qx_gen_tac `H` >> disch_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `ef.storage_trace = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  suspend "frame"
QED

Resume slot_copy_ready_writeback[frame]:
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by simp[SF CONJ_ss] >>
  `immutable_frame_mods func cenv cx (ef with gas_obs := []) t` by
    (irule slot_copy_linked_immutable_preserved >>
     qexistsl_tac [`es`,`s`,`sa`] >> simp[]) >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sa x` by metis_tac[not_fresh_at_mono] >>
  `ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gf tf` by
    (qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     pure_rewrite_tac[ghost_kept_at_def] >> conj_tac
     >- (qx_gen_tac `x` >> disch_tac >>
         `not_fresh_at sa x` by simp[] >>
         qpat_assum `!x. not_fresh_at sa x ==> _ /\ _` (drule_then strip_assume_tac) >>
         qpat_assum `!x. not_fresh_at sa0 x ==> _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
     qpat_assum `tf.t_mem = _` (pure_rewrite_tac o single) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!n b sz. local_region cenv ef.scopes t n b sz <=> local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> asm_rewrite_tac[] >> irule copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  `alloca_frame cenv es0 sa0 s0 cenv ef t` by
    (simp[alloca_frame_def] >>
     qpat_assum `alloca_frame _ _ _ _ _ _ s`
       (mp_tac o REWRITE_RULE [alloca_frame_def]) >>
     pure_asm_rewrite_tac[] >> disch_then ACCEPT_TAC) >>
  `return_buf_sep d cenv (ef with gas_obs := []) t` by
    (Cases_on `d` >- simp[return_buf_sep_def] >>
     rename1 `return_buf_sep (SOME rb) _ _ _` >> PairCases_on `rb` >>
     qpat_assum `return_buf_sep _ cenv ef t` mp_tac >>
     simp[NoAsms,return_buf_sep_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx (ef with gas_obs := []) (FST H)` by
    (qpat_assum `storage_well_formed_on _ ef _` mp_tac >>
     simp[NoAsms,storage_well_formed_on_def,boolTheory.FORALL_BOOL,get_storage_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  simp[cenv_top_ext_refl,SF CONJ_ss] >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ ef _ _ _` mp_tac >>
  simp[NoAsms,ghost_inv_at_mods_def] >> strip_tac >> first_assum ACCEPT_TAC
QED

Finalise slot_copy_ready_writeback[local]

val slot_copy_run =
  ``fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    sa0.cs_next_var <= sa.cs_next_var /\
    storage_trace_domain cx st0 es.storage_trace /\
    ^slot_copy_frames /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx)``;

val slot_copy_cut =
  ``eval_operand dst s = SOME dw /\ op_taint tn dst = {} /\ ^slot_copy_run``;

Theorem slot_copy_equal_writeback[local]:
  ^slot_copy_cut /\ ^slot_copy_structs /\ ^slot_copy_reserved /\ ^slot_copy_memory /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ tv = dtv /\
  value_has_type tv v /\ 0 < type_slot_size dtv /\
  compile_store_slots cenv src dst dty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (StoragePlace tr dw dtv) v) (es,s,G,tn) ^slot_copy_ok ^slot_copy_exit
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `tv = dtv` SUBST_ALL_TAC >>
  `well_formed_type_value dtv` by drule_then ACCEPT_TAC evaluate_type_well_formed_type_value >>
  `?writes. encode_value dtv v = SOME writes` by
    metis_tac[cj 1 value_has_type_equiv,optionTheory.IS_SOME_EXISTS] >>
  mp_tac (Q.INST [`ty` |-> `dty`, `tv` |-> `dtv`] (SPEC_ALL slot_copy_ready_writeback)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss])) >> disch_then ACCEPT_TAC
QED

Theorem slot_copy_widened_bytes_writeback[local]:
  ^slot_copy_cut /\ ^slot_copy_structs /\ ^slot_copy_reserved /\ ^slot_copy_memory /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  is_bytestring_type dty /\ is_bytestring_type ty /\ type_widens_to (get_tenv cx) ty dty /\
  value_has_type tv v /\ value_has_type dtv v /\ 0 < type_slot_size dtv /\
  compile_store_slots cenv src dst dty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (StoragePlace tr dw dtv) v) (es,s,G,tn) ^slot_copy_ok ^slot_copy_exit
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `w2n dw + type_slot_size dtv <= dimword (:256)` by
    (qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
     `valid_horizon cx st0 H0 es.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     `regions_consistent (FST H0)` by fs[valid_horizon_def] >>
     drule_all_then ACCEPT_TAC slot_copy_observed_bound) >>
  `well_formed_type_value dtv` by drule_then ACCEPT_TAC evaluate_type_well_formed_type_value >>
  mp_tac (Q.INST [`sty` |-> `ty`, `stv` |-> `tv`, `tenv` |-> `get_tenv cx`,
    `mask` |-> `tn.t_mem`, `memory` |-> `s.vs_memory`, `off` |-> `w2n (sw:256 word)`, `k` |-> `dw`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] slot_copy_bytes_layout_mods))) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >> strip_tac >>
  mp_tac (SPEC_ALL slot_copy_ready_writeback) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss])) >> disch_then ACCEPT_TAC
QED

Theorem slot_copy_header_writeback[local]:
  ^slot_copy_cut /\ has_length_word dty /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  compile_store_at_loc imm dst (Lit 0w) (SOME (if tr then LocTransient else LocStorage)) sa = ((),sb) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (StoragePlace tr dw dtv) (default_value dtv)) (es,s,G,tn)
    ^slot_copy_ok ^slot_copy_exit
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac (Q.INST [`c0` |-> `cenv`, `slot` |-> `dw`, `tv` |-> `dtv`, `ty` |-> `dty`]
    (SPEC_ALL slot_copy_empty_header_mods)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[] >> rpt strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >> simp[])) >>
  disch_then (fn th => irule gas_outcome_full_mods_post_source >> irule_at Any th) >>
  simp[]
QED

(* The typed prefix keeps the return-buffer allocation floor, even when
   that floor differs from the base of ordinary memory. *)
Theorem slot_copy_prefix_return_sep[local]:
  return_buf_sep d cenv es s /\ return_buf_frame d cenv sa s /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu) /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  return_buf_sep d cenv es u
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  irule return_buf_sep_transport >>
  conj_tac
  >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
      fs[return_buf_frame_def,return_buf_sep_def] >>
      drule_all abi_encode_origin_path_allocas_from >> simp[]) >>
  qexistsl_tac [`cenv`,`es`,`s`] >> simp[] >> rpt strip_tac >>
  qpat_assum `local_region _ _ u _ _ _` mp_tac >>
  drule_all_then (fn th => pure_rewrite_tac[th]) copy_buffer_local_region_frame >> simp[]
QED

Theorem slot_copy_prefix_ghost_kept[local]:
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
  ghost_kept_at lo cenv es sa G tn s Gu tu /\
  sa0.cs_next_var <= sa.cs_next_var /\ sa0.cs_next_id <= sa.cs_next_id /\
  alloca_frame cenv es0 sa0 s0 cenv es s /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!n b sz. local_region cenv es0.scopes s0 n b sz ==> local_region cenv es.scopes s n b sz) ==>
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gu tu
Proof
  pure_rewrite_tac[ghost_kept_at_def,alloca_frame_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  conj_tac
  >- (qx_gen_tac `x` >> disch_tac >>
      `not_fresh_at sa x` by metis_tac[not_fresh_at_mono] >>
      qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `!x. not_fresh_at sa0 x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by simp[] >>
      `aid < sa.cs_next_id` by decide_tac >>
      qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (drule_all_then strip_assume_tac) >>
      qpat_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
        (drule_all_then assume_tac) >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (drule_all_then ACCEPT_TAC)) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!n b sz. local_region cenv es0.scopes s0 n b sz ==> _`
    (drule_then assume_tac) >>
  qpat_assum `!n b sz i. local_region cenv es.scopes s n b sz /\ _ ==> _`
    (drule_all_then assume_tac) >>
  qpat_assum `!n b sz i. local_region cenv es0.scopes s0 n b sz /\ _ ==> _`
    (drule_all_then ACCEPT_TAC)
QED

Theorem slot_copy_normalized_writeback[local]:
  ^slot_copy_cut /\ ^slot_copy_structs /\ ^slot_copy_reserved /\ ^slot_copy_memory /\
  sa0.cs_next_id <= sa.cs_next_id /\ local_ptrs_reserved cenv sa0 /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type tv v /\ value_has_type dtv v /\ 0 < type_slot_size dtv /\
  type_widens_to (get_tenv cx) ty dty /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
  0 < type_memory_size tv /\ type_memory_size dtv < dimword (:256) /\
  expr_val_at cenv cx ty start sa es v src s /\
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  compile_store_memory_typed cenv buf.buf_operand dty src ty sm = ((),sc) /\
  compile_store_slots cenv buf.buf_operand dst dty tr sc = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (StoragePlace tr dw dtv) v) (es,s,G,tn) ^slot_copy_ok ^slot_copy_exit
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer,SND] >>
  `ci_mono sm sc` by metis_tac[cj 1 ci_mono_typed_memory_family,SND] >>
  `ci_mono sc sb` by metis_tac[cj 1 ci_mono_compile_store_slots,SND] >>
  `ci_mono sa sc` by metis_tac[ci_mono_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `val_wf tv v /\ val_wf dtv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  `?xs. src = Var xs /\ ptr_covers G tn xs s (type_memory_size tv)` by
    (qpat_assum `_ <> 0 ==> ?x. src = Var x /\ _` mp_tac >> simp[]) >>
  qpat_x_assum `src = Var xs` SUBST_ALL_TAC >>
  `not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
   w2n sw + type_memory_size tv <= s.vs_alloca_next` by fs[eval_operand_def] >>
  mp_tac (Q.INST [`sb` |-> `sc`, `sty` |-> `ty`, `stv` |-> `tv`]
    (SPEC_ALL slot_copy_normalize_ready_mods)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >>
  strip_tac >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` >>
  rename1 `buf.buf_operand = Var root` >>
  rename1 `lookup_var root u = SOME (n2w bcopy)` >>
  suspend "resources"
QED

Resume slot_copy_normalized_writeback[resources]:
  `sa0.cs_next_id <= sa.cs_next_id /\ sa0.cs_next_var <= sc.cs_next_var /\
   sa.cs_next_var <= sc.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sa x` by metis_tac[not_fresh_at_mono] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x /\ lookup_var x u = lookup_var x s` by
    simp[SF CONJ_ss] >>
  `local_ptrs_reserved cenv sc` by metis_tac[local_ptrs_reserved_next_var] >>
  `!n b sz. local_region cenv es0.scopes s0 n b sz ==> local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> disch_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s0`,`sa0`,`es0.scopes`] >> simp[]) >>
  `alloca_frame cenv es0 sa0 s0 cenv es u` by
    (irule alloca_frame_trans >> qexistsl_tac [`cenv`,`es`,`s`,`sa`] >> simp[]) >>
  `ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gu tu` by
    (irule slot_copy_prefix_ghost_kept >> qexistsl_tac [`G`,`es`,`s`,`sa`,`tn`] >> simp[]) >>
  `return_buf_sep d cenv es u` by
    (`gas_origin_ptr_path (ARB,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by simp[] >>
     irule slot_copy_prefix_return_sep >> goal_assum (drule_at (Pat `gas_origin_ptr_path _ _ _ _`)) >>
     simp[SF CONJ_ss] >> qexists_tac `sa` >> simp[SF CONJ_ss]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    storage_place_observed H (StoragePlace tr dw dtv) /\
    stmt_state_rel H ctx func cenv cx es u /\ immutable_frame_mods func cenv cx es u /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es Gu tu u /\ return_buf_sep d cenv es u` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  suspend "compose"
QED

Resume slot_copy_normalized_writeback[compose]:
  `eval_operand dst u = SOME dw /\ op_taint tu dst = {}` by
    (conj_tac >- simp[SF CONJ_ss] >> Cases_on `dst` >>
     fs[op_taint_def,SF CONJ_ss]) >>
  `w2n (n2w bcopy:256 word) = bcopy` by
    (`bcopy < dimword (:256)` by decide_tac >> simp[w2n_n2w,LESS_MOD]) >>
  `eval_operand buf.buf_operand u = SOME (n2w bcopy) /\ op_taint tu buf.buf_operand = {}` by
    ((simp[eval_operand_def] >> qpat_assum `ptr_covers Gu tu root _ _` mp_tac >>
     simp[ptr_covers_def] >> (gvs[eval_operand_def, ptr_covers_def]))) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `!x. root = x \/ dst = Var x ==> not_fresh_at sc x` by (rpt strip_tac >> gvs[SF CONJ_ss]) >>
  irule gas_outcome_full_mods_zero_prefix >> qexistsl_tac [`Gu`,`u`,`tu`] >>
  conj_tac >- simp[] >>
  mp_tac (Q.INST [`G` |-> `Gu`, `tn` |-> `tu`, `s` |-> `u`, `sa` |-> `sc`,
    `tv` |-> `dtv`, `src` |-> `buf.buf_operand`, `sw` |-> `n2w bcopy`]
    (SPEC_ALL slot_copy_equal_writeback)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss] >>
    rpt conj_tac >> rpt strip_tac >> gvs[SF CONJ_ss])) >> disch_then ACCEPT_TAC
QED

Finalise slot_copy_normalized_writeback[local]

(* A zero-sized slot layout and a zero length header are different: the
   former is excluded here by the typed assignable destination, and the
   latter is a scalar store even if the source value is empty. *)
val slot_copy_extra =
  ``dty <> ty /\ ~(is_bytestring_type dty /\ is_bytestring_type ty) ==>
    sa0.cs_next_id <= sa.cs_next_id /\ local_ptrs_reserved cenv sa0 /\
    MAP FDOM es0.scopes = MAP FDOM es.scopes /\
    0 < type_memory_size tv /\ type_memory_size dtv < dimword (:256) /\
    (?start. expr_val_at cenv cx ty start sa es v src s)``;

val slot_copy_code =
  ``compile_assign_value cenv dst (slot_loc tr) src (is_word_type dty)
      src_loc dty ty (type_memory_bytes cenv dty) sa = ((),sb)``;

val slot_copy_outcome =
  ``gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
     (write_place cx (StoragePlace tr dw dtv) v) (es,s,G,tn) ^slot_copy_ok ^slot_copy_exit``;

Theorem slot_copy_compiled_writeback[local]:
  ^slot_copy_cut /\ ^slot_copy_structs /\ ^slot_copy_reserved /\ ^slot_copy_memory /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ assignable_type (get_tenv cx) dty /\
  ~is_word_type dty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ type_widens_to (get_tenv cx) ty dty /\ ~is_word_type ty /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (^slot_copy_extra) /\ ^slot_copy_code ==> ^slot_copy_outcome
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `0 < type_slot_size dtv` by drule_all_then ACCEPT_TAC assignable_type_slot_size_pos >>
  `value_has_type dtv v` by (drule_all_then strip_assume_tac type_widens_to_value_has_type >> gvs[]) >>
  drule_then strip_assume_tac place_store_storage_compile >>
  qpat_x_assum `if is_word_type dty then _ else _`
    (fn th => mp_tac th >> pure_asm_rewrite_tac[COND_CLAUSES] >> disch_tac)
  >- suspend "normalize" >- suspend "equal" >> suspend "bytes"
QED

Resume slot_copy_compiled_writeback[normalize]:
  `~is_bytestring_type ty` by metis_tac[type_widens_from_bytestring] >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!n fs. FLOOKUP cenv.ce_struct_fields n = SOME fs ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qpat_assum `dty <> ty /\ _ ==> _` (drule_all_then strip_assume_tac) >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  `compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm)` by
    (qpat_assum `type_memory_bytes cenv dty = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (SPEC_ALL slot_copy_normalized_writeback) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss])) >> disch_then ACCEPT_TAC
QED

Resume slot_copy_compiled_writeback[equal]:
  `tv = dtv` by metis_tac[optionTheory.SOME_11] >>
  mp_tac (SPEC_ALL slot_copy_equal_writeback) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss])) >> disch_then ACCEPT_TAC
QED

Resume slot_copy_compiled_writeback[bytes]:
  mp_tac (SPEC_ALL slot_copy_widened_bytes_writeback) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss])) >> disch_then ACCEPT_TAC
QED

Finalise slot_copy_compiled_writeback[local]

val slot_copy_types =
  ``assignable_type (get_tenv cx) dty /\ ~is_word_type dty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    type_widens_to (get_tenv cx) ty dty /\ ~is_word_type ty``;

(* Dispatch on the actual emitted suffix, not on a chosen store run. *)
Theorem slot_copy_writeback_mods:
  ^slot_copy_cut /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  ((v = default_value dtv /\ has_length_word dty /\
    compile_store_at_loc imm dst (Lit 0w)
      (SOME (if tr then LocTransient else LocStorage)) sa = ((),sb)) \/
   (^slot_copy_structs /\ ^slot_copy_reserved /\ ^slot_copy_memory /\
    ^slot_copy_types /\ (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    (^slot_copy_extra) /\ ^slot_copy_code)) ==>
  ^slot_copy_outcome
Proof
  disch_then strip_assume_tac
  >- (qpat_x_assum `v = default_value dtv` SUBST_ALL_TAC >>
      mp_tac (SPEC_ALL slot_copy_header_writeback) >>
      (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >> disch_then ACCEPT_TAC) >>
  mp_tac (SPEC_ALL slot_copy_compiled_writeback) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >> disch_then ACCEPT_TAC
QED

(* The staged adapters recover the operands on the very state from which
   the compiled suffix runs. The caller binds the earlier counted cuts. *)
Theorem slot_copy_saved_writeback_mods:
  ^slot_copy_run /\ ^slot_copy_structs /\ ^slot_copy_reserved /\
  dst = FST r /\ ty = lowered_value_type cenv e /\
  assignable_type (get_tenv cx) dty /\ ~is_word_type dty /\ ~is_word_type ty /\
  type_widens_to (get_tenv cx) ty dty /\ ^slot_copy_code /\
  (dty <> ty /\ ~(is_bytestring_type dty /\ is_bytestring_type ty) ==>
   sa0.cs_next_id <= sa.cs_next_id /\ local_ptrs_reserved cenv sa0 /\
   MAP FDOM es0.scopes = MAP FDOM es.scopes /\ type_memory_size dtv < dimword (:256) /\
   !tv. evaluate_type (get_tenv cx) ty = SOME tv ==> 0 < type_memory_size tv) /\
  expr_body_pre_mods mods cenv cx env e before /\ ~is_word_type (expr_type e) /\
  bind (eval_expr cx e) (read_result cx) (before with gas_obs := gs) = (INL v,mid) /\
  write_target_post_mods H D lo d ctx func cenv cx bt mid sm st ss es
    (PlaceR (StoragePlace tr dw dtv)) (Type dty) r Ga tna Gu tu u /\
  unwrap_value cenv vv st = (src,sa) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at st x) /\
  expr_post_mods H ctx func cenv cx e es start sa u es v src s /\
  ptr_val_ok cx (post_value_type cenv e) v src G tn s /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e src G s) /\
  (~is_word_type (post_value_type cenv e) ==>
    !rt w. evaluate_type (get_tenv cx) ty = SOME rt /\ eval_operand src s = SOME w ==>
           type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next) /\
  eval_operand dst s = eval_operand dst u /\ ghost_kept_at lo cenv es st Gu tu u G tn ==>
  ^slot_copy_outcome
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `dst = FST r` SUBST_ALL_TAC >> qpat_x_assum `ty = lowered_value_type cenv e` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`es` |-> `before`, `ee` |-> `es`, `s` |-> `ss`, `z` |-> `s`, `op` |-> `src`,
    `k` |-> `dw`, `sb` |-> `st`, `sa` |-> `start`, `sc` |-> `sa`, `G0` |-> `Ga`, `tn0` |-> `tna`]
    (SPEC_ALL slot_copy_saved_input_mods)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss])) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN
    (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  rename1 `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv` >>
  rename1 `eval_operand src s = SOME sw` >>
  `!x. src = Var x \/ FST r = Var x ==> not_fresh_at sa x` by (rpt strip_tac >> simp[]) >>
  mp_tac (Q.INST [`dst` |-> `FST (r : operand # data_location option # place_ty option)`,
    `ty` |-> `lowered_value_type cenv e`] (SPEC_ALL slot_copy_compiled_writeback)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss,GSYM NOT_ZERO_LT_ZERO] >>
    disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
    `~is_bytestring_type (lowered_value_type cenv e)` by metis_tac[type_widens_from_bytestring] >>
    simp[SF CONJ_ss] >> qexists_tac `start` >> simp[])) >> disch_then ACCEPT_TAC
QED

Theorem slot_copy_snapshot_writeback_mods:
  ^slot_copy_run /\ ^slot_copy_structs /\ ^slot_copy_reserved /\
  dst = FST r /\ ty = vv_type vv /\ ^slot_copy_types /\ ^slot_copy_code /\
  (dty <> ty /\ ~(is_bytestring_type dty /\ is_bytestring_type ty) ==>
    sa0.cs_next_id <= sa.cs_next_id /\ local_ptrs_reserved cenv sa0 /\
    MAP FDOM es0.scopes = MAP FDOM es.scopes /\
    0 < type_memory_size tv /\ type_memory_size dtv < dimword (:256)) /\
  compile_snapshot_vv cenv T vv sm = (snap,ss) /\ vv_operand snap = Var x /\
  compile_get_target_ptr compile_expr cenv bt ss = (r,st) /\
  unwrap_value cenv snap st = (src,sa) /\
  write_target_post_mods H D lo d ctx func cenv cx bt mid ss st u es
    (PlaceR (StoragePlace tr dw dtv)) (Type dty) r Ga tna G tn s /\
  stmt_state_rel H ctx func cenv cx mid u /\ local_ptrs_reserved cenv ss /\
  FLOOKUP u.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < ss.cs_next_id /\
  lo <= b /\ b + type_memory_size tv < dimword (:256) /\
  b + type_memory_size tv <= u.vs_alloca_next /\
  (!n off len. local_region cenv mid.scopes u n off len ==>
     loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off len) /\
  not_fresh_at ss x /\ lookup_var x u = SOME (n2w b) /\
  ptr_covers Ga tna x u (type_memory_size tv) /\
  (!mem. mem_agree_outside tna.t_mem u.vs_memory mem ==> val_in_memory tv v b mem) ==>
  ^slot_copy_outcome
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `dst = FST r` SUBST_ALL_TAC >> qpat_x_assum `ty = vv_type vv` SUBST_ALL_TAC >>
  `val_wf tv v` by drule_then ACCEPT_TAC (cj 1 value_has_type_val_wf) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `ty` |-> `dty`, `k` |-> `dw`, `op` |-> `src`,
    `su` |-> `sa`, `ee` |-> `es`, `G` |-> `Ga`, `tn` |-> `tna`,
    `Gz` |-> `G`, `tnz` |-> `tn`, `z` |-> `s`] (SPEC_ALL slot_copy_snapshot_input_mods)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss])) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `sa = st` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `src = Var x` SUBST_ALL_TAC >>
  `!y. x = y \/ FST r = Var y ==> not_fresh_at sa y` by
    (rpt strip_tac >> gvs[]) >>
  mp_tac (Q.INST [`dst` |-> `FST (r : operand # data_location option # place_ty option)`,
    `ty` |-> `vv_type vv`, `src` |-> `Var x`, `sw` |-> `n2w b : 256 word`]
    (SPEC_ALL slot_copy_compiled_writeback)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    disch_tac >> qexists_tac `ss with cs_next_id := aid` >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
