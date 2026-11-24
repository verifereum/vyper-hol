(* The zero-GAS storage/transient suffix of a word Append. *)
Theory bodyAppendSlotWordMods
Ancestors
  bodyFullAppend bodyFullPostsMods bodyFullShadowBodyInv gasOutcomeFullPostMods
  appendStorageStaticPtr stmtAppendStoragePathPtr appendResolvedStorageRel
  appendStorageGhostPtr stmtSimAppendStorageCompose targetSubscriptStorage accountsRelProps
  fragGasCopyLoop fragGasOriginPtrLoop bodyMemAppendFacts
  allocaHistoryFragment assignTuplePtrLoadStep placeStoreStorage bodySlotCopyFieldsMods
  bodyMemoryDefs bodyInvSplit bodySimFull alist vyperStorage venomInst
  stateFrame stateRelProj bodyFullUnwrapRun freshWrites
  vyperFiniteStoragePreservation vyperStoragePlaceObserved vyperStoragePlaceRegion
  vyperStorageFootprint vyperStorageBackend sourceUnitExecution haltExitProj
  vfmState bodyPtrDefs exprLoweringProps loweringStateRelDefs loweringPosts
  compileEnv exprSimDefs stmtSimDefs venomState ptrDiscipline words finite_map pred_set
  vyperValue exprLowering exprSimUnwrap stmtSimAssignStorageFacts fragGasOriginPtr
  vyperTypeValues vyperTyping fragExec vyperState list rich_list

Theorem append_slot_observed_layout[local]:
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  regions_consistent (FST H) ==>
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  ?rootk root path delta.
    MEM (tr,rootk,root) (FST H) /\
    storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
    w2n slot = w2n rootk + delta /\
    w2n rootk + type_slot_size root <= dimword (:256)
Proof
  simp[storage_place_observed_def] >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac place_store_root_layout >>
  drule_then assume_tac storage_subregion_bounds >>
  `0 < type_slot_size (ArrayTV tv (Dynamic cap))` by simp[type_slot_size_def] >>
  `delta < dimword (:256) /\ w2n root + delta < dimword (:256)` by decide_tac >>
  `w2n (root + n2w delta) = w2n root + delta` by
    simp[word_add_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  conj_tac >- decide_tac >> qexistsl_tac [`root`, `tv'`, `path`, `delta`] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem append_slot_read_ready[local]:
  stmt_state_rel H ctx func cenv cx mid t /\
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  regions_consistent (FST H) /\ eval_operand bop t = SOME slot /\
  dead_lo_ok_mods H D lo cenv cx /\ ghost_inv_at_mods D lo d cenv cx mid G tn t ==>
  (if tr then tload slot t else sload slot t) = lookup_storage slot (get_storage cx mid tr) /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  t.vs_call_ctx.cc_static = cx.txn.is_static /\ allocas_from lo t
Proof
  strip_tac >> drule_all_then strip_assume_tac append_slot_observed_layout >>
  `!raw. storage_read_live H tr raw slot (ArrayTV tv (Dynamic cap))` by
    (gen_tac >> irule storage_place_observed_read_live >> simp[type_slot_size_def]) >>
  conj_tac
  >- (irule (INST_TYPE [alpha |-> ``:256``] (cj 2 target_storage_array_len_ok)) >>
      conj_tac >- (qexists_tac `bop` >> simp[]) >>
      qexistsl_tac [`H`, `cenv`, `ctx`, `func`, `cap`, `tv`] >> simp[]) >>
  `t.vs_call_ctx.cc_static = cx.txn.is_static /\ t.vs_call_ctx.cc_address = cx.txn.target` by
    (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[call_ctx_rel_def]) >>
  simp[] >> conj_tac
  >- (irule (INST_TYPE [alpha |-> ``:256``] storage_dead_key_taint_empty) >>
      qexistsl_tac [`H`, `if tr then contract_transient t else contract_storage t`,
                    `tr`, `ArrayTV tv (Dynamic cap)`] >>
      simp[type_slot_size_def] >> Cases_on `tr` >>
      gvs[ghost_inv_at_mods_def, stor_taint_ok_at_def, dead_lo_ok_mods_def,
          cx_dead_def, contract_storage_def, contract_transient_def, lookup_account_def]) >>
  fs[ghost_inv_at_mods_def]
QED

Theorem append_slot_no_dalloca[local]:
  compile_dynarray_append cenv bop vop 1 1 elem src_ty cap T
    (if tr then LocTransient else LocStorage) sm = ((),sb) ==>
  !pre i post u. emitted_insts sm sb = pre ++ i::post /\
    run_inst_seq pre t = OK u ==> unitTransformDefs$dalloca_no_wrap i u
Proof
  strip_tac >> drule append_storage_word_suffix_footprint_mem >> strip_tac >>
  rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
  strip_tac >> qpat_x_assum `EVERY _ _` mp_tac >> simp[]
QED

Theorem append_slot_capacity_path[local]:
  compile_dynarray_append cenv bop vop 1 1 elem src_ty cap T
    (if tr then LocTransient else LocStorage) sm = ((),sb) /\
  eval_operand bop t = SOME slot /\ eval_operand vop t = SOME w /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sm x) /\
  cap < dimword (:256) /\ op_taint tn bop = {} /\ op_taint tn vop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted /\
  fn_has_code sm sb func /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~(w2n (if tr then tload slot t else sload slot t) < cap) ==>
  ?u Gf tf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t,G,tn) [] (Abort Revert_abort u,Gf,tf)
Proof
  strip_tac >>
  mp_tac (Q.INST [`len` |-> `w2n (if tr then tload slot t else sload slot t)`,
    `D` |-> `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    append_nested_storage_abort_path) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >> strip_tac >>
  drule_all append_storage_word_suffix_code >> strip_tac >>
  `(ctx_has_dalloca ctx ==> !pre i post u. emitted_insts sm sb = pre ++ i::post /\
      run_inst_seq pre t = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (disch_tac >> drule_then (qspec_then `t` ACCEPT_TAC) append_slot_no_dalloca) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) (emitted_insts sm sb)` by
    fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >> strip_tac >>
  qexistsl_tac [`r with vs_inst_idx := j'`, `Gf`, `tf`] >> simp[]
QED

Theorem append_slot_success_path[local]:
  compile_dynarray_append cenv bop vop 1 1 elem src_ty cap T
    (if tr then LocTransient else LocStorage) sm = ((),sb) /\
  eval_operand bop t = SOME slot /\ eval_operand vop t = SOME w /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sm x) /\
  cap < dimword (:256) /\ op_taint tn bop = {} /\ op_taint tn vop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted /\
  fn_has_code sm sb func /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  len = w2n (if tr then tload slot t else sload slot t) /\ len < cap /\
  ~t.vs_call_ctx.cc_static /\ fn_inst_ids_distinct func /\ alloca_history func t /\
  alloca_inv t ==>
  ?u Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,Gf,tf)) /\
    state_frame (u with vs_inst_idx := t.vs_inst_idx) = state_frame
      (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w t)
       else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w t)) /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (if tr then
       tf.t_trans = key_update (key_update tn.t_trans (slot+n2w (1+len)) {}) slot {} /\
       tf.t_stor = tn.t_stor
     else
       tf.t_stor = key_update (key_update tn.t_stor (slot+n2w (1+len)) {}) slot {} /\
       tf.t_trans = tn.t_trans) /\
    (!x. not_fresh_at sm x ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t) /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_current_bb = sb.cs_current_bb /\ ~u.vs_halted /\ alloca_history func u
Proof
  strip_tac >> drule_all append_nested_storage_success_path >>
  disch_then (qspecl_then [`PG`, `G`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) t Gf tf` by
    (gen_tac >> drule_all append_nested_storage_success_path >>
     disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
     metis_tac[fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique]) >>
  `(ctx_has_dalloca ctx ==> !pre i post u. emitted_insts sm sb = pre ++ i::post /\
      run_inst_seq pre t = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (disch_tac >> drule_then (qspec_then `t` ACCEPT_TAC) append_slot_no_dalloca) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) (emitted_insts sm sb)` by fs[EVERY_MEM] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
     asm_rewrite_tac[] >> qexists_tac `sm` >> asm_rewrite_tac[] >> simp[]) >>
  drule_all append_storage_word_suffix_code >> strip_tac >>
  `?rest. DROP t.vs_inst_idx bb.bb_instructions = emitted_insts sm sb ++ rest` by
    metis_tac[IS_PREFIX_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  qpat_x_assum `alloca_history func (u with vs_inst_idx := _ )` mp_tac >>
  qpat_assum `t.vs_inst_idx + LENGTH _ = _` (fn th => pure_rewrite_tac[th]) >>
  strip_tac >>
  `u.vs_current_bb = sb.cs_current_bb /\ ~u.vs_halted` by
    (qpat_assum `state_frame u = _` mp_tac >> Cases_on `tr` >>
     simp[NoAsms, state_frame_def, tstore_def, sstore_def, venom_state_component_equality] >>
     strip_tac >> simp[]) >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`, `Gf`, `tf`] >>
  simp[lookup_var_def] >>
  qpat_assum `state_frame u = _` mp_tac >> Cases_on `tr` >>
  simp[NoAsms, state_frame_def, tstore_def, sstore_def, venom_state_component_equality] >>
  fs[lookup_var_def]
QED

Theorem append_slot_taint_bank[local]:
  MEM (tr,(rootk:bytes32),root) (FST H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  type_slot_size tv = 1 /\ len < cap /\
  X SUBSET {(k,b) | storage_dead H tr st (w2n k) b} ==>
  key_update (key_update X (slot+n2w (1+len)) {}) slot {} SUBSET
    {(k,b) | storage_dead H tr
       (update_storage slot (n2w (len+1)) (update_storage (slot+n2w (1+len)) w st))
       (w2n k) b}
Proof
  simp[SUBSET_DEF, pairTheory.FORALL_PROD, key_update_def] >> rpt strip_tac >>
  `storage_dead H tr st (w2n p_1) p_2` by metis_tac[] >>
  irule (SRULE [arithmeticTheory.ADD_COMM] append_resolved_storage_dead_mono) >>
  reverse conj_tac >- simp[] >> qexistsl_tac [`cap`,`delta`,`path`,`root`,`rootk`,`tv`] >> simp[]
QED

Theorem append_slot_endpoint_fields[local]:
  state_frame (u with vs_inst_idx := t.vs_inst_idx) = state_frame
    (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w t)
     else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w t)) ==>
  state_frame u = state_frame
    ((if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w t)
      else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w t))
     with vs_inst_idx := u.vs_inst_idx) /\
  u.vs_memory = t.vs_memory /\ u.vs_data_section = t.vs_data_section /\
  u.vs_immutables = t.vs_immutables /\ u.vs_allocas = t.vs_allocas /\
  u.vs_alloca_next = t.vs_alloca_next /\ u.vs_call_ctx = t.vs_call_ctx /\
  u.vs_fmp = t.vs_fmp /\ u.vs_initial_fmp = t.vs_initial_fmp /\
  (let a = t.vs_call_ctx.cc_address in
   let st = (t.vs_accounts a).storage in
   let ts = t.vs_transient a in
     (u.vs_accounts a).storage =
       (if tr then st else
        update_storage slot (n2w (len+1)) (update_storage (slot+n2w (1+len)) w st)) /\
     u.vs_transient a =
       (if tr then update_storage slot (n2w (len+1)) (update_storage (slot+n2w (1+len)) w ts)
        else ts))
Proof
  Cases_on `tr` >>
  simp[NoAsms, state_frame_def, tstore_def, sstore_def, venom_state_component_equality] >>
  strip_tac >> simp[lookup_account_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem append_slot_storage_taint[local]:
  MEM (tr,(rootk:bytes32),root) (FST H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  type_slot_size tv = 1 /\ len < cap /\
  state_frame (u with vs_inst_idx := t.vs_inst_idx) = state_frame
    (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w t)
     else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w t)) /\
  t.vs_call_ctx.cc_address = cx.txn.target /\
  dead_lo_ok_mods H D lo cenv cx /\ stor_taint_ok_at D tn t /\
  tf.t_imm = tn.t_imm /\
  (if tr then
     tf.t_trans = key_update (key_update tn.t_trans (slot+n2w (1+len)) {}) slot {} /\
     tf.t_stor = tn.t_stor
   else
     tf.t_stor = key_update (key_update tn.t_stor (slot+n2w (1+len)) {}) slot {} /\
     tf.t_trans = tn.t_trans) ==>
  stor_taint_ok_at D tf u
Proof
  strip_tac >> drule_then strip_assume_tac append_slot_endpoint_fields >>
  qpat_x_assum `state_frame _ = _` kall_tac >>
  qpat_x_assum `state_frame _ = _` kall_tac >>
  qpat_assum `t.vs_call_ctx.cc_address = cx.txn.target`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  Cases_on `tr` >>
  gvs[stor_taint_ok_at_def, dead_lo_ok_mods_def, cx_dead_def] >>
  irule (SRULE [arithmeticTheory.ADD_COMM] append_slot_taint_bank) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cap`,`delta`,`path`,`root`,`rootk`,`tv`] >> simp[]
QED

Theorem append_slot_local_region[local]:
  local_ptrs_reserved cenv sm /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t) ==>
  local_region cenv sc u n b sz = local_region cenv sc t n b sz
Proof
  strip_tac >> simp[local_region_def] >> eq_tac >> rpt strip_tac >>
  `not_fresh_at sm p` by metis_tac[local_ptrs_reserved_def] >>
  qpat_assum `!x. not_fresh_at sm x ==> _` drule >> strip_tac >>
  qexistsl_tac [`entry`,`p`,`w`] >> fs[]
QED

Theorem append_slot_immutable_frame[local]:
  immutable_frame_mods func cenv cx mid t /\
  ee.scopes = mid.scopes /\ ee.immutables = mid.immutables /\
  u.vs_memory = t.vs_memory /\ u.vs_data_section = t.vs_data_section /\
  u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
  (!n b sz. local_region cenv ee.scopes u n b sz =
             local_region cenv mid.scopes t n b sz) ==>
  immutable_frame_mods func cenv cx ee u
Proof
  simp[immutable_frame_mods_def] >> strip_tac >> conj_tac
  >- (qpat_x_assum `immutables_rel_mods _ _ _ _ _` mp_tac >>
      simp[immutables_rel_mods_def, immutables_rel_def]) >>
  fs[immutable_alloca_sep_mods_def] >> rpt strip_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`t`,`mid`] >> simp[] >>
  rpt gen_tac >> disch_tac >> qexists_tac `id` >>
  `!c z. local_region (c with ce_module := src) mid.scopes z id b sz =
          local_region c mid.scopes z id b sz` by simp[local_region_def] >>
  metis_tac[]
QED

Theorem append_slot_success_post[local]:
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid = (INL (),ee) /\
  ee = set_storage cx mid tr (update_storage slot (n2w (len+1))
          (update_storage (slot+n2w (1+len)) w (get_storage cx mid tr))) /\
  len < cap /\ type_slot_size tv = 1 /\ value_has_type tv v /\
  well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
  regions_consistent (FST H) /\
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  storage_well_formed_on cx mid (FST H) /\ stmt_state_rel H ctx func cenv cx mid t /\
  immutable_frame_mods func cenv cx mid t /\ return_buf_sep d cenv mid t /\
  dead_lo_ok_mods H D lo cenv cx /\ ghost_inv_at_mods D lo d cenv cx mid G tn t /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  state_frame (u with vs_inst_idx := t.vs_inst_idx) = state_frame
    (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w t)
     else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w t)) /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
  (if tr then
     tf.t_trans = key_update (key_update tn.t_trans (slot+n2w (1+len)) {}) slot {} /\
     tf.t_stor = tn.t_stor
   else
     tf.t_stor = key_update (key_update tn.t_stor (slot+n2w (1+len)) {}) slot {} /\
     tf.t_trans = tn.t_trans) ==>
  stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) u /\
  immutable_frame_mods func cenv cx (ee with gas_obs := []) u /\
  storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
  ghost_inv_at_mods D lo d cenv cx (ee with gas_obs := []) Gf tf u /\
  return_buf_sep d cenv (ee with gas_obs := []) u
Proof
  strip_tac >>
  drule_all_then strip_assume_tac append_slot_observed_layout >>
  drule_then strip_assume_tac append_slot_endpoint_fields >>
  `ee.scopes = mid.scopes /\ ee.immutables = mid.immutables` by
    (Cases_on `tr` >> fs[set_storage_def]) >>
  `!n b sz. local_region cenv ee.scopes u n b sz =
             local_region cenv mid.scopes t n b sz` by
    (simp[] >> metis_tac[append_slot_local_region]) >>
  conj_tac
  >- (drule_all stmt_state_rel_append_resolved_storage_updates >>
      disch_then (qspec_then `w` assume_tac) >>
      qmatch_asmsub_abbrev_tac `state_frame (dest with vs_inst_idx := u.vs_inst_idx)` >>
      rewrite_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
      irule stmt_state_rel_old_vars_frame_ptr >> qexistsl_tac [`dest`,`sm`] >>
      conj_tac
      >- (qpat_assum `!x. not_fresh_at sm x ==> _` (mp_tac o SIMP_RULE bool_ss [AND_IMP_INTRO]) >>
          Cases_on `tr` >> simp[Abbr `dest`,lookup_var_def,tstore_def,sstore_def]) >>
      asm_rewrite_tac[] >> gvs[]) >>
  conj_tac
  >- (irule append_slot_immutable_frame >> asm_rewrite_tac[] >> simp[] >>
      qexistsl_tac [`mid`,`t`] >> simp[] >>
      qpat_assum `ee.scopes = mid.scopes` (fn th =>
        qpat_assum `!n b sz. local_region _ _ _ _ _ _ = _`
          (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  conj_tac
  >- (`storage_well_formed_on cx ee (FST H)` by
        drule_all_then ACCEPT_TAC append_subregion_preserves_storage_well_formed_on >>
      `storage_well_formed_on cx (ee with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx ee (FST H)` suffices_by simp[] >>
      irule storage_well_formed_on_backends >> simp[]) >>
  conj_tac
  >- (`t.vs_call_ctx.cc_address = cx.txn.target` by
        (drule stmt_state_rel_state_rel >>
         disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >> simp[call_ctx_rel_def]) >>
      `stor_taint_ok_at D tn t` by fs[ghost_inv_at_mods_def] >>
      `stor_taint_ok_at D tf u` by drule_all_then ACCEPT_TAC append_slot_storage_taint >>
      irule slot_copy_ghost_frame_mods >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G`,`mid`,`t`,`sm`,`tn`] >>
      simp[] >> metis_tac[local_ptrs_reserved_imm_base]) >>
  irule (INST_TYPE [alpha |-> ``:256``] bodyFullSharedTheory.return_buf_sep_locals_kept) >>
  conj_tac
  >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
      qpat_assum `u.vs_allocas = t.vs_allocas` (fn th => pure_rewrite_tac[allocas_from_def,th]) >>
      qpat_assum `return_buf_sep _ _ _ _`
        (ACCEPT_TAC o REWRITE_RULE [allocas_from_def] o cj 1 o REWRITE_RULE [return_buf_sep_def])) >>
  qexistsl_tac [`H`,`ctx`,`cx`,`mid`,`func`,`t`,`sm`] >> simp[] >>
  metis_tac[]
QED

Theorem append_slot_error_outcome[local]:
  ~t.vs_halted /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid =
    (INR (Error (RuntimeError msg)),mid) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
          (Abort reason u,Gf,tf)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v) (mid,t,G,tn) Q
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))
Proof
  strip_tac >> irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl_tac [`Gf`,`mid`,`Abort reason u`,`INR (Error (RuntimeError msg))`,`tf`] >>
  simp[exit_result_def, stmt_exit_ptr_def, expr_exit_def, halt_exit_def] >>
  rpt gen_tac >> drule append_storage_place_gas_obs >> simp[]
QED

Theorem append_slot_written_frame[local]:
  ee.scopes = mid.scopes /\
  (!n b sz. local_region cenv ee.scopes u n b sz =
             local_region cenv mid.scopes t n b sz) /\
  u.vs_memory = t.vs_memory /\ alloca_frame cenv es sa s0 cenv mid t ==>
  alloca_frame cenv es sa s0 cenv ee u
Proof
  strip_tac >> qpat_x_assum `alloca_frame _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[alloca_frame_def] >>
  qpat_assum `!n b sz. local_region _ _ _ _ _ _ = _` (fn th => simp[th])
QED

(* The reached RHS is the initial state of this suffix.  All storage and
   taint observations below concern that state, not the incoming statement. *)
Theorem append_slot_word_landing_mods:
  is_word_type elem /\ evaluate_type (get_tenv cx) elem = SOME tv /\ value_has_type tv v /\
  compile_dynarray_append cenv bop vop 1 1 elem src_ty cap T
    (if tr then LocTransient else LocStorage) sm = ((),sb) /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sm x) /\
  eval_operand bop t = SOME slot /\ eval_operand vop t = SOME (typed_val_to_w256 tv v) /\
  op_taint tn bop = {} /\ op_taint tn vop = {} /\ cap < dimword (:256) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\ immutable_frame_mods func cenv cx mid t /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t /\
    storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap)))) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  fn_inst_ids_distinct func /\ fn_has_code sm sb func /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sm t /\ return_buf_sep d cenv mid t /\
  alloca_history func t /\ alloca_inv t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  alloca_frame cenv es sa s0 cenv mid t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  cenv_top_ext cenv0 cenv mid.scopes ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v) (mid,t,G,tn)
    (\H res ee Gf tf u. ?cenv'.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv' = cenv) /\
      cenv_top_ext cenv0 cenv' ee.scopes /\
      stmt_state_rel H ctx func cenv' cx ee u /\ immutable_frame_mods func cenv' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv' sb u /\
      alloca_history func u /\ return_buf_sep d cenv' ee u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv' ee u /\
      (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem))
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))
Proof
  strip_tac >>
  `?H. valid_horizon cx st0 H mid.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _` drule >> strip_tac >>
  `regions_consistent (FST H)` by fs[valid_horizon_def] >>
  `dead_lo_ok_mods H (DF H) lo cenv cx` by simp[] >>
  drule_all_then strip_assume_tac append_slot_read_ready >>
  qabbrev_tac `len = w2n (lookup_storage slot (get_storage cx mid tr))` >>
  Cases_on `len < cap`
  >- (Cases_on `cx.txn.is_static`
      >- suspend "static" >> suspend "success") >>
  suspend "capacity"
QED

Resume append_slot_word_landing_mods[capacity]:
  `~(w2n (if tr then tload slot t else sload slot t) < cap)` by simp[Abbr `len`] >>
  `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid =
     (INR (Error (RuntimeError "append full storage array")),mid)` by
    (irule vyperStorageBackendTheory.append_storage_full >> fs[Abbr `len`]) >>
  drule_all append_slot_capacity_path >>
  strip_tac >>
  irule append_slot_error_outcome >> simp[] >> metis_tac[]
QED

Resume append_slot_word_landing_mods[static]:
  `w2n (if tr then tload slot t else sload slot t) < cap` by simp[Abbr `len`] >>
  `t.vs_call_ctx.cc_static` by simp[] >>
  `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid =
     (INR (Error (RuntimeError "write in static context")),mid)` by
    (irule stmtSimAppendStorageTheory.append_storage_static >> fs[Abbr `len`]) >>
  drule_all append_storage_word_static_origin_path >> strip_tac >>
  irule append_slot_error_outcome >> simp[] >> metis_tac[]
QED

Resume append_slot_word_landing_mods[success]:
  `len = w2n (if tr then tload slot t else sload slot t)` by simp[Abbr `len`] >>
  `~t.vs_call_ctx.cc_static` by simp[] >>
  qabbrev_tac `w = typed_val_to_w256 tv v` >>
  `type_slot_size tv = 1` by metis_tac[word_type_slot_size] >>
  `encode_value tv v = SOME [(0,w)]` by
    (simp[Abbr `w`] >> metis_tac[encode_value_word_typed]) >>
  `well_formed_type_value (ArrayTV tv (Dynamic cap))` by
    (`well_formed_type_value tv` by metis_tac[evaluate_type_well_formed] >>
     simp[well_formed_type_value_def,type_slot_size_def]) >>
  qabbrev_tac `ee = set_storage cx mid tr (update_storage slot (n2w (len+1))
                      (update_storage (slot+n2w (1+len)) w (get_storage cx mid tr)))` >>
  `len = w2n (lookup_storage slot (get_storage cx mid tr))` by simp[Abbr `len`] >>
  `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid = (INL (),ee)` by
    (drule_all vyperStorageBackendTheory.append_storage_word_success >>
     strip_tac >> qpat_assum `append_place _ _ _ _ = _` (fn th => pure_rewrite_tac[th]) >>
     Cases_on `tr` >> simp[NoAsms,Abbr `ee`,set_storage_def]) >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v (mid with gas_obs := tail)
      = (INL (),ee with gas_obs := tail)` by
    (gen_tac >> drule append_storage_place_gas_obs >> simp[]) >>
  drule_all append_slot_success_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  `ee.storage_trace = mid.storage_trace /\ ee.scopes = mid.scopes` by
    (Cases_on `tr` >> simp[NoAsms,Abbr `ee`,set_storage_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by metis_tac[] >>
  drule_then strip_assume_tac append_slot_endpoint_fields >>
  `return_buf_frame d cenv sb u` by
    (drule append_storage_word_suffix_grows_mem >> strip_tac >>
     irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`t`,`sm`] >> simp[] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` by
    (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`,`tn`] >> simp[] >> metis_tac[]) >>
  `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) u` by
    (irule append_slot_written_frame >> qexistsl_tac [`mid`,`t`] >> simp[] >>
     metis_tac[append_slot_local_region]) >>
  irule gas_outcome_full_mods_pure >> asm_rewrite_tac[] >>
  qexistsl_tac [`Gf`,`ee`,`INL ()`,`u`,`tf`] >>
  asm_rewrite_tac[] >> qx_gen_tac `hz` >> rpt strip_tac >> BETA_TAC >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `hz` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `regions_consistent (FST hz)` by fs[valid_horizon_def] >>
  `dead_lo_ok_mods hz (DF hz) lo cenv cx` by simp[] >>
  `ee = set_storage cx mid tr (update_storage slot (n2w (len+1))
         (update_storage (slot+n2w (1+len)) w (get_storage cx mid tr)))` by
    simp[NoAsms,Abbr `ee`] >>
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  drule_all_then strip_assume_tac append_slot_success_post >>
  ntac 2 (qpat_x_assum `state_frame _ = _` kall_tac) >>
  qexists_tac `cenv` >>
  `~block_is_terminated sb` by drule_then ACCEPT_TAC append_storage_word_suffix_open_mem >>
  qpat_x_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  asm_rewrite_tac[] >> simp[stmt_lands_def] >>
  strip_tac >>
  `allocas_below_fmp t` by metis_tac[] >>
  qpat_assum `allocas_below_fmp t` (strip_assume_tac o REWRITE_RULE [allocas_below_fmp_def]) >>
  simp[allocas_below_fmp_def] >> first_assum ACCEPT_TAC
QED

Finalise append_slot_word_landing_mods
