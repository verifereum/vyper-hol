(* The selected internal call executes the transient guard once, in the
   entered callee. The concrete cursor and taint are independent of H. *)
Theory bodySelectedLockLandingMods
Ancestors
  nonreentrantEntryPath fragGasCopySeqLiftProps fragGasOriginPtrLoop
  fragGasCopyLoop nonreentrantEntry nonreentrantEquiv bodyFullPostsMods
  bodyForRangeScalarFrameMods bodyFullShared
  stateRelProj guardSourceExternalPrimitives accountsRelProps
  bodyFullIfExpReach bodyFullPathHistory externalCallSelected
  vyperStorageTrace vyperStorageFootprint gasStorage vyperInterpreter
  vyperState vyperAST venomState venomInst venomExecSemantics compileEnv
  compileVyper transientLockProps transientLockPtr loweringStateRelDefs
  exprLoweringProps bodyFullShadowBodyInv bodyPtrDefs ptrDiscipline pred_set
  words finite_map list rich_list ctorDeployLoweringSource fragGasSeqPtr
  emitHelperProps vyperExternalEntryStorageFrame

Theorem selected_lock_trace[local]:
  cx.nonreentrant_slot = SOME key ==>
  !view es. (SND (lock_if_nr cx T view es)).storage_trace =
    es.storage_trace ++ [StorageLock key]
Proof
  strip_tac >> rpt gen_tac >> Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  Cases_on `lookup_storage (n2w key) (es.tStorage cx.txn.target) = 1w` >>
  simp[lock_if_nr_def, acquire_nonreentrant_lock_execution,
       ignore_bind_def, bind_def, return_def, check_not_static_def,
       check_def, assert_def, raise_def]
QED

Theorem selected_lock_horizon[local]:
  valid_horizon cx st H (tr ++ [StorageLock key]) ==>
  valid_horizon cx st H tr /\
  storage_locks_separated (FST H) (SND H) /\ MEM key (SND H)
Proof
  simp[valid_horizon_def, storage_observations_ok_def, storage_trace_locks_def]
QED

Theorem selected_lock_source_fields[local]:
  lock_if_nr cx nr view es = (res,locked) ==>
  locked.scopes = es.scopes /\ locked.immutables = es.immutables /\
  locked.accounts = es.accounts /\ locked.outcomes = es.outcomes
Proof
  strip_tac >> drule_then assume_tac lock_if_nr_scopes >> simp[] >>
  Cases_on `nr` >> fs[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> fs[raise_def] >>
  gvs[acquire_nonreentrant_lock_execution, ignore_bind_def, bind_def,
      check_not_static_def, check_def, assert_def, return_def, raise_def,
      COND_RATOR, AllCaseEqs()]
QED

Theorem selected_lock_read[local]:
  state_rel H callee ce p es s /\ MEM key (SND H) /\ key < dimword (:256) ==>
  lookup_storage (n2w key) (es.tStorage p.txn.target) = tload (n2w key) s /\
  s.vs_call_ctx.cc_static = p.txn.is_static
Proof
  strip_tac >> drule_then assume_tac state_rel_call_ctx_rel >>
  reverse conj_tac >- fs[call_ctx_rel_def] >>
  `storage_read_live H T (es.tStorage p.txn.target)
     (n2w key) (BaseTV (UintT 256))` by simp[nonreentrant_slot_read_live] >>
  drule_all_then ACCEPT_TAC state_rel_transient_lookup
QED

Theorem selected_lock_clean[local]:
  dead_lo_ok_mods (H:(bool # 256 word # type_value) list # num list) D lo ce p /\ stor_taint_ok_at D tn s /\
  MEM key (SND H) /\ key < dimword (:256) ==>
  !b. (n2w key,b) NOTIN tn.t_trans
Proof
  simp[dead_lo_ok_mods_def, stor_taint_ok_at_def] >> strip_tac >>
  qpat_assum `tn.t_trans SUBSET _`
    (mp_tac o REWRITE_RULE [SUBSET_DEF]) >>
  Cases_on `s.vs_call_ctx.cc_address = p.txn.target` >>
  simp[sourceUnitExecutionTheory.cx_dead_def, storage_dead_def] >>
  disch_tac >> gen_tac >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem selected_lock_run[local]:
  cx.nonreentrant_slot = SOME key /\
  lookup_storage (n2w key) (es.tStorage cx.txn.target) = tload (n2w key) s /\
  s.vs_call_ctx.cc_static = cx.txn.is_static /\
  compile_nonreentrant_lock key T view pro = ((),a) ==>
  (?e u. lock_if_nr cx T view es = (INL (),e) /\
          run_inst_seq (emitted_insts pro a) s = OK u) \/
  (?e u. lock_if_nr cx T view es = (INR (Error (RuntimeError "nonreentrant lock")),e) /\
          run_inst_seq (emitted_insts pro a) s = Abort Revert_abort u) \/
  (?e u. lock_if_nr cx T view es = (INR (Error (RuntimeError "write in static context")),e) /\
          run_inst_seq (emitted_insts pro a) s = Abort ExHalt_abort u)
Proof
  strip_tac >> drule_then assume_tac compile_nonreentrant_lock_transient_code >>
  Cases_on `tload (n2w key) s = 1w` >> Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  simp[transient_lock_code_execution, lock_if_nr_def,
       acquire_nonreentrant_lock_execution, ignore_bind_def, bind_def,
       return_def, check_not_static_def, check_def, assert_def, raise_def]
QED

Theorem selected_lock_code[local]:
  compile_nonreentrant_lock key T view pro = ((),a) ==>
  a.cs_current_bb = pro.cs_current_bb /\
  inst_extends pro a /\ ~block_is_terminated a /\
  a.cs_next_var = pro.cs_next_var + 3 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA /\
              ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
    (emitted_insts pro a) /\
  (!i u. MEM i (emitted_insts pro a) ==> unitTransformDefs$dalloca_no_wrap i u)
Proof
  strip_tac >> drule_then strip_assume_tac compile_nonreentrant_lock_transient_same_block >>
  drule_then assume_tac compile_nonreentrant_lock_transient_code >>
  drule_then assume_tac transientLockFramePropsTheory.compile_nonreentrant_lock_transient_counter >>
  Cases_on `view` >> Cases_on `pro.cs_current_insts` >>
  simp[emitHelperPropsTheory.inst_extends_def, block_is_terminated_def,
       transient_lock_code_def, mk_inst_def, is_terminator_def,
       listTheory.LAST_APPEND_CONS, listTheory.LAST_CONS_cond] >>
  rpt strip_tac >> gvs[unitTransformDefsTheory.dalloca_no_wrap_def]
QED

Theorem selected_lock_path[local]:
  compile_nonreentrant_lock key T view pro = ((),a) /\
  fn_has_code pro a callee /\
  ~s.vs_halted /\ s.vs_current_bb = pro.cs_current_bb /\
  s.vs_inst_idx = LENGTH pro.cs_current_insts /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!b. (n2w key,b) NOTIN tn.t_trans) ==>
  (?G' tn'. !u. run_inst_seq (emitted_insts pro a) s = OK u ==>
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG) (s,G,tn) []
           (OK (u with vs_inst_idx := LENGTH a.cs_current_insts),G',tn')) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at pro x ==>
         FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))) /\
  (!ab u. run_inst_seq (emitted_insts pro a) s = Abort ab u ==>
    ?j G' tn'. !D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG) (s,G,tn) []
           (Abort ab (u with vs_inst_idx := j),G',tn'))
Proof
  strip_tac >>
  drule_then strip_assume_tac selected_lock_code >>
  drule_then assume_tac compile_nonreentrant_lock_transient_code >>
  drule_all_then strip_assume_tac compile_nonreentrant_lock_transient_prefix >>
  `run_inst_seq_mem_ok (emitted_insts pro a) s` by
    (irule lock_opcodes_mem_ok >> Cases_on `view` >> simp[transient_lock_code_def]) >>
  `ctx_has_dalloca ctx ==>
   !pre i post u. emitted_insts pro a = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
                  unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac >- suspend "success" >> suspend "abort"
QED

Resume selected_lock_path[success]:
  Cases_on `?u. run_inst_seq (emitted_insts pro a) s = OK u`
  >- (pop_assum strip_assume_tac >>
      `tload (n2w key) s <> 1w /\ (~view ==> ~s.vs_call_ctx.cc_static)` by
        (qpat_assum `run_inst_seq _ s = OK u` mp_tac >> Cases_on `view` >>
         Cases_on `tload (n2w key) s = 1w` >> Cases_on `s.vs_call_ctx.cc_static` >>
         gvs[transient_lock_code_execution]) >>
      `!D. ?P N. inst_seq_ptr D 0 ctx callee PG G tn
         (transient_lock_code key view pro) s P N /\
         N.t_mem = tn.t_mem /\ N.t_stor = tn.t_stor /\
         N.t_trans = tn.t_trans /\ N.t_imm = tn.t_imm /\
         (!x. not_fresh_at pro x ==>
              FLOOKUP P x = FLOOKUP G x /\ op_taint N (Var x) = op_taint tn (Var x))` by
        (gen_tac >> irule transient_lock_code_ptr_frame >> simp[]) >>
      first_assum (qspec_then `ARB:dead` strip_assume_tac) >>
      qexistsl_tac [`P`, `N`] >> gen_tac >> disch_tac >>
      reverse conj_tac >- (simp[] >> metis_tac[]) >>
      gen_tac >>
      `inst_seq_ptr D 0 ctx callee PG G tn (emitted_insts pro a) s P N` by
        (simp[] >> first_x_assum (qspec_then `D` strip_assume_tac) >>
         metis_tac[inst_seq_ptr_ghost_unique]) >>
      `s.vs_inst_idx + LENGTH (emitted_insts pro a) = LENGTH a.cs_current_insts` by
        fs[inst_extends_def] >>
      qpat_assum `_ + LENGTH _ = LENGTH a.cs_current_insts`
        (once_rewrite_tac o single o SYM) >>
      `gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG) (s,G,tn) []
         (OK (u' with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts pro a)),P,N) /\
       allocas_from lo u'` suffices_by simp[] >>
      irule run_inst_seq_origin_ptr_lift >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
      >- fs[EVERY_MEM] >>
      qexists_tac `bb` >> conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `s.vs_inst_idx = _` (rewrite_tac o single o SYM) >>
      qpat_assum `emitted_insts pro a = _` (rewrite_tac o single) >>
      first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`tn`] >> metis_tac[]
QED

Resume selected_lock_path[abort]:
  rpt strip_tac >>
  `tload (n2w key) s = 1w \/ ~view /\ s.vs_call_ctx.cc_static` by
    (qpat_assum `run_inst_seq _ s = Abort _ _` mp_tac >> Cases_on `view` >>
     Cases_on `tload (n2w key) s = 1w` >> Cases_on `s.vs_call_ctx.cc_static` >>
     gvs[transient_lock_code_execution]) >>
  `key_taint tn.t_trans (n2w key) = {}` by simp[key_taint_def, EXTENSION] >>
  `!D. ?P N. inst_seq_ptr D 0 ctx callee PG G tn (transient_lock_code key view pro) s P N` by
    (gen_tac >> irule transient_lock_abort_ptr_ghost >> simp[]) >>
  first_assum (qspec_then `ARB:dead` strip_assume_tac) >>
  `!D. inst_seq_ptr D lo ctx callee PG G tn (emitted_insts pro a) s P N` by
    (gen_tac >> irule inst_seq_ptr_lower_bound_transport >> simp[] >> conj_tac
     >- fs[EVERY_MEM] >>
     qexists_tac `0` >> simp[] >> first_x_assum (qspec_then `D` strip_assume_tac) >>
     gvs[] >> metis_tac[inst_seq_ptr_ghost_unique]) >>
  `isPREFIX (emitted_insts pro a) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `emitted_insts pro a = _` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) (emitted_insts pro a)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >>
  disch_then (qx_choose_then `j` assume_tac) >>
  qexistsl_tac [`j`,`P`,`N`] >> metis_tac[]
QED

Finalise selected_lock_path

Theorem selected_lock_checked_fields[local]:
  let chk = transient_lock_checked_state pro key s in
  chk.vs_memory = s.vs_memory /\ chk.vs_allocas = s.vs_allocas /\
  chk.vs_alloca_next = s.vs_alloca_next /\ chk.vs_call_ctx = s.vs_call_ctx /\
  chk.vs_accounts = s.vs_accounts /\ chk.vs_transient = s.vs_transient /\
  chk.vs_immutables = s.vs_immutables /\ chk.vs_data_section = s.vs_data_section /\
  chk.vs_fmp = s.vs_fmp /\ chk.vs_initial_fmp = s.vs_initial_fmp /\
  chk.vs_current_bb = s.vs_current_bb /\ chk.vs_halted = s.vs_halted /\
  (!x. not_fresh_at pro x ==> lookup_var x chk = lookup_var x s)
Proof
  simp[transient_lock_checked_state_def, update_var_def, not_fresh_at_def,
       lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem selected_lock_target_shape[local]:
  compile_nonreentrant_lock key T view pro = ((),a) /\
  run_inst_seq (emitted_insts pro a) s = OK u ==>
  (u = (if view then transient_lock_checked_state pro key s else
        tstore (n2w key) 1w (transient_lock_checked_state pro key s)))
Proof
  strip_tac >> drule_then assume_tac compile_nonreentrant_lock_transient_code >>
  Cases_on `view` >> Cases_on `tload (n2w key) s = 1w` >>
  Cases_on `s.vs_call_ctx.cc_static` >> gvs[transient_lock_code_execution]
QED

Theorem selected_lock_target_fields[local]:
  compile_nonreentrant_lock key T view pro = ((),a) /\
  run_inst_seq (emitted_insts pro a) s = OK u /\ fresh_vars_wrt pro s ==>
  let at_body = u with vs_inst_idx := LENGTH a.cs_current_insts in
  fresh_vars_wrt a at_body /\
  at_body.vs_memory = s.vs_memory /\ at_body.vs_allocas = s.vs_allocas /\
  at_body.vs_alloca_next = s.vs_alloca_next /\
  at_body.vs_call_ctx = s.vs_call_ctx /\ at_body.vs_accounts = s.vs_accounts /\
  at_body.vs_immutables = s.vs_immutables /\ at_body.vs_data_section = s.vs_data_section /\
  at_body.vs_fmp = s.vs_fmp /\ at_body.vs_initial_fmp = s.vs_initial_fmp /\
  at_body.vs_current_bb = s.vs_current_bb /\ at_body.vs_halted = s.vs_halted /\
  (!x. not_fresh_at pro x ==> lookup_var x at_body = lookup_var x s)
Proof
  strip_tac >> drule_all_then assume_tac selected_lock_target_shape >>
  drule_then assume_tac transientLockFramePropsTheory.compile_nonreentrant_lock_transient_counter >>
  `fresh_vars_wrt a (transient_lock_checked_state pro key s)` by
    (irule transientLockFramePropsTheory.transient_lock_checked_fresh_vars >> simp[]) >>
  qspecl_then [`pro`,`key`,`s`] (strip_assume_tac o SIMP_RULE bool_ss [LET_THM])
    (Q.GENL [`pro`,`key`,`s`] selected_lock_checked_fields) >>
  Cases_on `view` >>
  gvs[fresh_vars_wrt_def, lookup_var_def, tstore_def]
QED

Theorem selected_lock_source_success[local]:
  p.nonreentrant_slot = SOME key /\ lock_if_nr p T view es = (INL (),locked) ==>
  acquire_nonreentrant_lock p.txn.target key view es = (INL (),locked) /\
  (~view ==> ~p.txn.is_static) /\
  lookup_storage (n2w key) (es.tStorage p.txn.target) <> 1w
Proof
  strip_tac >> Cases_on `view` >> Cases_on `p.txn.is_static` >>
  Cases_on `lookup_storage (n2w key) (es.tStorage p.txn.target) = 1w` >>
  gvs[lock_if_nr_def, acquire_nonreentrant_lock_execution, ignore_bind_def,
      bind_def, check_not_static_def, check_def, assert_def, raise_def, return_def]
QED

Theorem selected_lock_stmt_rel[local]:
  storage_locks_separated (FST H) (SND H) /\ MEM key (SND H) /\
  key < dimword (:256) /\ p.nonreentrant_slot = SOME key /\
  lock_if_nr p T view es = (INL (),locked) /\
  lookup_storage (n2w key) (es.tStorage p.txn.target) = tload (n2w key) s /\
  compile_nonreentrant_lock key T view pro = ((),a) /\
  run_inst_seq (emitted_insts pro a) s = OK u /\ fresh_vars_wrt pro s /\
  stmt_state_rel H ctx callee ce p es s /\ local_ptrs_reserved ce pro ==>
  stmt_state_rel H ctx callee ce p locked (u with vs_inst_idx := LENGTH a.cs_current_insts)
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx] >>
  drule_all_then strip_assume_tac selected_lock_source_success >>
  drule_then assume_tac stmt_state_rel_state_rel >>
  `tload (n2w key) s <> 1w` by metis_tac[] >>
  `state_rel H callee ce p locked u` by
    (drule_all_then strip_assume_tac compile_nonreentrant_lock_source_correct >> gvs[]) >>
  drule_then strip_assume_tac selected_lock_source_fields >>
  drule_all_then assume_tac selected_lock_target_shape >>
  qabbrev_tac `chk = transient_lock_checked_state pro key s` >>
  `stmt_state_rel H ctx callee ce p es chk` by
    (simp[Abbr `chk`] >> irule transient_lock_checked_stmt_state_rel >> simp[]) >>
  `immutable_alloca_sep callee ce p es chk` by fs[stmt_state_rel_def] >>
  `immutable_alloca_sep callee ce p locked u` by
    (irule immutable_alloca_sep_fields >> qexistsl_tac [`chk`,`es`] >>
     Cases_on `view` >> simp[tstore_def] >> rpt strip_tac >>
     qexists_tac `id` >> fs[local_region_def, lookup_var_def]) >>
  `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==>
     immutable_alloca_sep callee (ce with ce_module := src) p locked u` by
    (rpt strip_tac >>
     irule immutable_alloca_sep_fields >> qexistsl_tac [`chk`,`es`] >>
     qpat_assum `stmt_state_rel _ _ _ _ _ es chk`
       (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
     Cases_on `view` >> simp[tstore_def] >> rpt strip_tac
     >- metis_tac[] >>
     qexists_tac `id` >> fs[local_region_def, lookup_var_def]) >>
  `immutable_base_zero ce chk` by metis_tac[stmt_state_rel_immutable_base_zero] >>
  irule stmt_state_rel_allocas_frame >> simp[] >> conj_tac
  >- (Cases_on `view` >> fs[immutable_base_zero_alt, tstore_def]) >>
  qexistsl_tac [`es`,`chk`] >> Cases_on `view` >> simp[tstore_def]
QED

Theorem selected_lock_ghost_tstore[local]:
  dead_lo_ok_mods (H:(bool # 256 word # type_value) list # num list) D lo ce p /\ storage_locks_separated (FST H) (SND H) /\
  MEM key (SND H) /\ key < dimword (:256) /\ ghost_inv_at_mods D lo d ce p e P N s ==>
  ghost_inv_at_mods D lo d ce p e P N (tstore (n2w key) value s)
Proof
  strip_tac >>
  `!st j b. storage_dead H T (update_storage (n2w key) value st) j b =
            storage_dead H T st j b` by
    (rpt gen_tac >> irule nonreentrantSourceTheory.nonreentrant_storage_dead_frame >> simp[]) >>
  `stor_taint_ok_at D N (tstore (n2w key) value s)` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     gvs[dead_lo_ok_mods_def, stor_taint_ok_at_def,
        sourceUnitExecutionTheory.cx_dead_def, tstore_def, combinTheory.APPLY_UPDATE_THM]) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  Cases_on `d`
  >- (simp[ghost_inv_at_mods_def, tstore_def, ptr_covers_def,
           return_buf_ptr_def, lookup_var_def, allocas_from_def] >>
      strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rename1 `ghost_inv_at_mods _ _ (SOME rb) _ _ _ _ _ _ ==> _` >> PairCases_on `rb` >>
  simp[ghost_inv_at_mods_def, tstore_def, ptr_covers_def,
       return_buf_ptr_def, lookup_var_def, allocas_from_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem selected_lock_ghost[local]:
  dead_lo_ok_mods (H:(bool # 256 word # type_value) list # num list) D lo ce p /\ storage_locks_separated (FST H) (SND H) /\
  MEM key (SND H) /\ key < dimword (:256) /\
  ghost_inv_at_mods D lo d ce p es G tn s /\ local_ptrs_reserved ce pro /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at pro x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at pro x) /\
  locked.scopes = es.scopes /\
  N.t_mem = tn.t_mem /\ N.t_stor = tn.t_stor /\ N.t_trans = tn.t_trans /\ N.t_imm = tn.t_imm /\
  (!x. not_fresh_at pro x ==>
     FLOOKUP P x = FLOOKUP G x /\ op_taint N (Var x) = op_taint tn (Var x)) /\
  compile_nonreentrant_lock key T view pro = ((),a) /\
  run_inst_seq (emitted_insts pro a) s = OK u ==>
  ghost_inv_at_mods D lo d ce p locked P N (u with vs_inst_idx := LENGTH a.cs_current_insts)
Proof
  strip_tac >> drule_all_then assume_tac selected_lock_target_shape >>
  qabbrev_tac `chk = transient_lock_checked_state pro key s` >>
  `ghost_inv_at_mods D lo d ce p locked P N (chk with vs_inst_idx := LENGTH a.cs_current_insts)` by
    (irule ghost_inv_at_mods_exterior_frame >> qexistsl_tac [`G`,`es`,`s`,`pro`,`tn`] >>
     qspecl_then [`pro`,`key`,`s`] (strip_assume_tac o SIMP_RULE bool_ss [LET_THM])
       (Q.GENL [`pro`,`key`,`s`] selected_lock_checked_fields) >>
     simp[Abbr `chk`, blockPrefixEquivTheory.lookup_var_set_inst_idx]) >>
  Cases_on `view` >> gvs[] >>
  `tstore (n2w key) 1w chk with vs_inst_idx := LENGTH a.cs_current_insts =
   tstore (n2w key) 1w (chk with vs_inst_idx := LENGTH a.cs_current_insts)` by
    simp[tstore_def] >>
  pop_assum SUBST1_TAC >> irule selected_lock_ghost_tstore >> simp[] >>
  qexists_tac `H` >> simp[]
QED

Theorem selected_lock_return_frame[local]:
  pro.cs_next_var <= a.cs_next_var /\ local_ptrs_reserved ce pro /\
  ret_pc_ok ce pro s /\ return_buf_frame d ce pro s /\ return_buf_sep d ce es s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at pro x) /\
  (!x. not_fresh_at pro x ==> lookup_var x t = lookup_var x s) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  locked.scopes = es.scopes ==>
  local_ptrs_reserved ce a /\ ret_pc_ok ce a t /\ return_buf_frame d ce a t /\
  return_buf_sep d ce locked t /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x)
Proof
  strip_tac >> conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `pro` >> simp[]) >>
  conj_tac
  >- (irule stmtSimPropsTheory.ret_pc_ok_frame >> qexistsl_tac [`ce`,`s`,`pro`] >> simp[]) >>
  conj_tac
  >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl_tac [`ce`,`s`,`pro`] >> simp[]) >>
  reverse conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  irule return_buf_sep_transport >> conj_tac
  >- (rpt strip_tac >> gvs[bodySimFullTheory.return_buf_sep_def, allocas_from_def] >>
      first_assum ACCEPT_TAC) >>
  qexistsl_tac [`ce`,`es`,`s`] >> simp[] >>
  rpt strip_tac >>
  `local_region ce es.scopes t n b sz <=> local_region ce es.scopes s n b sz` by
    (irule local_region_lookup_cong >> rpt strip_tac >>
     first_x_assum irule >> metis_tac[local_ptrs_reserved_def]) >>
  fs[]
QED

Theorem selected_lock_bad_domain[local]:
  p.nonreentrant_slot = SOME key /\
  ~storage_trace_domain p st0 (es.storage_trace ++ [StorageLock key]) /\
  storage_trace_frame k ==>
  ~storage_trace_domain p st0
    (SND (ignore_bind (lock_if_nr p T view) k (es with gas_obs := tail))).storage_trace
Proof
  strip_tac >>
  `?res ee. lock_if_nr p T view (es with gas_obs := tail) = (res,ee)` by metis_tac[pairTheory.PAIR] >>
  `ee.storage_trace = es.storage_trace ++ [StorageLock key]` by
    (drule_then (qspecl_then [`view`,`es with gas_obs := tail`] mp_tac)
       selected_lock_trace >> simp[]) >>
  pure_rewrite_tac[ignore_bind_def, bind_def] >>
  qpat_assum `lock_if_nr _ _ _ _ = _` (pure_rewrite_tac o single) >>
  Cases_on `res`
  >- (simp[] >> `?r u. k ee = (r,u)` by metis_tac[pairTheory.PAIR] >>
      simp[] >> irule storage_trace_frame_preserves_bad_domain >>
      qexistsl_tac [`k`,`r`,`ee`] >> simp[]) >>
  simp[]
QED

Theorem selected_lock_landing_horizons[local]:
  (!H. dead_lo_ok_mods H (DF H) lo ce p) /\
  (!H. valid_horizon p st0 H es.storage_trace ==>
       stmt_state_rel H ctx callee ce p es s /\ immutable_frame_mods callee ce p es s /\
       storage_well_formed_on p es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce p es G tn s) /\
  p.nonreentrant_slot = SOME key /\ key < dimword (:256) /\
  lock_if_nr p T view es = (INL (),locked) /\
  lookup_storage (n2w key) (es.tStorage p.txn.target) = tload (n2w key) s /\
  compile_nonreentrant_lock key T view pro = ((),a) /\
  run_inst_seq (emitted_insts pro a) s = OK u /\ fresh_vars_wrt pro s /\
  local_ptrs_reserved ce pro /\ ret_pc_ok ce pro s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at pro x) /\
  N.t_mem = tn.t_mem /\ N.t_stor = tn.t_stor /\ N.t_trans = tn.t_trans /\ N.t_imm = tn.t_imm /\
  (!x. not_fresh_at pro x ==>
     FLOOKUP P x = FLOOKUP G x /\ op_taint N (Var x) = op_taint tn (Var x)) ==>
  !H. valid_horizon p st0 H locked.storage_trace ==>
    let at_body = u with vs_inst_idx := LENGTH a.cs_current_insts in
    stmt_state_rel H ctx callee ce p locked at_body /\
    immutable_frame_mods callee ce p locked at_body /\
    storage_well_formed_on p locked (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce p locked P N at_body
Proof
  strip_tac >> gen_tac >> strip_tac >> simp[LET_THM] >>
  `locked.storage_trace = es.storage_trace ++ [StorageLock key]` by
    (drule_then (qspecl_then [`view`,`es`] mp_tac) selected_lock_trace >>
     qpat_assum `lock_if_nr _ _ _ _ = _` (pure_rewrite_tac o single) >> simp[]) >>
  `valid_horizon p st0 H es.storage_trace /\
   storage_locks_separated (FST H) (SND H) /\ MEM key (SND H)` by
    (irule selected_lock_horizon >> simp[] >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac >- drule_all_then ACCEPT_TAC selected_lock_stmt_rel >>
  drule_then strip_assume_tac selected_lock_source_fields >>
  conj_tac
  >- (irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`es`,`s`,`pro`] >>
      drule_all selected_lock_target_fields >> simp[LET_THM]) >>
  conj_tac
  >- (irule lock_if_nr_preserves_storage_well_formed_on >>
      `regions_consistent (FST H) /\ storage_observations_ok p H locked.storage_trace` by
        (qpat_assum `valid_horizon p st0 H locked.storage_trace` mp_tac >>
         pure_rewrite_tac[valid_horizon_def] >> strip_tac >> simp[]) >>
      simp[Excl "lock_if_nr_def"] >>
      qexistsl_tac [`T`,`INL ():unit + exception`,`es`,`view`] >>
      simp[Excl "lock_if_nr_def"]) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at pro x` by
    fs[loweringPostsTheory.ret_pc_ok_def] >>
  irule selected_lock_ghost >> simp[] >>
  qexistsl_tac [`G`,`H`,`es`,`key`,`pro`,`s`,`tn`,`view`] >> simp[]
QED

(* One reached concrete cursor supplies all body-entry fields. *)
Theorem selected_lock_landing_run_mods:
  (if nr then compile_nonreentrant_lock key T view else comp_return ()) pro = ((),a) /\
  (nr ==> p.nonreentrant_slot = SOME key /\ key < dimword (:256)) /\
  fn_has_code pro a callee /\ fn_inst_ids_distinct callee /\
  (!bb. MEM bb callee.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. dead_lo_ok_mods H (DF H) lo ce p) /\
  fresh_vars_wrt pro s /\ local_ptrs_reserved ce pro /\ ret_pc_ok ce pro s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at pro x) /\
  ~block_is_terminated pro /\ return_buf_frame d ce pro s /\ return_buf_sep d ce es s /\
  alloca_history callee s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst t. frag_reachable ctx callee s fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon p st0 H es.storage_trace ==>
       stmt_state_rel H ctx callee ce p es s /\ immutable_frame_mods callee ce p es s /\
       storage_well_formed_on p es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce p es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = pro.cs_current_bb /\
  s.vs_inst_idx = LENGTH pro.cs_current_insts ==>
  (nr /\ ~storage_trace_domain p st0 (es.storage_trace ++ [StorageLock key]) /\
   !k tail. storage_trace_frame k ==>
     ~storage_trace_domain p st0
       (SND (ignore_bind (lock_if_nr p nr view) k (es with gas_obs := tail))).storage_trace) \/
  (?msg ab ee t P N.
     nr /\ ((msg = "nonreentrant lock" /\ ab = Revert_abort) \/
             (msg = "write in static context" /\ ab = ExHalt_abort)) /\
     lock_if_nr p nr view es = (INR (Error (RuntimeError msg)),ee) /\
     (!tail. lock_if_nr p nr view (es with gas_obs := tail) =
             (INR (Error (RuntimeError msg)),ee with gas_obs := tail)) /\
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG) (s,G,tn) [] (Abort ab t,P,N))) \/
  (?locked at_body P N.
     lock_if_nr p nr view es = (INL (),locked) /\
     (!tail. lock_if_nr p nr view (es with gas_obs := tail) =
             (INL (),locked with gas_obs := tail)) /\
     (nr /\ ~view ==> ~p.txn.is_static) /\
     (~nr ==> a = pro /\ locked = es /\ at_body = s /\ P = G /\ N = tn) /\
     locked.scopes = es.scopes /\ locked.immutables = es.immutables /\
     locked.accounts = es.accounts /\ locked.outcomes = es.outcomes /\
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG) (s,G,tn) [] (OK at_body,P,N)) /\
     fresh_vars_wrt a at_body /\ local_ptrs_reserved ce a /\ ret_pc_ok ce a at_body /\
     (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
     ~block_is_terminated a /\ return_buf_frame d ce a at_body /\
     return_buf_sep d ce locked at_body /\ alloca_history callee at_body /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp at_body) /\
     (!fn inst t. frag_reachable ctx callee at_body fn inst t ==> dalloca_fmp_headroom inst t) /\
     (!H. valid_horizon p st0 H locked.storage_trace ==>
       stmt_state_rel H ctx callee ce p locked at_body /\
       immutable_frame_mods callee ce p locked at_body /\
       storage_well_formed_on p locked (FST H) /\
       ghost_inv_at_mods (DF H) lo d ce p locked P N at_body) /\
     ~at_body.vs_halted /\ at_body.vs_current_bb = a.cs_current_bb /\
     at_body.vs_inst_idx = LENGTH a.cs_current_insts /\
     (!x. not_fresh_at pro x ==> lookup_var x at_body = lookup_var x s /\
        FLOOKUP P x = FLOOKUP G x /\ op_taint N (Var x) = op_taint tn (Var x)) /\
     at_body.vs_memory = s.vs_memory /\ at_body.vs_allocas = s.vs_allocas /\
     at_body.vs_alloca_next = s.vs_alloca_next /\
     N.t_mem = tn.t_mem /\ N.t_stor = tn.t_stor /\ N.t_trans = tn.t_trans /\ N.t_imm = tn.t_imm)
Proof
  strip_tac >> Cases_on `nr`
  >- suspend "lock" >>
  gvs[comp_return_def, lock_if_nr_def, return_def] >>
  conj_tac >- (gen_tac >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Resume selected_lock_landing_run_mods[lock]:
  fs[Excl "lock_if_nr_def"] >>
  reverse (Cases_on `storage_trace_domain p st0 (es.storage_trace ++ [StorageLock key])`)
  >- (disj1_tac >> simp[Excl "lock_if_nr_def"] >>
      rpt gen_tac >> disch_tac >> irule selected_lock_bad_domain >> simp[]) >>
  disj2_tac >>
  fs[storage_trace_domain_def, Excl "lock_if_nr_def"] >>
  drule_then strip_assume_tac selected_lock_horizon >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  drule_then assume_tac stmt_state_rel_state_rel >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_all_then strip_assume_tac selected_lock_read >>
  `!b. (n2w key,b) NOTIN tn.t_trans` by
    (irule selected_lock_clean >> simp[] >>
     qmatch_asmsub_rename_tac `valid_horizon _ _ H _` >>
     qexistsl_tac [`DF H`,`H`,`ce`,`lo`,`p`,`s`] >>
     fs[ghost_inv_at_mods_def]) >>
  drule_all_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) selected_lock_path >>
  drule_all_then strip_assume_tac selected_lock_run
  >- suspend "acquired"
  >- suspend "reverted" >> suspend "static"
QED

Resume selected_lock_landing_run_mods[acquired]:
  qpat_assum `!u. run_inst_seq _ _ = OK u ==> _` (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac selected_lock_code >>
  drule_all_then strip_assume_tac (SIMP_RULE bool_ss [LET_THM] selected_lock_target_fields) >>
  drule_then strip_assume_tac selected_lock_source_fields >>
  drule_all_then strip_assume_tac selected_lock_source_success >>
  rename1 `lock_if_nr p T view es = (INL (),locked)` >>
  qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) _ [] (OK _,_,_)`
    (qspec_then `ARB:dead` assume_tac) >>
  drule_all_then assume_tac body_full_path_alloca_history >>
  `!fn inst t. frag_reachable ctx callee (u with vs_inst_idx := LENGTH a.cs_current_insts)
                      fn inst t ==> dalloca_fmp_headroom inst t` by
    (rpt gen_tac >> disch_tac >> drule gas_origin_ptr_path_dalloca_fmp_headroom >>
     disch_then (qspecl_then [`fn`,`inst`,`t`] irule) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `fn` >> first_assum ACCEPT_TAC) >>
  `pro.cs_next_var <= a.cs_next_var` by simp[] >>
  drule_all_then strip_assume_tac selected_lock_return_frame >>
  disj2_tac >>
  rename1 `!D. gas_origin_ptr_path (D,_,_,_,_,_) _ [] (OK _,P,N)` >>
  qexistsl_tac [`locked`,`u with vs_inst_idx := LENGTH a.cs_current_insts`,`P`,`N`] >>
  simp[Excl "lock_if_nr_def"] >>
  conj_tac >- (gen_tac >> irule lock_if_nr_with_gas_obs >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (`allocas_below_fmp u <=> allocas_below_fmp s` by
        (irule allocasBelowFmpUpdatesPropsTheory.allocas_below_fmp_fields >> fs[]) >>
      pop_assum (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >>
  irule (SIMP_RULE bool_ss [LET_THM] selected_lock_landing_horizons) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`es`,`key`,`pro`,`s`,`st0`,`tn`,`view`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume selected_lock_landing_run_mods[reverted]:
  qpat_assum `!ab u. run_inst_seq _ _ = Abort ab u ==> _` (drule_then strip_assume_tac) >>
  rename1 `!D. gas_origin_ptr_path (D,_,_,_,_,_) _ [] (Abort Revert_abort t,P,N)` >>
  rename1 `lock_if_nr _ _ _ _ = (INR _,ee)` >>
  disj1_tac >> qexistsl_tac [`"nonreentrant lock"`,`Revert_abort`,`ee`,`t`,`P`,`N`] >>
  simp[Excl "lock_if_nr_def"] >> gen_tac >> irule lock_if_nr_with_gas_obs >> first_assum ACCEPT_TAC
QED

Resume selected_lock_landing_run_mods[static]:
  qpat_assum `!ab u. run_inst_seq _ _ = Abort ab u ==> _` (drule_then strip_assume_tac) >>
  rename1 `!D. gas_origin_ptr_path (D,_,_,_,_,_) _ [] (Abort ExHalt_abort t,P,N)` >>
  rename1 `lock_if_nr _ _ _ _ = (INR _,ee)` >>
  disj1_tac >> qexistsl_tac [`"write in static context"`,`ExHalt_abort`,`ee`,`t`,`P`,`N`] >>
  simp[Excl "lock_if_nr_def"] >> gen_tac >> irule lock_if_nr_with_gas_obs >> first_assum ACCEPT_TAC
QED

Finalise selected_lock_landing_run_mods
