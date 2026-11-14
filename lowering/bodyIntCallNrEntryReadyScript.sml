(* The actual guarded entry: transport of runtime resources through its lock. *)
Theory bodyIntCallNrEntryReady
Ancestors
  bodyIntCallNrEntrySemantic bodyIntCallNrEntryResources bodyIntCallNrLockResources
  bodyIntCallNonreentrantLock nonreentrantEntry fragExecMem moduleLoweringProps
  exprLoweringProps loweringStateRelDefs venomState finite_map words
  transientLockFrameProps transientLockProps nonreentrantEquiv vyperInterpreter
  vyperState fragGasSeq fragGasSeqAbort venomInst emitHelper

Theorem internal_entry_lock_runtime_resources:
  fmp_room ctx func s /\ immutable_base_zero ce s /\
  vars_pc_only (if view then s else tstore (n2w key) 1w s) u /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s) /\
  (!op. ce.ce_imm_alloca = SOME op ==> ?x. op = Var x /\ not_fresh_at st x) ==>
  fmp_room ctx func u /\ immutable_base_zero ce u
Proof
  strip_tac >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_fmp = s.vs_fmp /\ u.vs_labels = s.vs_labels` by
    (fs[vars_pc_only_def] >> Cases_on `view` >>
     gvs[tstore_def, venom_state_component_equality]) >>
  conj_tac
  >- (fs[fmp_room_def, pending_alloca_size_def] >> metis_tac[]) >>
  irule immutable_base_zero_frame >> qexists_tac `s` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `Var x` mp_tac) >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem internal_entry_lock_success_resources:
  compile_nonreentrant_lock key T view st = ((),st') /\
  cx.nonreentrant_slot = SOME key /\ nonreentrant_slot_separated cx /\
  stmt_state_rel ctx func ce cx es s /\ fresh_vars_wrt st s /\
  tload (n2w key) s <> 1w /\
  (!op. ce.ce_imm_alloca = SOME op ==> ?x. op = Var x /\ not_fresh_at st x) ==>
  ?locked u.
    run_inst_seq (emitted_insts st st') s = OK u /\
    lock_if_nr cx T view es = (INL (),locked) /\
    state_rel func ce cx locked u /\ fresh_vars_wrt st' u /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    fmp_room ctx func u /\ immutable_base_zero ce u /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op u = SOME w)
Proof
  strip_tac >>
  `state_rel func ce cx es s /\ local_ptrs_rel func ce es.scopes s /\
   ~s.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all compile_nonreentrant_lock_source_correct >> strip_tac >>
  drule_all compile_nonreentrant_lock_transient_frame >> strip_tac >>
  gvs[] >> rename1 `state_rel func ce cx locked u` >>
  drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  `vars_pc_only (if view then s else tstore (n2w key) 1w s) u` by
    (gvs[transient_lock_code_execution] >> Cases_on `view` >>
     gvs[vars_pc_only_def, transient_lock_checked_state_def,
         update_var_def, tstore_def]) >>
  `!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s` by
    (gvs[transient_lock_code_execution] >> Cases_on `view` >>
     gvs[transient_lock_checked_state_def, lookup_var_def, update_var_def,
         tstore_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> gvs[not_fresh_at_def]) >>
  `fmp_room ctx func s /\ immutable_base_zero ce s /\ ~cx.txn.is_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all internal_entry_lock_runtime_resources >> strip_tac >>
  qexists_tac `locked` >> simp[] >>
  fs[lock_if_nr_def, ignore_bind_def, bind_def, check_not_static_def,
     check_def, assert_def, return_def, raise_def] >>
  Cases_on `view` >>
  gvs[assert_def, return_def, vars_pc_only_def, tstore_def,
      venom_state_component_equality]
QED

Theorem internal_entry_lock_failure_resources:
  compile_nonreentrant_lock key T view st = ((),st') /\
  cx.nonreentrant_slot = SOME key /\ nonreentrant_slot_separated cx /\
  state_rel func ce cx es s /\ tload (n2w key) s = 1w ==>
  lock_if_nr cx T view es =
    (INR (vyperState$Error (RuntimeError "nonreentrant lock")),es) /\
  ?u. run_inst_seq (emitted_insts st st') s = Abort Revert_abort u /\
    u.vs_returndata = [] /\ u.vs_memory = s.vs_memory /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all compile_nonreentrant_lock_source_revert >> strip_tac >>
  drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  conj_tac
  >- (`~cx.txn.is_static` by fs[state_rel_def] >>
      fs[lock_if_nr_def, ignore_bind_def, bind_def]) >>
  gvs[transient_lock_code_execution] >>
  simp[revert_state_def, set_returndata_def, transient_lock_checked_state_def,
       update_var_def]
QED

Theorem internal_entry_lock_success_path:
  compile_nonreentrant_lock key T view st = ((),st') /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts st st') s = OK u ==>
  gas_path ctx func s 0
    (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st')))
Proof
  strip_tac >> drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by
    (Cases_on `view` >> simp[transient_lock_code_def, mk_inst_def, is_terminator_def]) >>
  drule_all tuple_run_inst_seq_gas_path >>
  simp[transient_lock_code_def, mk_inst_def] >>
  Cases_on `view` >> simp[transient_lock_code_def, mk_inst_def]
QED

Theorem internal_entry_lock_failure_path:
  compile_nonreentrant_lock key T view st = ((),st') /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts st st') s = Abort a u ==>
  ?j. gas_marked_path F ctx func s 0 (Abort a (u with vs_inst_idx := j))
Proof
  strip_tac >> drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  irule run_inst_seq_abort_zero_path >>
  simp[] >> qexists_tac `emitted_insts st st'` >> simp[] >>
  Cases_on `view` >> simp[transient_lock_code_def, mk_inst_def, is_terminator_def]
QED
