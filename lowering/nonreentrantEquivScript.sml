(* TOP-LEVEL: source/target lock, release and rejection simulation.
   The slot is explicit: callers must establish source/compiled slot agreement. *)
Theory nonreentrantEquiv
Ancestors
  transientLockProps transientLockFrameProps
  emitHelperProps exprLoweringProps context compileEnv
  venomExecSemantics venomState
  vyperInterpreter vyperState vyperContext vyperValue
  vfmExecution vfmState
Libs
  proofAuditLib

Theorem acquire_nonreentrant_lock_execution:
  acquire_nonreentrant_lock addr key is_view vs =
    if lookup_storage (n2w key) (vs.tStorage addr) = 1w then
      (INR (vyperState$Error (RuntimeError "nonreentrant lock")),vs)
    else
      (INL (), if is_view then vs else
        vs with tStorage :=
          (addr =+ update_storage (n2w key) 1w (vs.tStorage addr)) vs.tStorage)
Proof
  Cases_on `is_view` >>
  Cases_on `lookup_storage (n2w key) (vs.tStorage addr) = 1w` >>
  simp[acquire_nonreentrant_lock_def, vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, COND_RATOR,
       lookup_transient_storage_def, update_transient_storage_def,
       evaluation_state_component_equality]
QED

Theorem release_nonreentrant_lock_execution:
  release_nonreentrant_lock addr key vs =
    (INL (), vs with tStorage :=
      (addr =+ update_storage (n2w key) 0w (vs.tStorage addr)) vs.tStorage)
Proof
  simp[release_nonreentrant_lock_def, vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       lookup_transient_storage_def, update_transient_storage_def,
       evaluation_state_component_equality]
QED

Theorem state_rel_transient_lookup:
  state_rel func cenv cx vs ss ==>
  lookup_storage key (vs.tStorage cx.txn.target) = tload key ss
Proof
  simp[state_rel_def, transient_rel_def, tload_def]
QED

Theorem state_rel_transient_update:
  state_rel func cenv cx vs ss ==>
  state_rel func cenv cx
    (vs with tStorage :=
      (cx.txn.target =+ update_storage key value (vs.tStorage cx.txn.target))
        vs.tStorage)
    (tstore key value ss)
Proof
  rw[state_rel_def, local_ptrs_rel_tstore, storage_rel_def,
     transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def,
     call_ctx_rel_def, contract_storage_def, contract_transient_def] >>
  gvs[tstore_def, combinTheory.APPLY_UPDATE_THM] >>
  first_x_assum (drule_all_then strip_assume_tac) >> simp[]
QED

(* Unlike the transient write, the scratch writes need freshness: state_rel
   now includes the live local pointer registers. *)
Theorem state_rel_transient_lock_checked_state:
  state_rel func cenv cx vs ss /\ fresh_vars_wrt st ss ==>
  state_rel func cenv cx vs (transient_lock_checked_state st key ss)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv vs.scopes
     (transient_lock_checked_state st key ss)` by
    (irule transient_lock_checked_local_ptrs >> fs[state_rel_def]) >>
  irule state_rel_frame >> simp[] >> qexistsl_tac [`vs`, `ss`] >>
  simp[transient_lock_checked_state_def, update_var_def]
QED

Theorem compile_nonreentrant_lock_source_correct:
  state_rel func cenv cx vs ss /\ fresh_vars_wrt st ss /\
  compile_nonreentrant_lock key T is_view st = ((),st') /\
  tload (n2w key) ss <> 1w ==>
  ?vs' ss'.
    acquire_nonreentrant_lock cx.txn.target key is_view vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel func cenv cx vs' ss'
Proof
  strip_tac >>
  drule_all state_rel_transient_lookup >> strip_tac >>
  drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  `state_rel func cenv cx vs (transient_lock_checked_state st key ss)` by
    (irule state_rel_transient_lock_checked_state >> simp[]) >>
  Cases_on `is_view` >>
  simp[acquire_nonreentrant_lock_execution, transient_lock_code_execution] >>
  irule state_rel_transient_update >> simp[]
QED

Theorem compile_nonreentrant_lock_source_revert:
  state_rel func cenv cx vs ss /\
  compile_nonreentrant_lock key T is_view st = ((),st') /\
  tload (n2w key) ss = 1w ==>
  acquire_nonreentrant_lock cx.txn.target key is_view vs =
    (INR (vyperState$Error (RuntimeError "nonreentrant lock")),vs) /\
  ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  strip_tac >>
  drule_all state_rel_transient_lookup >> strip_tac >>
  conj_tac
  >- simp[acquire_nonreentrant_lock_execution] >>
  drule_all compile_nonreentrant_lock_transient_revert >> simp[]
QED

Theorem compile_nonreentrant_unlock_source_correct:
  state_rel func cenv cx vs ss /\
  compile_nonreentrant_unlock key T is_view st = ((),st') ==>
  ?vs' ss'.
    (if is_view then return () else
       release_nonreentrant_lock cx.txn.target key) vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel func cenv cx vs' ss'
Proof
  Cases_on `is_view` >> strip_tac
  >- gvs[compile_nonreentrant_unlock_transient_view, emitted_insts_def,
         run_inst_seq_def, vyperStateTheory.return_def] >>
  drule compile_nonreentrant_unlock_transient_correct >> strip_tac >>
  simp[release_nonreentrant_lock_execution] >>
  irule state_rel_transient_update >> simp[]
QED

val () = proofAuditLib.check_theory "nonreentrantEquiv";
