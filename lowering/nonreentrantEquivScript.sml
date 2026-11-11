(* TOP-LEVEL: source/target lock, release and rejection simulation.
   The slot is explicit: callers must establish source/compiled slot agreement. *)
Theory nonreentrantEquiv
Ancestors
  loweringStateRelDefs transientLockProps transientLockFrameProps
  accountsRelProps vyperStorageLayoutSafety
  emitHelperProps exprLoweringProps context compileEnv
  venomExecSemantics venomState
  vyperInterpreter vyperState vyperContext vyperValue
  vfmExecution vfmState

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
  state_rel func cenv cx vs ss /\
  storage_read_live cx T (vs.tStorage cx.txn.target) key
    (BaseTV (UintT 256)) ==>
  lookup_storage key (vs.tStorage cx.txn.target) = tload key ss
Proof
  strip_tac >>
  `storage_agree (storage_dead cx T (vs.tStorage cx.txn.target))
     (vs.tStorage cx.txn.target) (contract_transient ss)` by
    gvs[state_rel_def, transient_rel_def] >>
  `0 < type_slot_size (BaseTV (UintT 256))` by
    simp[vyperValueTheory.type_slot_size_def] >>
  drule_all storage_agree_read_head >>
  simp[vyperValueTheory.type_slot_size_def, tload_def, contract_transient_def]
QED

Theorem state_rel_transient_update:
  state_rel func cenv cx vs ss /\
  (!j b. storage_dead cx T (vs.tStorage cx.txn.target) j b /\
         j <> w2n key ==>
         storage_dead cx T
           (update_storage key value (vs.tStorage cx.txn.target)) j b) ==>
  state_rel func cenv cx
    (vs with tStorage :=
      (cx.txn.target =+ update_storage key value (vs.tStorage cx.txn.target))
        vs.tStorage)
    (tstore key value ss)
Proof
  strip_tac >>
  `transient_agree cx vs.tStorage ss.vs_transient` by
    gvs[state_rel_def, accounts_rel_def] >>
  drule_all transient_agree_update >> strip_tac >>
  `storage_agree
     (storage_dead cx T (update_storage key value (vs.tStorage cx.txn.target)))
     (update_storage key value (vs.tStorage cx.txn.target))
     (update_storage key value (ss.vs_transient cx.txn.target))` by
    (irule storage_agree_update >>
     qexists_tac `storage_dead cx T (vs.tStorage cx.txn.target)` >>
     gvs[state_rel_def, transient_rel_def, contract_transient_def,
         call_ctx_rel_def]) >>
  gvs[state_rel_def, local_ptrs_rel_tstore, storage_rel_def,
      transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def,
      call_ctx_rel_def, contract_storage_def, contract_transient_def,
      tstore_def, combinTheory.APPLY_UPDATE_THM] >>
  first_assum ACCEPT_TAC
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
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor vs
     (transient_lock_checked_state st key ss)` by
    (gvs[state_rel_def, immutables_rel_def,
         transient_lock_checked_state_def, update_var_def] >>
     first_assum ACCEPT_TAC) >>
  irule state_rel_frame >> simp[] >> qexistsl_tac [`vs`, `ss`] >>
  simp[transient_lock_checked_state_def, update_var_def]
QED

Theorem compile_nonreentrant_lock_source_correct:
  nonreentrant_slot_separated cx /\ cx.nonreentrant_slot = SOME key /\
  state_rel func cenv cx vs ss /\ fresh_vars_wrt st ss /\
  compile_nonreentrant_lock key T is_view st = ((),st') /\
  tload (n2w key) ss <> 1w ==>
  ?vs' ss'.
    acquire_nonreentrant_lock cx.txn.target key is_view vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel func cenv cx vs' ss'
Proof
  strip_tac >>
  `~ss.vs_call_ctx.cc_static` by fs[state_rel_def] >>
  `storage_read_live cx T (vs.tStorage cx.txn.target) (n2w key)
     (BaseTV (UintT 256))` by
    (irule nonreentrant_slot_read_live >> simp[]) >>
  drule_all state_rel_transient_lookup >> strip_tac >>
  drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  `state_rel func cenv cx vs (transient_lock_checked_state st key ss)` by
    (irule state_rel_transient_lock_checked_state >> simp[]) >>
  Cases_on `is_view` >>
  simp[acquire_nonreentrant_lock_execution, transient_lock_code_execution] >>
  irule state_rel_transient_update >> simp[] >>
  rpt strip_tac >> irule nonreentrant_slot_dead_preserved >> simp[]
QED

Theorem compile_nonreentrant_lock_source_revert:
  nonreentrant_slot_separated cx /\ cx.nonreentrant_slot = SOME key /\
  state_rel func cenv cx vs ss /\
  compile_nonreentrant_lock key T is_view st = ((),st') /\
  tload (n2w key) ss = 1w ==>
  acquire_nonreentrant_lock cx.txn.target key is_view vs =
    (INR (vyperState$Error (RuntimeError "nonreentrant lock")),vs) /\
  ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  strip_tac >>
  `storage_read_live cx T (vs.tStorage cx.txn.target) (n2w key)
     (BaseTV (UintT 256))` by
    (irule nonreentrant_slot_read_live >> simp[]) >>
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
  `~ss.vs_call_ctx.cc_static` by fs[state_rel_def] >>
  drule_all compile_nonreentrant_unlock_transient_correct >> strip_tac >>
  simp[release_nonreentrant_lock_execution] >>
  irule state_rel_transient_update >> simp[] >>
  metis_tac[storage_dead_update_zero]
QED
