(* Source invariants across the reserved transient lock slot. *)
Theory bodyIntCallNRSourceInv
Ancestors
  exprSimHypsDefs bodyStorageCases nonreentrantEquiv
  vyperInterpreter vyperState vyperTypeInvariants
  vyperTypeEvalStoragePreservation vyperTypeStoragePreservation

Theorem intcall_lock_source_frame:
  lock_if_nr cx nr view es = (res,ee) ==>
  ee = es with tStorage := ee.tStorage
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[raise_def, ignore_bind_def, bind_def, acquire_nonreentrant_lock_eq,
       check_not_static_def, assert_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs(), return_def, raise_def,
                           evaluation_state_component_equality] >>
  gvs[COND_RATOR, AllCaseEqs(), return_def, check_def, assert_def, raise_def]
QED

Theorem intcall_unlock_source_frame:
  unlock_if_nr cx nr view es = (res,ee) ==>
  ee = es with tStorage := ee.tStorage
Proof
  Cases_on `nr` >> Cases_on `view` >>
  simp[unlock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[return_def, release_nonreentrant_lock_eq] >>
  rpt strip_tac >> gvs[evaluation_state_component_equality]
QED

Theorem intcall_lock_expr_sim_inv:
  expr_sim_inv ce cx env es /\
  lock_if_nr cx nr view es = (INL (),ee) ==>
  expr_sim_inv ce cx env ee
Proof
  strip_tac >>
  `ee = es with tStorage := ee.tStorage` by
    (irule intcall_lock_source_frame >> metis_tac[]) >>
  `contract_storage_well_formed cx ee /\ IS_SOME ee.outcomes /\
   oracle_storage_ok cx ee` by
    (irule body_intcall_lock_oracle_entry >>
     gvs[expr_sim_inv_def] >> metis_tac[]) >>
  gvs[evaluation_state_component_equality] >>
  gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
      env_immutables_consistent_def, state_well_typed_def] >>
  metis_tac[]
QED

Theorem intcall_unlock_expr_sim_inv:
  expr_sim_inv ce cx env es /\
  unlock_if_nr cx nr view es = (INL (),ee) ==>
  expr_sim_inv ce cx env ee
Proof
  strip_tac >>
  `ee = es with tStorage := ee.tStorage` by
    (irule intcall_unlock_source_frame >> metis_tac[]) >>
  `contract_storage_well_formed cx ee` by
    (Cases_on `nr` >> Cases_on `view` >>
     gvs[unlock_if_nr_def, return_def, expr_sim_inv_def] >>
     Cases_on `cx.nonreentrant_slot` >> gvs[return_def, expr_sim_inv_def] >>
     irule release_nonreentrant_lock_preserves_contract_storage_well_formed >>
     gvs[expr_sim_inv_def] >> metis_tac[]) >>
  gvs[evaluation_state_component_equality] >>
  gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
      env_immutables_consistent_def, state_well_typed_def,
      oracle_storage_ok_payload] >> metis_tac[]
QED
