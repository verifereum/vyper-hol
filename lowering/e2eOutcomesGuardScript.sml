(* Closed-world storage invariants for a reentered frame. *)
Theory e2eOutcomesGuard
Ancestors
  e2eRequestCutDefs e2eDefs vfmAccountFrame vyperStorageFootprint
  vyperInterpreter vyperState vyperStorageBackend vfmState

Triviality guard_closed_world_inherit:
  vyper_closed_world fin policy tops runtime_bc am tx H es /\
  run_call_reaches es e /\ LENGTH es.contexts <= LENGTH e.contexts /\
  am_e.sources = am.sources /\ am_e.layouts = am.layouts /\
  tx_e.target = tx.target /\
  world_rel am_e tx_e e /\
  storage_well_formed_on
    (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
    (empty_state with <|accounts := e.rollback.accounts;
                       tStorage := e.rollback.tStorage|>) (FST H) /\
  horizon_covers H am_e tx_e (MAP SND (call_trace e)) /\
  ~account_empty (lookup_account tx_e.target e.originalAccounts) /\
  (!gobs. ~source_exempt tops
    (call_external (SOME (MAP SND (call_trace e))) gobs am_e tx_e)) ==>
  vyper_closed_world fin policy tops runtime_bc am_e tx_e H e
Proof
  strip_tac >>
  `!a. (accounts_after_transfer tx_e am_e.accounts a).storage =
       (am_e.accounts a).storage` by
    (gen_tac >> rw[accounts_after_transfer_def, lookup_account_def,
                  update_account_def, combinTheory.APPLY_UPDATE_THM] >>
     rpt IF_CASES_TAC >> simp[]) >>
  `storage_well_formed_on
    (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
    (initial_state am_e []) (FST H)` by
    (qpat_x_assum `world_rel _ _ _`
       (strip_assume_tac o REWRITE_RULE [world_rel_def]) >>
     qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     simp[storage_well_formed_on_def, boolTheory.FORALL_BOOL,
          get_storage_def, initial_state_def]) >>
  fs[vyper_closed_world_def] >> rpt strip_tac >>
  rename1 `step s = (INL u, child)` >>
  `run_call_reaches es s` by
    (irule run_call_reaches_trans >> qexists_tac `e` >> simp[]) >>
  qpat_x_assum `!s child. run_call_reaches es s /\ _ ==> _`
    (qspecl_then [`s`, `child`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> simp[]
QED
