(*
 * The finite storage invariant across a whole external call.
 *
 * storage_well_formed_on cx st L reads only the contract's two storage
 * backends (get_storage cx st T and F), so it depends on cx only through
 * cx.txn.target.  A call that fails returns its input machine; one that
 * succeeds or halts runs the call-value transfer (balances only), the
 * defaults and the body (eval_storage_well_formed_on_mutual, given the
 * observed horizon H), the lock and scope cleanup, the machine round trip
 * through abstract_machine_from_state, and the commit of pending deletions
 * (a deleted account's storage reads zero, in range at every root).
 *
 * TOP-LEVEL:
 *   checked_call_external_preserves_storage_well_formed_on
 *)
Theory vyperCallStorageFootprint
Ancestors
  vyperFiniteStoragePreservation vyperStorageFootprint vyperStorageBackend
  vyperTypeExternalCallMachine vyperTypeContractSoundness vyperInterpreter
  vyperState vyperTypeExternalDefaults vyperTypeExprSoundness vyperStorageTrace
  vyperReadOnlyEval vyperReadOnlySyntax vyperTypeContractGetter
  vyperMachineFrame vyperReadOnlyBranches vyperCallOutcomeFrame

val _ = Parse.hide "body";

Theorem eval_external_defaults_preserves_storage_well_formed_on[local]:
  well_typed_exprs env es /\
  runtime_consistent env cx (st with scopes := [FEMPTY]) /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) /\
  storage_observations_ok cx H rt.storage_trace /\
  eval_external_defaults cx es st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H)
Proof
  simp[eval_external_defaults_run] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  simp[] >> strip_tac >> gvs[] >>
  `storage_well_formed_on cx (st with scopes := [FEMPTY]) (FST H)` by
    (fs[storage_well_formed_on_def] >> rpt strip_tac >>
     Cases_on `b` >> gvs[get_storage_def] >>
     metis_tac[get_storage_def]) >>
  drule_all (cj 6 eval_storage_well_formed_on_mutual) >>
  (fs[storage_well_formed_on_def] >> rpt strip_tac >>
     Cases_on `b` >> gvs[get_storage_def] >>
     metis_tac[get_storage_def])
QED

(* Explicit selected-entry storage boundary. *)
Theorem explicit_current_body_storage[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP FST args) /\
  body_entry_ready art cx scope st /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H rt.storage_trace /\
  eval_stmts cx body st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H)
Proof
  strip_tac >>
  drule_all checked_explicit_external_body_setup_current >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (gvs[] >> drule_all checked_explicit_external_body_call_evaluation_safe >> simp[]) >>
  `runtime_consistent env_body cx st` by simp[runtime_consistent_def] >>
  drule_all (cj 2 eval_storage_well_formed_on_mutual) >> simp[]
QED

Theorem explicit_lock_observed:
  lock_if_nr cx nr is_view st = (r,u) /\
  nr /\ cx.nonreentrant_slot = SOME slot ==>
  MEM (StorageLock slot) u.storage_trace
Proof
  strip_tac >> Cases_on `is_view` >>
  gvs[lock_if_nr_def, vyperTypeEvalStoragePreservationTheory.acquire_nonreentrant_lock_eq,
      bind_def, ignore_bind_def, return_def, raise_def,
      check_not_static_def, assert_def, check_def, AllCaseEqs(), listTheory.MEM_APPEND]
QED

Theorem explicit_locked_body_storage[local]:
  (!cx nr is_view st r u H obs.
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\ storage_observations_ok cx H obs /\
    (!slot. nr /\ cx.nonreentrant_slot = SOME slot ==> MEM (StorageLock slot) obs) /\
    lock_if_nr cx nr is_view st = (r,u) ==>
    storage_well_formed_on cx u (FST H)) ==>
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  body_entry_ready art cx scope st /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H rt.storage_trace /\
  (do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od) st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H) /\
  (!slot. nr /\ cx.nonreentrant_slot = SOME slot ==>
    MEM (StorageLock slot) rt.storage_trace)
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  pure_rewrite_tac[ignore_bind_def, bind_def] >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) st` >> Cases_on `q` >>
  pure_asm_rewrite_tac[pairTheory.pair_case_def, sumTheory.sum_case_def] >>
  BETA_TAC >> pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC
  >- (strip_tac >>
      qpat_assum `cx = _` (fn th =>
        qpat_x_assum `eval_stmts _ _ _ = _` (assume_tac o REWRITE_RULE [GSYM th])) >>
      `?tail. rt.storage_trace = r.storage_trace ++ tail` by
        (`storage_trace_frame (eval_stmts cx body)` by
           simp[cj 2 evaluate_storage_trace_frame] >>
         drule_all storage_trace_frame_prefix >> simp[]) >>
      `!slot. nr /\ cx.nonreentrant_slot = SOME slot ==>
         MEM (StorageLock slot) rt.storage_trace` by
        (rpt strip_tac >> drule_all explicit_lock_observed >>
         simp[listTheory.MEM_APPEND]) >>
      `storage_well_formed_on cx r (FST H)` by
        (first_assum (drule_at (Pat `lock_if_nr`)) >>
         disch_then irule >> metis_tac[]) >>
      `r.scopes = st.scopes /\ r.immutables = st.immutables /\ r.accounts = st.accounts` by
        (qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
         simp[lock_if_nr_def, is_view_mut_def] >>
         metis_tac[call_lock_action_frame_c53]) >>
      `body_entry_ready art cx scope r` by
        gvs[body_entry_ready_def, vyperTypeInvariantsTheory.state_well_typed_def] >>
      drule_all checked_external_declaration_static >> strip_tac >>
      conj_tac >- (drule_all explicit_current_body_storage >> simp[]) >> simp[]) >>
  strip_tac >> gvs[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  `!slot. nr /\ (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot = SOME slot ==>
    MEM (StorageLock slot) r.storage_trace` by
    (rpt strip_tac >> drule_all explicit_lock_observed >> simp[]) >>
  conj_tac >- (first_assum (drule_at (Pat `lock_if_nr`)) >> disch_then irule >> metis_tac[]) >>
  simp[]
QED

Theorem explicit_defaults_body_storage[local]:
  (!cx nr is_view st r u H obs.
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\ storage_observations_ok cx H obs /\
    (!slot. nr /\ cx.nonreentrant_slot = SOME slot ==> MEM (StorageLock slot) obs) /\
    lock_if_nr cx nr is_view st = (r,u) ==>
    storage_well_formed_on cx u (FST H)) ==>
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\ state_well_typed st /\ accounts_well_typed st.accounts /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st.immutables /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H rt.storage_trace /\
  (do dvs <- eval_external_defaults cx (DROP k dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME scope => do set_scopes [scope]; lock_if_nr cx nr (is_view_mut mut);
                         eval_stmts cx body od
   od) st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H)
Proof
  strip_tac >> strip_tac >>
  drule_all checked_external_empty_frame_ready >> strip_tac >>
  `runtime_consistent (artifact_env art mods src) cx (st with scopes := [FEMPTY])` by
    simp[runtime_consistent_def] >>
  drule_all checked_external_suffix_static >>
  disch_then (qspec_then `k` strip_assume_tac) >>
  qpat_x_assum `bind _ _ st = _` mp_tac >> pure_rewrite_tac[bind_def] >>
  Cases_on `eval_external_defaults cx (DROP k dflts) st` >> Cases_on `q` >>
  pure_asm_rewrite_tac[pairTheory.pair_case_def, sumTheory.sum_case_def] >>
  BETA_TAC >> pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC
  >- (rename1 `eval_external_defaults cx (DROP k dflts) st = (INL dvs,s2)` >>
      Cases_on `bind_arguments (type_env_all_modules mods) args (vals ++ dvs)` >>
      simp_tac bool_ss [raise_def]
      >- (strip_tac >> gvs[raise_def] >>
          drule_all eval_external_defaults_preserves_storage_well_formed_on >>
          simp[runtime_consistent_def]) >>
      rename1 `bind_arguments _ _ _ = SOME scope` >>
      pure_rewrite_tac[ignore_bind_def, bind_def, set_scopes_def, return_def] >>
      BETA_TAC >> pure_rewrite_tac[pairTheory.pair_case_def, sumTheory.sum_case_def] >>
      BETA_TAC >> strip_tac >>
      suspend "bound") >>
  strip_tac >> gvs[] >>
  drule_all eval_external_defaults_preserves_storage_well_formed_on >>
  simp[runtime_consistent_def]
QED

Resume explicit_defaults_body_storage[bound]:
  qpat_assum `cx = _` (fn th =>
    qpat_x_assum `option_CASE _ _ _ _ = _`
      (mp_tac o REWRITE_RULE [GSYM th])) >>
  simp_tac bool_ss [optionTheory.option_case_def, ignore_bind_def, bind_def,
                   set_scopes_def, return_def] >> strip_tac >>
  `(do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od)
     (s2 with scopes := [scope]) = (res,rt)` by
    gvs[bind_def, ignore_bind_def] >>
  `storage_trace_frame (do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od)` by
    (irule storage_trace_frame_ignore_bind >>
     simp[cj 1 storage_trace_frame_optional_locks, cj 2 evaluate_storage_trace_frame]) >>
  `?tail. rt.storage_trace = s2.storage_trace ++ tail` by
    (drule_all storage_trace_frame_prefix >> simp[]) >>
  `storage_observations_ok cx H s2.storage_trace` by
    metis_tac[storage_observations_ok_append] >>
  `storage_well_formed_on cx s2 (FST H)` by
    (drule_all eval_external_defaults_preserves_storage_well_formed_on >> simp[]) >>
  `state_well_typed s2 /\ accounts_well_typed s2.accounts` by
    (drule_all eval_external_defaults_type_sound >> simp[]) >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx s2.immutables` by
    (drule_all eval_external_defaults_immutables_ready >> simp[]) >>
  `scope_well_typed scope` by metis_tac[vyperTypeBindArgumentsTheory.bind_arguments_scope_well_typed_from_success] >>
  `body_entry_ready art cx scope (s2 with scopes := [scope])` by
    gvs[body_entry_ready_def, vyperTypeInvariantsTheory.state_well_typed_def] >>
  `storage_well_formed_on cx (s2 with scopes := [scope]) (FST H)` by
    (`storage_well_formed_on cx (s2 with scopes := [scope]) (FST H) =
      storage_well_formed_on cx s2 (FST H)` by
       (irule storage_well_formed_on_backends >> simp[]) >> metis_tac[]) >>
  drule explicit_locked_body_storage >>
  disch_then (drule_all o cj 1) >> gvs[]
QED
Finalise explicit_defaults_body_storage

Theorem explicit_entry_storage[local]:
  (!mut cx st r u (H : (bool # bytes32 # type_value) list # num list). send_call_value mut cx st = (r,u) /\
    storage_well_formed_on cx st (FST H) ==> storage_well_formed_on cx u (FST H)) /\
  (!cx nr is_view st r u H obs.
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\ storage_observations_ok cx H obs /\
    (!slot. nr /\ cx.nonreentrant_slot = SOME slot ==> MEM (StorageLock slot) obs) /\
    lock_if_nr cx nr is_view st = (r,u) ==>
    storage_well_formed_on cx u (FST H)) ==>
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\ state_well_typed st /\ accounts_well_typed st.accounts /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st.immutables /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H rt.storage_trace /\
  (do send_call_value mut cx;
      dvs <- eval_external_defaults cx (DROP k dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME scope => do set_scopes [scope]; lock_if_nr cx nr (is_view_mut mut);
                         eval_stmts cx body od
   od) st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H)
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  pure_rewrite_tac[ignore_bind_def, bind_def] >>
  Cases_on `send_call_value mut cx st` >> Cases_on `q` >>
  pure_asm_rewrite_tac[pairTheory.pair_case_def, sumTheory.sum_case_def] >>
  BETA_TAC >> pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC
  >- (strip_tac >>
      `storage_well_formed_on cx r (FST H)` by
        (first_assum (drule_at (Pat `send_call_value`)) >>
         disch_then (qspec_then `H` mp_tac) >> metis_tac[]) >>
      drule_all send_call_value_state_sound_c53 >> strip_tac >>
      `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx r.immutables` by
        metis_tac[] >>
      qpat_assum `cx = _` (fn th =>
        qpat_x_assum `bind _ _ r = _` (assume_tac o REWRITE_RULE [GSYM th])) >>
      drule explicit_defaults_body_storage >>
      disch_then (drule_at (Pat `check_contract`)) >>
      disch_then (drule_all o REWRITE_RULE [ignore_bind_def]) >> gvs[]) >>
  strip_tac >> gvs[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  first_assum (drule_at (Pat `send_call_value`)) >>
         disch_then (qspec_then `H` mp_tac) >> metis_tac[]
QED

Theorem explicit_unlock_storage:
  (!cx nr view st r u H obs.
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\ storage_observations_ok cx H obs /\
    (!slot. nr /\ cx.nonreentrant_slot = SOME slot ==> MEM (StorageLock slot) obs) /\
    unlock_if_nr cx nr view st = (r,u) ==> storage_well_formed_on cx u (FST H)) ==>
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\ storage_observations_ok cx H u.storage_trace /\
  unlock_if_nr cx nr view st = (r,u) ==>
  storage_well_formed_on cx u (FST H)
Proof
  strip_tac >> strip_tac >>
  Cases_on `nr /\ ~view` >-
    (`!slot. nr /\ cx.nonreentrant_slot = SOME slot ==> MEM (StorageLock slot) u.storage_trace` by
       (rpt strip_tac >> gvs[unlock_if_nr_def,
          vyperTypeEvalStoragePreservationTheory.release_nonreentrant_lock_eq]) >>
     first_assum (drule_at (Pat `unlock_if_nr`)) >> disch_then irule >> metis_tac[]) >>
  gvs[unlock_if_nr_def, return_def]
QED

val explicit_unlocked_tac =
  qpat_x_assum `!mut cx st r u H. send_call_value _ _ _ = _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!cx nr view st r u H obs. _ /\ _ /\ _ /\ _ /\ _ /\ lock_if_nr _ _ _ _ = _ ==> _` kall_tac >>
  pop_assum mp_tac >>
  asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF, pairTheory.pair_case_def,
                        sumTheory.sum_case_def] >> strip_tac >>
  drule explicit_unlock_storage >> disch_then (drule_at (Pat `unlock_if_nr`)) >>
  disch_then (qspec_then `H` assume_tac) >> rpt (qpat_x_assum `!x. _` kall_tac) >>
  gvs[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  `?tail. r.storage_trace = sb.storage_trace ++ tail` by
    (drule_at (Pat `f st = _`) storage_trace_frame_prefix >>
     simp[storage_trace_frame_optional_locks]) >>
  qmatch_goalsub_abbrev_tac `storage_well_formed_on cx` >>
  `storage_well_formed_on cx
      (initial_state (abstract_machine_from_state am.sources am.exports am.layouts r) []) (FST H) =
    storage_well_formed_on cx r (FST H)` by
     (irule storage_well_formed_on_backends >>
      simp[initial_state_def, abstract_machine_from_state_def]) >>
  gvs[storage_observations_ok_append];

Theorem send_call_value_storage:
  send_call_value mut cx st = (r,u) /\
  storage_well_formed_on cx st (FST H) ==>
  storage_well_formed_on cx u (FST H)
Proof
  simp[send_call_value_def, ignore_bind_def, bind_def, check_def,
       assert_def, return_def, raise_def] >>
  rpt IF_CASES_TAC >> simp[] >> strip_tac >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def,
      vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def] >>
  Cases_on `mut = Payable` >>
  gvs[vyperStateTheory.assert_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def] >>
  drule_all transfer_value_preserves_storage_well_formed_on >> simp[]
QED

Theorem lock_if_nr_storage:
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H obs /\
  (!slot. nr /\ cx.nonreentrant_slot = SOME slot ==>
    MEM (StorageLock slot) obs) /\
  lock_if_nr cx nr is_view st = (r,u) ==>
  storage_well_formed_on cx u (FST H)
Proof
  reverse (Cases_on `nr`) >- (rw[lock_if_nr_def, vyperStateTheory.return_def] >> simp[]) >>
  simp[lock_if_nr_def] >>
  Cases_on `cx.nonreentrant_slot` >-
    (rw[vyperStateTheory.raise_def] >> simp[]) >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def] >>
  Cases_on `acquire_nonreentrant_lock cx.txn.target x
    (is_view \/ cx.txn.is_static) st` >>
  strip_tac >>
  `storage_well_formed_on cx r' (FST H)` by
    (drule_all acquire_lock_preserves_storage_well_formed_on >> simp[]) >>
  Cases_on `q` >> gvs[return_def] >>
  Cases_on `is_view` >> gvs[return_def, check_not_static_def,
    assert_def, check_def, raise_def]
QED

Theorem unlock_if_nr_storage:
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H obs /\
  (!slot. nr /\ cx.nonreentrant_slot = SOME slot ==>
    MEM (StorageLock slot) obs) /\
  unlock_if_nr cx nr is_view st = (r,u) ==>
  storage_well_formed_on cx u (FST H)
Proof
  reverse (Cases_on `nr /\ ~is_view`) >-
    (rw[unlock_if_nr_def, vyperStateTheory.return_def] >> simp[]) >>
  simp[unlock_if_nr_def] >>
  Cases_on `cx.nonreentrant_slot` >-
    (rw[vyperStateTheory.return_def] >> simp[]) >>
  strip_tac >>
  `MEM (StorageLock x) obs` by gvs[] >>
  gvs[] >> drule_all release_lock_preserves_storage_well_formed_on >> simp[]
QED

Theorem selected_explicit_storage[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\ module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH vals <= LENGTH args /\ LENGTH args - LENGTH vals <= LENGTH dflts /\
  call_external_function_trace orc gobs am cx nr mut ts mods args dflts vals body ret =
    (res,am',rqs,obs) /\
  (res = INL v \/ res = INR HaltException) /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_observations_ok cx H obs /\
  storage_well_formed_on cx (initial_state am []) (FST H) ==>
  storage_well_formed_on cx (initial_state am' []) (FST H)
Proof
  strip_tac >>
  `!mut cx st r u (H : (bool # bytes32 # type_value) list # num list).
    send_call_value mut cx st = (r,u) /\
    storage_well_formed_on cx st (FST H) ==> storage_well_formed_on cx u (FST H)` by
    metis_tac[send_call_value_storage] >>
  `!cx nr view st r u H obs.
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\ storage_observations_ok cx H obs /\
    (!slot. nr /\ cx.nonreentrant_slot = SOME slot ==> MEM (StorageLock slot) obs) /\
    lock_if_nr cx nr view st = (r,u) ==> storage_well_formed_on cx u (FST H)` by
    (rpt strip_tac >> drule_all lock_if_nr_storage >> simp[]) >>
  `!cx nr view st r u H obs.
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\ storage_observations_ok cx H obs /\
    (!slot. nr /\ cx.nonreentrant_slot = SOME slot ==> MEM (StorageLock slot) obs) /\
    unlock_if_nr cx nr view st = (r,u) ==> storage_well_formed_on cx u (FST H)` by
    (rpt strip_tac >> drule_all unlock_if_nr_storage >> simp[]) >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  `context_well_typed cx` by
    (qpat_x_assum `call_tx_well_typed tx` mp_tac >>
     simp[call_tx_well_typed_def, vyperTypeInvariantsTheory.context_well_typed_def,
          initial_evaluation_context_def]) >>
  `cx.in_deploy = F` by simp[initial_evaluation_context_def] >>
  qpat_x_assum `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [call_external_function_trace_def, LET_THM] >>
  qpat_assum `cx = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  `~(LENGTH vals > LENGTH args \/ LENGTH args - LENGTH vals > LENGTH dflts)` by decide_tac >>
  qpat_assum `~(LENGTH vals > LENGTH args \/ _)` (fn th => pure_rewrite_tac [th, COND_CLAUSES]) >>
  qpat_assum `cx.in_deploy = F` (fn th => pure_rewrite_tac [th, COND_CLAUSES]) >>
  simp_tac bool_ss [pairTheory.pair_case_def, pairTheory.UNCURRY_DEF, optionTheory.option_case_def] >>
  qmatch_goalsub_abbrev_tac `entry (initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|>)` >>
  qabbrev_tac `st0 = initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|>` >>
  Cases_on `entry st0` >> rename1 `entry st0 = (br,sb)` >>
  `state_well_typed st0 /\ accounts_well_typed st0.accounts` by
    (qpat_x_assum `machine_well_typed am` mp_tac >>
     simp[Abbr `st0`, initial_state_def, vyperTypeInvariantsTheory.state_well_typed_def,
          vyperTypeInitialStateTheory.machine_well_typed_def, vyperTypeInvariantsTheory.scope_well_typed_def]) >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st0.immutables` by
    (simp_tac (srw_ss()) [Abbr `st0`, initial_state_def] >>
     metis_tac[checked_contract_runtime_ready_def,
               vyperTypeContractFunctionTheory.immutables_ready_initial_evaluation_context_source]) >>
  `storage_well_formed_on cx st0 (FST H)` by
    (`storage_well_formed_on cx st0 (FST H) =
      storage_well_formed_on cx (initial_state am []) (FST H)` by
       (irule storage_well_formed_on_backends >> simp[Abbr `st0`, initial_state_def]) >>
     metis_tac[]) >>
  `storage_observations_ok cx H sb.storage_trace ==>
    storage_well_formed_on cx sb (FST H)` by
    (strip_tac >> qpat_assum `entry st0 = _` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     simp_tac bool_ss [Abbr `entry`] >> strip_tac >>
     drule explicit_entry_storage >> disch_then (drule_at (Pat `check_contract`)) >>
     disch_then drule_all >> simp[]) >>
  (Cases_on `br` >> simp_tac bool_ss []
   >- (Cases_on `unlock_if_nr cx nr (is_view_mut mut) sb` >> Cases_on `q` >>
       simp_tac bool_ss [pairTheory.pair_case_def, sumTheory.sum_case_def,
                        pairTheory.UNCURRY_DEF] >> strip_tac >>
       explicit_unlocked_tac) >>
   Cases_on `y` >> simp_tac (srw_ss()) [Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def", pairTheory.UNCURRY_DEF]
   >~ [`entry st0 = (INR (ReturnException rv),sb)`] >-
      (Cases_on `unlock_if_nr cx nr (is_view_mut mut) sb` >> Cases_on `q` >>
       simp_tac (srw_ss()) [Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def", pairTheory.UNCURRY_DEF]
       >- (Cases_on `evaluate_type (type_env_all_modules mods) ret` >>
           simp_tac (srw_ss()) [] >- (strip_tac >> metis_tac[]) >>
           rename1 `safe_cast tv rv` >> Cases_on `safe_cast tv rv` >>
           simp_tac (srw_ss()) [] >> strip_tac >> explicit_unlocked_tac) >>
       strip_tac >> metis_tac[]) >>
   strip_tac >>
    rpt (qpat_x_assum `!x. _` kall_tac) >>
    gvs[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
    qmatch_goalsub_abbrev_tac `storage_well_formed_on cx` >>
    `storage_well_formed_on cx
       (initial_state (abstract_machine_from_state am.sources am.exports am.layouts sb) []) (FST H) =
     storage_well_formed_on cx sb (FST H)` by
      (irule storage_well_formed_on_backends >>
       simp[initial_state_def, abstract_machine_from_state_def]) >> metis_tac[])
QED

(* Getters have no machine-visible effects, including on Halt.  Unlike the
   general selected-entry branch this needs no binding or trace-prefix premise. *)
Theorem selected_getter_machine_frame[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function_trace orc gobs am cx nr mut ts mods args dflts vals body ret =
    (res,am',rqs,obs) ==> am' = am
Proof
  rpt strip_tac >>
  `mut = View /\ dflts = []` by
    (Cases_on `decl` >> gvs[external_getter_tuple_def]
     >- (rename1 `VariableDecl vis _ _ _ _` >> Cases_on `vis` >>
         gvs[external_getter_tuple_def, vyperGetterTheory.getter_def,
             pairTheory.UNCURRY, AllCaseEqs()]) >>
     rename1 `HashMapDecl vis _ _ _ _ _` >> Cases_on `vis` >>
     gvs[external_getter_tuple_def, vyperGetterTheory.getter_def,
         pairTheory.UNCURRY, AllCaseEqs()]) >>
  `read_only_context mods cx` by
    (gvs[read_only_context_def, initial_evaluation_context_def,
         checked_contract_runtime_ready_def] >> metis_tac[]) >>
  `state_rel_frame machine_frame (eval_stmts cx body)` by
    (irule machine_frame_eval_stmts >> qexists `mods` >>
     metis_tac[external_getter_mutability]) >>
  `~cx.in_deploy` by simp[initial_evaluation_context_def] >>
  qpat_x_assum `cx = _` kall_tac >>
  gvs[] >>
  qpat_x_assum `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_trace_def,
       is_view_mut_def, unlock_if_nr_def, eval_external_defaults_nil] >>
  IF_CASES_TAC >- simp[] >>
  qmatch_goalsub_abbrev_tac `entry (initial_state am [FEMPTY] with
    <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|>)` >>
  `state_rel_frame machine_frame entry` by
    (simp[Abbr `entry`, ignore_bind_def] >>
     match_mp_tac machine_frame_bind >> conj_tac
     >- simp[machine_frame_nonpayable_value] >>
     gen_tac >> simp[] >> match_mp_tac machine_frame_bind >> conj_tac
     >- simp[state_rel_frame_def, eval_external_defaults_nil] >>
     qx_gen_tac `dvs` >>
     Cases_on `bind_arguments (type_env_all_modules mods) args (vals ++ dvs)` >>
     simp[machine_frame_primitives] >>
     simp[ignore_bind_def] >> match_mp_tac machine_frame_bind >>
     simp[machine_frame_primitives] >>
     match_mp_tac machine_frame_bind >>
     simp[REWRITE_RULE [ignore_bind_def] machine_frame_internal_lock]) >>
  Cases_on `entry (initial_state am [FEMPTY] with
    <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|>)` >>
  rename1 `entry _ = (entry_res,st)` >>
  `machine_frame (initial_state am []) st` by
    (drule_all state_rel_frame_at >>
     simp[machine_frame_def, initial_state_def]) >>
  `abstract_machine_from_state am.sources am.exports am.layouts st = am` by
    metis_tac[machine_frame_reconstruct] >>
  Cases_on `entry_res`
  >- simp[return_def] >>
  rename1 `INR exc` >> Cases_on `exc` >> simp[return_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >> strip_tac >> gvs[]
QED

Theorem selected_getter_storage[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function_trace orc gobs am cx nr mut ts mods args dflts vals body ret =
    (res,am',rqs,obs) /\
  storage_well_formed_on caller_cx (initial_state am []) (FST H) ==>
  storage_well_formed_on caller_cx (initial_state am' []) (FST H)
Proof
  strip_tac >> drule_all selected_getter_machine_frame >> simp[]
QED

Theorem storage_well_formed_on_target:
  cx'.txn.target = cx.txn.target ==>
  (storage_well_formed_on cx' st L <=> storage_well_formed_on cx st L)
Proof
  strip_tac >>
  `!b. get_storage cx' st b = get_storage cx st b` by
    (Cases_on `b` >> simp[get_storage_def]) >>
  simp[storage_well_formed_on_def]
QED

Theorem storage_observations_ok_target:
  cx'.txn.target = cx.txn.target ==>
  (storage_observations_ok cx' H obs <=> storage_observations_ok cx H obs)
Proof
  strip_tac >>
  `storage_trace_backends_well_formed cx' (FST H) obs <=>
   storage_trace_backends_well_formed cx (FST H) obs` by
    (Induct_on `obs` >> simp[storage_trace_backends_well_formed_def] >>
     Cases_on `h` >> fs[storage_trace_backends_well_formed_def] >>
     metis_tac[storage_well_formed_on_target]) >>
  fs[storage_observations_ok_def]
QED

Theorem finalize_pending_deletions_preserves_storage_well_formed_on[local]:
  storage_well_formed_on cx (initial_state am []) L ==>
  storage_well_formed_on cx (initial_state (finalize_pending_deletions am) []) L
Proof
  simp[storage_well_formed_on_def, initial_state_def,
       finalize_pending_deletions_def] >> strip_tac >>
  map_every qx_gen_tac [`b`, `slot`, `tv`] >> strip_tac >>
  first_x_assum (qspecl_then [`b`, `slot`, `tv`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `b` >- gvs[get_storage_def] >>
  gvs[get_storage_def] >>
  `!ds accounts. slots_in_range (accounts cx.txn.target).storage (w2n slot) tv ==>
     slots_in_range ((vfmExecution$process_deletions ds accounts) cx.txn.target).storage
       (w2n slot) tv` suffices_by metis_tac[] >>
  Induct >> simp[vfmExecutionTheory.process_deletions_def] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[vfmStateTheory.update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  IF_CASES_TAC >> simp[] >>
  irule (cj 1 vyperLookupStorageTheory.slots_in_range_zero_reads) >>
  simp[vyperStorageTheory.read_slot_def, vfmStateTheory.empty_account_state_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.empty_storage_def]
QED

(* The premises are those of checked_call_external_preserves_machine_well_typed
   (vyperTypeExternalCallMachine) without checked_external_call_inputs_ready,
   plus the finite horizon facts eval_storage_well_formed_on_mutual takes,
   about the call's own observations obs.

   Why it holds (a sketch): lookup and other failures return am; on success
   or halt, the bound arguments are typed (bind_arguments safe-casts), so
   checked_explicit_external_body_setup_current, checked_external_suffix_static
   and checked_external_empty_frame_ready give what
   eval_storage_well_formed_on_mutual needs for the defaults and the body;
   their traces are prefixes of obs; storage_well_formed_on and
   storage_observations_ok see cx only through cx.txn.target; process_deletions
   leaves the target's storage alone or all zero (slots_in_range_zero_reads);
   tStorage is untouched by finalize and the machine round trip. *)
Theorem checked_call_external_preserves_storage_well_formed_on:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  call_external_trace orc gobs am tx = (res,am',rqs,obs) /\
  cx.txn.target = tx.target /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_observations_ok cx H obs /\
  storage_well_formed_on cx (initial_state am []) (FST H) ==>
  storage_well_formed_on cx (initial_state am' []) (FST H)
Proof
  strip_tac >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  qpat_x_assum `call_external_trace _ _ _ _ = _` mp_tac >>
  simp[Once call_external_trace_def] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac vyperCallTheory.call_external_function_trace_error_rollback >> gvs[] >>
  `(?raw. MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body') ts) \/
   (?decl. MEM decl ts /\ is_public_getter_decl tx.function_name decl /\
     external_getter_tuple (find_function_module am tx.target tx.function_name) decl =
       SOME (mut,nr,args,dflts,ret,body'))` by
    (irule lookup_exported_function_checked_cases_current >>
     qexistsl [`am`, `art`, `mods`] >>
     gvs[vyperContextTheory.get_module_code_def,
         vyperContextTheory.get_self_code_def, initial_evaluation_context_def]) >>
  irule finalize_pending_deletions_preserves_storage_well_formed_on >>
  `!src. storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx src) (initial_state am []) (FST H)` by
    (gen_tac >>
     `storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx src)
        (initial_state am []) (FST H) =
      storage_well_formed_on cx (initial_state am []) (FST H)` by
       (irule storage_well_formed_on_target >> simp[initial_evaluation_context_def]) >>
     simp[]) >>
  `!src. storage_observations_ok
      (initial_evaluation_context am.sources am.layouts tx src) H obs` by
    (gen_tac >>
     `storage_observations_ok (initial_evaluation_context am.sources am.layouts tx src) H obs =
      storage_observations_ok cx H obs` by
       (irule storage_observations_ok_target >> simp[initial_evaluation_context_def]) >> simp[]) >>
  `!src st. storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx src) st (FST H) ==>
      storage_well_formed_on cx st (FST H)` by
    (rpt strip_tac >>
     `storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx src) st (FST H) =
      storage_well_formed_on cx st (FST H)` by
       (irule storage_well_formed_on_target >> simp[initial_evaluation_context_def]) >> gvs[]) >>
  gvs[] >>
  `LENGTH tx.args <= LENGTH args /\ LENGTH args - LENGTH tx.args <= LENGTH dflts` by
    (Cases_on `LENGTH tx.args > LENGTH args \/ LENGTH args - LENGTH tx.args > LENGTH dflts`
     >- (qpat_x_assum `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
         simp[Once call_external_function_trace_def]) >> decide_tac) >>
  `ALOOKUP mods (find_function_module am tx.target tx.function_name) = SOME ts` by
    gvs[vyperContextTheory.get_self_code_def, vyperContextTheory.get_module_code_def,
        initial_evaluation_context_def] >>
  `module_allocated am.layouts tx.target (find_function_module am tx.target tx.function_name) ts` by
    metis_tac[checked_contract_runtime_ready_module_allocated] >>
  (metis_tac[selected_explicit_storage, selected_getter_storage])
QED
