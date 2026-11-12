(* Mechanical storage boundaries for external entry computations. *)
Theory vyperExternalEntryStorageFrame
Ancestors
  vyperFiniteStoragePreservation vyperStorageFootprint vyperStorageTrace
  vyperInterpreter vyperState vyperStorageBackend vyperTypeEvalStoragePreservation

val _ = Parse.hide "body";

Theorem send_call_value_preserves_storage_well_formed_on:
  storage_well_formed_on cx st regions /\
  send_call_value mut cx st = (res,u) ==>
  storage_well_formed_on cx u regions
Proof
  strip_tac >>
  qpat_x_assum `send_call_value _ _ _ = _` mp_tac >>
  Cases_on `cx.txn.value = 0` >>
  simp[send_call_value_def, ignore_bind_def, bind_def, check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `mut = Payable` >> simp[return_def, raise_def] >>
  strip_tac >> gvs[] >>
  metis_tac[transfer_value_preserves_storage_well_formed_on]
QED

Theorem unlock_if_nr_preserves_storage_well_formed_on:
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H u.storage_trace /\
  unlock_if_nr cx nr view st = (res,u) ==>
  storage_well_formed_on cx u (FST H)
Proof
  strip_tac >>
  Cases_on `nr /\ ~view` >> gvs[unlock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
  rename1 `release_nonreentrant_lock _ slot st = (res,u)` >>
  `MEM (StorageLock slot) u.storage_trace` by
    (qpat_x_assum `release_nonreentrant_lock _ _ _ = _` mp_tac >>
     simp[release_nonreentrant_lock_eq] >> strip_tac >> gvs[]) >>
  drule_all release_lock_preserves_storage_well_formed_on >> simp[]
QED

Theorem lock_if_nr_preserves_storage_well_formed_on:
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H u.storage_trace /\
  lock_if_nr cx nr view st = (res,u) ==>
  storage_well_formed_on cx u (FST H)
Proof
  strip_tac >>
  Cases_on `nr` >> gvs[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
  rename1 `acquire_nonreentrant_lock _ slot _` >>
  qpat_x_assum `(do _; _ od) _ = _` mp_tac >>
  simp[ignore_bind_def, bind_def] >>
  Cases_on `acquire_nonreentrant_lock cx.txn.target slot
    (view \/ cx.txn.is_static) st` >>
  rename1 `acquire_nonreentrant_lock _ _ _ st = (out,s)` >>
  `MEM (StorageLock slot) s.storage_trace` by
    (qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
     simp[acquire_nonreentrant_lock_eq] >> rpt IF_CASES_TAC >>
     strip_tac >> gvs[]) >>
  Cases_on `out` >> simp[return_def, check_not_static_def, check_def,
    assert_def, raise_def] >> strip_tac >>
  Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  gvs[return_def, assert_def, raise_def] >>
  drule_all acquire_lock_preserves_storage_well_formed_on >> simp[]
QED

Theorem initial_state_abstract_machine_storage_well_formed_on:
  storage_well_formed_on cx
    (initial_state (abstract_machine_from_state srcs exps layouts st) []) regions <=>
  storage_well_formed_on cx st regions
Proof
  irule storage_well_formed_on_backends >>
  simp[initial_state_def, abstract_machine_from_state_def]
QED

Theorem call_external_function_trace_storage_well_formed_on_general:
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx (initial_state am []) (FST H) /\
  (!am_c constant_trace r u.
    (if cx.in_deploy then evaluate_module_constants_trace cx am cx.txn.target (constants_order mods)
     else (SOME am, [])) = (SOME am_c,constant_trace) /\
    (do send_call_value mut cx;
        dvs <- eval_external_defaults cx (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts);
        case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
          NONE => raise (Error (RuntimeError "call bind_arguments"))
        | SOME env => do
            set_scopes [env]; lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body
          od
     od) (initial_state am_c [FEMPTY] with
       <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := constant_trace|>) = (r,u) /\
    storage_observations_ok cx H u.storage_trace ==>
    storage_well_formed_on cx u (FST H)) /\
  storage_observations_ok cx H obs /\
  call_external_function_trace orc gobs am cx nr mut ts mods args dflts vals body ret =
    (res,am_out,rqs,obs) ==>
  storage_well_formed_on cx (initial_state am_out []) (FST H)
Proof
  strip_tac >>
  qpat_x_assum `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_trace_def] >>
  Cases_on `LENGTH vals > LENGTH args \/ LENGTH args - LENGTH vals > LENGTH dflts` >>
  simp[] >- (strip_tac >> gvs[]) >>
  Cases_on `if cx.in_deploy then evaluate_module_constants_trace cx am cx.txn.target (constants_order mods)
    else (SOME am, [])` >>
  rename1 `(if cx.in_deploy then _ else _) = (constants,constant_trace)` >>
  Cases_on `constants` >> simp[] >- (strip_tac >> gvs[]) >>
  rename1 `(if cx.in_deploy then _ else _) = (SOME am_c,constant_trace)` >>
  qmatch_goalsub_abbrev_tac `ignore_bind (send_call_value mut cx) rest s0` >>
  Cases_on `ignore_bind (send_call_value mut cx) rest s0` >>
  rename1 `ignore_bind (send_call_value mut cx) rest s0 = (out,u)` >>
  `!r t. ignore_bind (send_call_value mut cx) rest s0 = (r,t) /\
    storage_observations_ok cx H t.storage_trace ==>
    storage_well_formed_on cx t (FST H)` by
    (qpat_x_assum `!am_c constant_trace r u. _`
       (qspecl_then [`am_c`,`constant_trace`] mp_tac) >>
     simp[Abbr `rest`, lock_if_nr_def, is_view_mut_def]) >>
  Cases_on `out` >> simp[]
  >- (qmatch_goalsub_abbrev_tac `unlock u` >>
      Cases_on `unlock u` >> rename1 `unlock u = (ur,v)` >>
      Cases_on `ur` >> simp[] >> strip_tac >> gvs[] >>
      `unlock = unlock_if_nr cx nr (is_view_mut mut)` by
        simp[Abbr `unlock`, unlock_if_nr_def, is_view_mut_def] >>
      qpat_x_assum `Abbrev (unlock = _)` kall_tac >>
      qpat_x_assum `unlock = _` SUBST_ALL_TAC >>
      `storage_trace_frame (unlock_if_nr cx nr (is_view_mut mut))` by
        simp[storage_trace_frame_optional_locks] >>
      drule_all storage_trace_frame_prefix >> strip_tac >>
      `storage_well_formed_on cx u (FST H)` by gvs[] >>
      simp[initial_state_abstract_machine_storage_well_formed_on] >>
      drule_all unlock_if_nr_preserves_storage_well_formed_on >> simp[]) >>
  rename1 `ignore_bind (send_call_value mut cx) rest s0 = (INR exc,u)` >>
  Cases_on `exc` >> simp[] >>
  TRY (strip_tac >> gvs[] >> NO_TAC)
  >- (qmatch_goalsub_abbrev_tac `unlock u` >>
      Cases_on `unlock u` >> rename1 `unlock u = (ur,w)` >>
      Cases_on `ur` >> simp[]
      >- (Cases_on `evaluate_type (type_env_all_modules mods) ret` >> simp[]
          >- (strip_tac >> gvs[]) >>
          rename1 `safe_cast tv rv` >> Cases_on `safe_cast tv rv` >> simp[]
          >- (strip_tac >> gvs[]) >>
          strip_tac >> gvs[] >>
          `unlock = unlock_if_nr cx nr (is_view_mut mut)` by
            simp[Abbr `unlock`, unlock_if_nr_def, is_view_mut_def] >>
          qpat_x_assum `Abbrev (unlock = _)` kall_tac >>
          qpat_x_assum `unlock = _` SUBST_ALL_TAC >>
          `storage_trace_frame (unlock_if_nr cx nr (is_view_mut mut))` by
            simp[storage_trace_frame_optional_locks] >>
          drule_all storage_trace_frame_prefix >> strip_tac >>
          `storage_well_formed_on cx u (FST H)` by gvs[] >>
          simp[initial_state_abstract_machine_storage_well_formed_on] >>
          drule_all unlock_if_nr_preserves_storage_well_formed_on >> simp[]) >>
      strip_tac >> gvs[]) >>
  strip_tac >> gvs[initial_state_abstract_machine_storage_well_formed_on]
QED

Theorem call_external_function_trace_storage_well_formed_on:
  ~cx.in_deploy /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx (initial_state am []) (FST H) /\
  (!r u.
    (do send_call_value mut cx;
        dvs <- eval_external_defaults cx (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts);
        case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
          NONE => raise (Error (RuntimeError "call bind_arguments"))
        | SOME env => do
            set_scopes [env]; lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body
          od
     od) (initial_state am [FEMPTY] with
       <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|>) = (r,u) /\
    storage_observations_ok cx H u.storage_trace ==>
    storage_well_formed_on cx u (FST H)) /\
  storage_observations_ok cx H obs /\
  call_external_function_trace orc gobs am cx nr mut ts mods args dflts vals body ret =
    (res,am_out,rqs,obs) ==>
  storage_well_formed_on cx (initial_state am_out []) (FST H)
Proof
  strip_tac >>
  drule_at (Pat `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)
    call_external_function_trace_storage_well_formed_on_general >>
  disch_then (qspec_then `H` mp_tac) >>
  simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"]
QED
