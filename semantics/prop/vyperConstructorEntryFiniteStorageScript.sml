(* Constructor entry preservation from an arbitrary typed incoming state. *)
Theory vyperConstructorEntryFiniteStorage
Ancestors
  vyperConstructorBodyFiniteStorage vyperExternalEntryStorageFrame
  vyperTypeDeploymentMachine vyperTypeDeploymentSoundness
  vyperTypeContractSoundness vyperTypeContractStaticMaps
  vyperTypeSystem vyperTypeInvariants vyperTypeInitialState vyperTypeBindArguments
  vyperTypeExprSoundness vyperStorageFootprint vyperStorageTrace
  vyperInterpreter vyperState vyperContext

val _ = Parse.hide "body";

Theorem checked_constructor_locked_storage[local]:
  check_contract T layouts tx.target mods = SOME deploy_art /\
  check_contract F layouts tx.target mods = SOME runtime_art /\
  ALOOKUP sources tx.target = SOME mods /\ ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts = SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context sources layouts tx NONE with in_deploy := T) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP FST args) /\ st.scopes = [scope] /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  env_immutables_consistent (artifact_env deploy_art mods NONE) cx st /\
  context_well_typed cx /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H rt.storage_trace /\
  (do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od) st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H)
Proof
  strip_tac >>
  qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  pure_rewrite_tac[ignore_bind_def, bind_def] >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) st` >>
  rename1 `lock_if_nr cx nr (is_view_mut mut) st = (lr,ls)` >>
  Cases_on `lr` >> simp_tac std_ss []
  >- (strip_tac >>
      `eval_stmts cx body ls = (res,rt)` by gvs[] >>
      `?obs. rt.storage_trace = ls.storage_trace ++ obs` by
        metis_tac[storage_trace_frame_prefix, evaluate_storage_trace_frame] >>
      `storage_observations_ok cx H ls.storage_trace` by fs[] >>
      `storage_well_formed_on cx ls (FST H)` by
        metis_tac[lock_if_nr_preserves_storage_well_formed_on] >>
      `ls.scopes = st.scopes /\ ls.immutables = st.immutables /\ ls.accounts = st.accounts` by
        (qpat_x_assum `lock_if_nr _ _ _ st = _` mp_tac >>
         pure_rewrite_tac[lock_if_nr_def, is_view_mut_def] >> strip_tac >>
         drule call_lock_action_frame_c53 >> simp[]) >>
      `state_well_typed ls` by gvs[state_well_typed_def] >>
      `env_immutables_consistent (artifact_env deploy_art mods NONE) cx ls` by
        metis_tac[env_immutables_consistent_immutables_cong] >>
      metis_tac[checked_constructor_body_storage_well_formed_on]) >>
  strip_tac >>
  FULL_SIMP_TAC pure_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def, pairTheory.PAIR_EQ] >>
  metis_tac[lock_if_nr_preserves_storage_well_formed_on]
QED

Theorem checked_constructor_bound_storage[local]:
  check_contract T layouts tx.target mods = SOME deploy_art /\
  check_contract F layouts tx.target mods = SOME runtime_art /\
  ALOOKUP sources tx.target = SOME mods /\ ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts = SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context sources layouts tx NONE with in_deploy := T) /\
  ALL_DISTINCT (MAP FST args) /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  env_immutables_consistent (artifact_env deploy_art mods NONE) cx st /\
  context_well_typed cx /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H rt.storage_trace /\
  (case bind_arguments (type_env_all_modules mods) args vals of
     NONE => raise (Error (RuntimeError "call bind_arguments"))
   | SOME scope => do set_scopes [scope];
       lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od) st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H)
Proof
  strip_tac >>
  Cases_on `bind_arguments (type_env_all_modules mods) args vals`
  >- (gvs[raise_def]) >>
  rename1 `bind_arguments (type_env_all_modules mods) args vals = SOME scope` >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `(do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od)
     (st with scopes := [scope]) = (res,rt)` by
    gvs[bind_def, ignore_bind_def, set_scopes_def, return_def] >>
  `state_well_typed (st with scopes := [scope])` by
    gvs[state_well_typed_def] >>
  `env_immutables_consistent (artifact_env deploy_art mods NONE) cx
     (st with scopes := [scope])` by
    (irule (iffLR env_immutables_consistent_immutables_cong) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `storage_well_formed_on cx (st with scopes := [scope]) (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `accounts_well_typed (st with scopes := [scope]).accounts /\
   (st with scopes := [scope]).scopes = [scope]` by simp[] >>
  drule_all checked_constructor_locked_storage >> simp[]
QED

Theorem checked_constructor_entry_storage_well_formed_on:
  check_contract T layouts tx.target mods = SOME deploy_art /\
  check_contract F layouts tx.target mods = SOME runtime_art /\
  ALOOKUP sources tx.target = SOME mods /\ ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts = SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context sources layouts tx NONE with in_deploy := T) /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  env_immutables_consistent (artifact_env deploy_art mods NONE) cx st /\
  context_well_typed cx /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H rt.storage_trace /\
  (do send_call_value mut cx;
      dvs <- eval_external_defaults cx (DROP k dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME scope => do set_scopes [scope];
          lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od
   od) st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H)
Proof
  strip_tac >>
  `dflts = []` by metis_tac[check_contract_constructor_no_defaults] >>
  `ALL_DISTINCT (MAP FST args)` by metis_tac[checked_constructor_args_distinct] >>
  qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  pure_asm_rewrite_tac[listTheory.DROP_def, bind_def, eval_external_defaults_nil,
    pairTheory.pair_case_thm, sumTheory.sum_case_def, listTheory.APPEND_NIL] >>
  qmatch_goalsub_abbrev_tac `ignore_bind _ suffix st` >>
  pure_rewrite_tac[bind_def, ignore_bind_def] >>
  Cases_on `send_call_value mut cx st` >>
  rename1 `send_call_value mut cx st = (sr,ss)` >>
  Cases_on `sr` >> simp_tac std_ss []
  >- (strip_tac >>
      `suffix ss = (res,rt)` by gvs[] >>
      `storage_trace_frame suffix` by
        (unabbrev_all_tac >>
         irule storage_trace_frame_bind_all >>
         simp_tac bool_ss [storage_trace_frame_eval_external_defaults] >>
         qx_gen_tac `dvs` >>
         Cases_on `bind_arguments (type_env_all_modules mods) args (vals ++ dvs)` >>
         simp_tac std_ss [storage_trace_frame_raise] >>
         irule storage_trace_frame_ignore_bind >>
         simp_tac bool_ss [storage_trace_frame_state_updates] >>
         irule storage_trace_frame_ignore_bind >>
         simp_tac bool_ss [storage_trace_frame_optional_locks, evaluate_storage_trace_frame]) >>
      `?obs. rt.storage_trace = ss.storage_trace ++ obs` by
        metis_tac[storage_trace_frame_prefix] >>
      `storage_observations_ok cx H ss.storage_trace` by fs[] >>
      `storage_well_formed_on cx ss (FST H)` by
        metis_tac[send_call_value_preserves_storage_well_formed_on] >>
      drule_all send_call_value_state_sound_c53 >> strip_tac >>
      `env_immutables_consistent (artifact_env deploy_art mods NONE) cx ss` by
        metis_tac[env_immutables_consistent_immutables_cong] >>
      `(case bind_arguments (type_env_all_modules mods) args vals of
          NONE => raise (Error (RuntimeError "call bind_arguments"))
        | SOME scope => do set_scopes [scope];
            lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od) ss = (res,rt)` by
        (qpat_x_assum `suffix ss = _` mp_tac >>
         simp_tac std_ss [Abbr `suffix`, bind_def, eval_external_defaults_nil] >> simp[]) >>
      drule_all checked_constructor_bound_storage >> simp[]) >>
  strip_tac >>
  FULL_SIMP_TAC pure_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def, pairTheory.PAIR_EQ] >>
  `rt = ss` by gvs[] >>
  drule_all send_call_value_preserves_storage_well_formed_on >> simp[]
QED
