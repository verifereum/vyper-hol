(* Storage preservation for the checked explicit entry, before projection. *)
Theory vyperExplicitEntryFiniteStorage
Ancestors
  vyperExternalBodyFiniteStorage vyperExternalDefaultsFiniteStorage
  vyperTypeContractSoundness vyperTypeExternalDefaults vyperStorageFootprint
  vyperStorageTrace vyperInterpreter vyperState vyperTypeInvariants
  vyperTypeBindArguments vyperTypeExprSoundness

val _ = Parse.hide "body";

Theorem checked_explicit_locked_body_storage_well_formed_on:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  body_entry_ready art cx scope st /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  (!s r t. storage_well_formed_on cx s (FST H) /\
     storage_observations_ok cx H t.storage_trace /\
     lock_if_nr cx nr (is_view_mut mut) s = (r,t) ==>
     storage_well_formed_on cx t (FST H)) /\
  storage_observations_ok cx H rt.storage_trace /\
  (do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od) st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H)
Proof
  strip_tac >>
  drule_all checked_external_declaration_static >> strip_tac >>
  qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  pure_rewrite_tac[bind_def, ignore_bind_def] >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) st` >>
  rename1 `lock_if_nr cx nr (is_view_mut mut) st = (lr,ls)` >>
  Cases_on `lr` >> pure_asm_rewrite_tac[pairTheory.pair_case_thm, sumTheory.sum_case_def]
  >- (strip_tac >>
      `eval_stmts cx body ls = (res,rt)` by gvs[] >>
      `?obs. rt.storage_trace = ls.storage_trace ++ obs` by
        metis_tac[storage_trace_frame_prefix, evaluate_storage_trace_frame] >>
      `storage_observations_ok cx H ls.storage_trace` by
        fs[storage_observations_ok_append] >>
      `storage_well_formed_on cx ls (FST H)` by metis_tac[] >>
      `body_entry_ready art cx scope ls` by
        (qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
         simp[lock_if_nr_def, is_view_mut_def] >> strip_tac >>
         drule call_lock_action_frame_c53 >>
         gvs[body_entry_ready_def, state_well_typed_def]) >>
      irule checked_explicit_external_body_storage_well_formed_on_current >>
      metis_tac[]) >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem checked_explicit_defaults_body_storage_well_formed_on:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\ state_well_typed st /\ accounts_well_typed st.accounts /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st.immutables /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  (!s r t. storage_well_formed_on cx s (FST H) /\
     storage_observations_ok cx H t.storage_trace /\
     lock_if_nr cx nr (is_view_mut mut) s = (r,t) ==>
     storage_well_formed_on cx t (FST H)) /\
  storage_observations_ok cx H rt.storage_trace /\
  (do dvs <- eval_external_defaults cx (DROP k dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME scope => do
          set_scopes [scope]; lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body
        od
   od) st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H)
Proof
  strip_tac >>
  drule_all checked_external_empty_frame_ready >> strip_tac >>
  drule_all checked_external_suffix_static >>
  disch_then (qspec_then `k` strip_assume_tac) >>
  qpat_x_assum `bind _ _ st = _` mp_tac >> pure_rewrite_tac[bind_def] >>
  Cases_on `eval_external_defaults cx (DROP k dflts) st` >>
  rename1 `eval_external_defaults cx (DROP k dflts) st = (dr,ds)` >>
  Cases_on `dr` >> simp_tac std_ss []
  >- (rename1 `eval_external_defaults cx (DROP k dflts) st = (INL dvs,ds)` >>
      Cases_on `bind_arguments (type_env_all_modules mods) args (vals ++ dvs)`
      >- (simp_tac std_ss [raise_def] >> strip_tac >> gvs[raise_def] >>
          irule eval_external_defaults_storage_well_formed_on >>
          simp[] >>
          qexistsl [`artifact_env art mods src`, `DROP k dflts`, `INL dvs`, `st`] >>
          simp[runtime_consistent_def]) >>
      rename1 `bind_arguments (type_env_all_modules mods) args (vals ++ dvs) = SOME scope` >>
      simp_tac std_ss [bind_def, ignore_bind_def, set_scopes_def, return_def] >>
      strip_tac >>
      `(do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od)
         (ds with scopes := [scope]) = (res,rt)` by
        gvs[bind_def, ignore_bind_def, set_scopes_def, return_def] >>
      `storage_trace_frame
         (do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od)` by
        (irule storage_trace_frame_ignore_bind >>
         simp_tac bool_ss [storage_trace_frame_optional_locks, evaluate_storage_trace_frame]) >>
      `?obs. rt.storage_trace = ds.storage_trace ++ obs` by
        (drule_all storage_trace_frame_prefix >> simp[]) >>
      `storage_observations_ok cx H ds.storage_trace` by fs[] >>
      `storage_well_formed_on cx ds (FST H)` by
        (irule eval_external_defaults_storage_well_formed_on >> simp[] >>
         qexistsl [`artifact_env art mods src`, `DROP k dflts`, `INL dvs`, `st`] >>
         gvs[runtime_consistent_def]) >>
      drule_all eval_external_defaults_type_sound >> strip_tac >>
      drule_all eval_external_defaults_immutables_ready >> strip_tac >>
      `scope_well_typed scope` by metis_tac[bind_arguments_scope_well_typed_from_success] >>
      `body_entry_ready art cx scope (ds with scopes := [scope])` by
        gvs[body_entry_ready_def, state_well_typed_def] >>
      `storage_well_formed_on cx (ds with scopes := [scope]) (FST H)` by
        (irule (iffRL storage_well_formed_on_backends) >>
         goal_assum (drule_at Any) >> simp[]) >>
      drule_all checked_explicit_locked_body_storage_well_formed_on >> simp[]) >>
  rename1 `eval_external_defaults cx (DROP k dflts) st = (INR exc,ds)` >>
  strip_tac >> gvs[] >>
  irule eval_external_defaults_storage_well_formed_on >> simp[] >>
  qexistsl [`artifact_env art mods src`, `DROP k dflts`, `INR exc`, `st`] >>
  gvs[runtime_consistent_def]
QED

(* Arbitrary typed incoming state: the wrapper's empty initial frame is a
   specialization.  The two mechanical premises are discharged by the shared
   entry-frame theory at the whole-call join. *)
Theorem checked_explicit_entry_storage_well_formed_on:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\ state_well_typed st /\ accounts_well_typed st.accounts /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st.immutables /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  (!s r t. storage_well_formed_on cx s (FST H) /\
     storage_observations_ok cx H t.storage_trace /\
     send_call_value mut cx s = (r,t) ==>
     storage_well_formed_on cx t (FST H)) /\
  (!s r t. storage_well_formed_on cx s (FST H) /\
     storage_observations_ok cx H t.storage_trace /\
     lock_if_nr cx nr (is_view_mut mut) s = (r,t) ==>
     storage_well_formed_on cx t (FST H)) /\
  storage_observations_ok cx H rt.storage_trace /\
  (do send_call_value mut cx;
      dvs <- eval_external_defaults cx (DROP k dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME scope => do
          set_scopes [scope]; lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body
        od
   od) st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H)
Proof
  strip_tac >>
  qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `ignore_bind _ suffix st` >>
  pure_rewrite_tac[bind_def, ignore_bind_def] >>
  Cases_on `send_call_value mut cx st` >>
  rename1 `send_call_value mut cx st = (sr,ss)` >>
  Cases_on `sr` >> simp_tac std_ss []
  >- (strip_tac >>
      `suffix ss = (res,rt)` by gvs[] >>
      `storage_trace_frame suffix` by
        (unabbrev_all_tac >> irule storage_trace_frame_bind_all >>
         simp_tac bool_ss [storage_trace_frame_eval_external_defaults] >> qx_gen_tac `v` >>
         Cases_on `bind_arguments (type_env_all_modules mods) args (vals ++ v)` >>
         simp_tac std_ss [storage_trace_frame_raise] >>
         irule storage_trace_frame_ignore_bind >>
         simp_tac bool_ss [storage_trace_frame_state_updates] >>
         irule storage_trace_frame_ignore_bind >>
         simp_tac bool_ss [storage_trace_frame_optional_locks, evaluate_storage_trace_frame]) >>
      `?obs. rt.storage_trace = ss.storage_trace ++ obs` by
        (drule_all storage_trace_frame_prefix >> simp[]) >>
      `storage_observations_ok cx H ss.storage_trace` by fs[] >>
      `storage_well_formed_on cx ss (FST H)` by metis_tac[] >>
      drule_all send_call_value_state_sound_c53 >> strip_tac >>
      `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx ss.immutables` by
        metis_tac[] >>
      unabbrev_all_tac >>
      drule_all checked_explicit_defaults_body_storage_well_formed_on >> simp[]) >>
  strip_tac >> gvs[] >> metis_tac[]
QED
