(* Checked explicit external-entry finite-prefix preservation. *)
Theory guardSourceExternal
Ancestors
  guardSourceExternalPrimitives guardSourceExecution vyperCallStorageFootprint
  vyperInterpreter vyperState vyperStorageFootprint vyperStorageTrace
  vyperFiniteStoragePreservation vyperTypeExprSoundness vyperTypeExternalDefaults
  vyperTypeContractSoundness vyperTypeEvalStoragePreservation vyperEvalOutcomeSuffix
  vyperContext vyperTypeInvariants vyperTypeInitialState e2eDefs

val _ = Parse.hide "body";

fun prefix_assumption_tac (asl,w) =
  if is_exists w then (qexists `sfx` >> first_assum ACCEPT_TAC) (asl,w)
  else first_assum ACCEPT_TAC (asl,w);

(* Keep the existential premise as a theorem for drule_all after strip_tac
   has exposed its concrete suffix witness. *)
val remember_prefix_tac =
  qpat_assum `selected = prefix ++ suffix` (fn th =>
    let
      val (lhs,rhs) = dest_eq (concl th)
      val (prefix,suffix) = listSyntax.dest_append rhs
      val bound = genvar (type_of suffix)
      val proposition = mk_exists (bound,
        mk_eq (lhs,listSyntax.mk_append (prefix,bound)))
    in assume_tac (EXISTS (proposition,suffix) th) end);

(* Substitute only the result state; preserve the selected-trace parameter. *)
val project_result_state_tac =
  qpat_x_assum `(_,_) = (_,_)`
    (SUBST_ALL_TAC o SYM o CONJUNCT2 o PURE_REWRITE_RULE [pairTheory.PAIR_EQ]);

val selected_prefix_conditions = ``
  IS_SOME st.outcomes /\ valid_horizon cx initial_st H st.storage_trace /\
  (?sfx. selected = out.storage_trace ++ sfx) /\
  EVERY (\r. MEM r (FST H)) (storage_trace_regions selected) /\
  EVERY (\l. MEM l (SND H)) (storage_trace_locks selected) /\
  storage_roots_fit selected /\
  (!pre rq co sfx.
    selected = pre ++ StorageOutcome rq co :: sfx /\
    valid_horizon cx initial_st H pre /\
    storage_well_formed_on cx
      (empty_state with <|accounts := rq.cr_accounts; tStorage := rq.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on cx
      (empty_state with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>) (FST H))``;

Theorem explicit_current_body_finite_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP FST args) /\ body_entry_ready art cx scope st /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\ ^selected_prefix_conditions /\
  eval_stmts cx body st = (res,out) ==>
  storage_well_formed_on cx out (FST H) /\
  storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >> drule_all checked_explicit_external_body_setup_current >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (gvs[] >> drule_all checked_explicit_external_body_call_evaluation_safe >> simp[]) >>
  `runtime_consistent env_body cx st` by simp[runtime_consistent_def] >>
  mp_tac (Q.INST [`H` |-> `H`, `v0` |-> `cx`, `v1` |-> `body`,
    `initial_st` |-> `initial_st`, `selected` |-> `selected`,
    `env` |-> `env_body`, `ret_ty` |-> `ret`, `env'` |-> `env_after`,
    `st` |-> `st`, `res` |-> `res`, `st'` |-> `out`]
    (SPEC_ALL (cj 2 eval_storage_finite_prefix_mutual))) >>
  (impl_tac >- (rpt conj_tac >> prefix_assumption_tac)) >> simp[]
QED

Theorem explicit_locked_body_finite_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  body_entry_ready art cx scope st /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\ ^selected_prefix_conditions /\
  (do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od) st = (res,out) ==>
  storage_well_formed_on cx out (FST H) /\
  storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >> remember_prefix_tac >>
  `storage_observations_ok cx H st.storage_trace` by gvs[valid_horizon_def] >>
  qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  pure_rewrite_tac[ignore_bind_def, bind_def] >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) st` >>
  rename1 `lock_if_nr cx nr (is_view_mut mut) st = (lr,ls)` >> Cases_on `lr` >>
  simp_tac bool_ss [pairTheory.pair_case_def, sumTheory.sum_case_def] >> strip_tac
  >- (`?tail. selected = ls.storage_trace ++ tail` by
       (mp_tac (cj 2 evaluate_storage_trace_frame) >>
        disch_then (qspecl_then [`cx`,`body`] assume_tac) >>
        drule_all storage_trace_frame_prefix >> strip_tac >>
        metis_tac[listTheory.APPEND_ASSOC]) >>
      `storage_well_formed_on cx ls (FST H) /\
       storage_observations_ok cx H ls.storage_trace` by
       (remember_prefix_tac >> drule_all lock_if_nr_finite_prefix >> simp[]) >>
      `ls.scopes = st.scopes /\ ls.immutables = st.immutables /\ ls.accounts = st.accounts` by
       (qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
        simp[lock_if_nr_def, is_view_mut_def] >> metis_tac[call_lock_action_frame_c53]) >>
      `body_entry_ready art cx scope ls` by
       gvs[body_entry_ready_def, vyperTypeInvariantsTheory.state_well_typed_def] >>
      `IS_SOME ls.outcomes` by metis_tac[optional_lock_outcomes] >>
      `valid_horizon cx initial_st H ls.storage_trace` by gvs[valid_horizon_def] >>
      drule_all checked_external_declaration_static >> strip_tac >>
      drule_all explicit_current_body_finite_prefix >> simp[]) >>
  project_result_state_tac >>
  remember_prefix_tac >> drule_all lock_if_nr_finite_prefix >> simp[]
QED

Theorem external_defaults_oracle_mode[local]:
  IS_SOME st.outcomes /\ eval_external_defaults cx es st = (res,out) ==>
  IS_SOME out.outcomes
Proof
  simp[eval_external_defaults_run, LET_THM] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >> simp[] >> strip_tac >>
  drule (cj 6 eval_outcome_suffix_mutual) >>
  disch_then (strip_assume_tac o MATCH_MP outcome_suffix_modes) >> gvs[] >>
  Cases_on `st.outcomes` >> Cases_on `r.outcomes` >> gvs[]
QED

Theorem explicit_defaults_body_finite_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\ state_well_typed st /\ accounts_well_typed st.accounts /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st.immutables /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\ ^selected_prefix_conditions /\
  (do dvs <- eval_external_defaults cx (DROP k dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME scope => do set_scopes [scope]; lock_if_nr cx nr (is_view_mut mut);
                         eval_stmts cx body od
   od) st = (res,out) ==>
  storage_well_formed_on cx out (FST H) /\
  storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >> remember_prefix_tac >>
  drule_all checked_external_empty_frame_ready >> strip_tac >>
  `runtime_consistent (artifact_env art mods src) cx (st with scopes := [FEMPTY])` by
    simp[runtime_consistent_def] >>
  drule_all checked_external_suffix_static >>
  disch_then (qspec_then `k` strip_assume_tac) >>
  qpat_x_assum `bind _ _ st = _` mp_tac >> pure_rewrite_tac[bind_def] >>
  Cases_on `eval_external_defaults cx (DROP k dflts) st` >>
  rename1 `eval_external_defaults cx (DROP k dflts) st = (dr,ds)` >> Cases_on `dr` >>
  pure_asm_rewrite_tac[pairTheory.pair_case_def, sumTheory.sum_case_def] >>
  BETA_TAC >> pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC
  >- (rename1 `eval_external_defaults cx (DROP k dflts) st = (INL dvs,ds)` >>
      Cases_on `bind_arguments (type_env_all_modules mods) args (vals ++ dvs)` >>
      simp_tac bool_ss [raise_def, optionTheory.option_case_def]
      >- (strip_tac >> project_result_state_tac >>
          remember_prefix_tac >> drule_all external_defaults_finite_prefix >> simp[]) >>
      rename1 `bind_arguments _ _ _ = SOME scope` >>
      pure_rewrite_tac[ignore_bind_def, bind_def, set_scopes_def, return_def] >>
      BETA_TAC >> pure_rewrite_tac[pairTheory.pair_case_def, sumTheory.sum_case_def] >>
      BETA_TAC >> strip_tac >>
      `(do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od)
         (ds with scopes := [scope]) = (res,out)` by
        gvs[bind_def, ignore_bind_def] >>
      `storage_trace_frame (do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od)` by
        (irule storage_trace_frame_ignore_bind >>
         simp[storage_trace_frame_optional_locks, evaluate_storage_trace_frame]) >>
      `?tail. selected = ds.storage_trace ++ tail` by
        (drule_all storage_trace_frame_prefix >> strip_tac >>
         qexists_tac `observations ++ sfx` >>
         qpat_x_assum `selected = out.storage_trace ++ sfx` mp_tac >>
         qpat_x_assum `out.storage_trace = _ ++ observations` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [listTheory.APPEND_ASSOC]) >>
      `storage_well_formed_on cx ds (FST H) /\
       storage_observations_ok cx H ds.storage_trace` by
        (remember_prefix_tac >> drule_all external_defaults_finite_prefix >> simp[]) >>
      `state_well_typed ds /\ accounts_well_typed ds.accounts` by
        (drule_all eval_external_defaults_type_sound >> simp[]) >>
      `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx ds.immutables` by
        (drule_all eval_external_defaults_immutables_ready >> simp[]) >>
      `scope_well_typed scope` by
        metis_tac[vyperTypeBindArgumentsTheory.bind_arguments_scope_well_typed_from_success] >>
      `body_entry_ready art cx scope (ds with scopes := [scope])` by
        gvs[body_entry_ready_def, vyperTypeInvariantsTheory.state_well_typed_def] >>
      `storage_well_formed_on cx (ds with scopes := [scope]) (FST H)` by
        simp[storage_well_formed_on_scopes] >>
      `IS_SOME ds.outcomes` by metis_tac[external_defaults_oracle_mode] >>
      `valid_horizon cx initial_st H ds.storage_trace` by gvs[valid_horizon_def] >>
      `IS_SOME (ds with scopes := [scope]).outcomes` by simp[] >>
      `valid_horizon cx initial_st H (ds with scopes := [scope]).storage_trace` by gvs[] >>
      drule_all explicit_locked_body_finite_prefix >> simp[]) >>
  strip_tac >> project_result_state_tac >> remember_prefix_tac >> drule_all external_defaults_finite_prefix >> simp[]
QED

Theorem explicit_entry_finite_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\ state_well_typed st /\ accounts_well_typed st.accounts /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st.immutables /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\ ^selected_prefix_conditions /\
  (do send_call_value mut cx;
      dvs <- eval_external_defaults cx (DROP k dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME scope => do set_scopes [scope]; lock_if_nr cx nr (is_view_mut mut);
                         eval_stmts cx body od
   od) st = (res,out) ==>
  storage_well_formed_on cx out (FST H) /\
  storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >> remember_prefix_tac >>
  qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  pure_rewrite_tac[ignore_bind_def, bind_def] >>
  Cases_on `send_call_value mut cx st` >>
  rename1 `send_call_value mut cx st = (sr,ss)` >> Cases_on `sr` >>
  pure_asm_rewrite_tac[pairTheory.pair_case_def, sumTheory.sum_case_def] >>
  BETA_TAC >> pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC
  >- (strip_tac >>
      `storage_well_formed_on cx ss (FST H)` by metis_tac[send_call_value_storage] >>
      drule_all send_call_value_state_sound_c53 >> strip_tac >>
      drule send_call_value_trace_outcomes >> strip_tac >>
      `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx ss.immutables` by
        metis_tac[] >>
      `valid_horizon cx initial_st H ss.storage_trace` by metis_tac[] >>
      `IS_SOME ss.outcomes` by metis_tac[] >>
      qpat_assum `cx = _` (fn th =>
        qpat_x_assum `bind _ _ ss = _` (assume_tac o REWRITE_RULE [GSYM th])) >>
      drule_all (PURE_REWRITE_RULE [ignore_bind_def] explicit_defaults_body_finite_prefix) >> simp[]) >>
  strip_tac >> project_result_state_tac >> drule send_call_value_trace_outcomes >> strip_tac >>
  conj_tac >- metis_tac[send_call_value_storage] >> gvs[valid_horizon_def]
QED

Theorem selected_explicit_finite_prefix:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\ module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx (initial_state am []) (FST H) /\
  EVERY (\r. MEM r (FST H)) (storage_trace_regions obs) /\
  EVERY (\l. MEM l (SND H)) (storage_trace_locks obs) /\ storage_roots_fit obs /\
  (!pre rq co sfx.
    obs = pre ++ StorageOutcome rq co :: sfx /\
    valid_horizon cx (initial_state am []) H pre /\
    storage_well_formed_on cx
      (empty_state with <|accounts := rq.cr_accounts; tStorage := rq.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on cx
      (empty_state with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>) (FST H)) /\
  call_external_function_trace (SOME os) gs am cx nr mut ts mods args dflts vals body ret =
    (res,am',rqs,obs) ==>
  storage_observations_ok cx H obs
Proof
  strip_tac >>
  `ALOOKUP am.sources tx.target = SOME mods` by gvs[checked_contract_runtime_ready_def] >>
  `context_well_typed cx` by
    (qpat_x_assum `call_tx_well_typed tx` mp_tac >>
     simp[call_tx_well_typed_def, vyperTypeInvariantsTheory.context_well_typed_def,
          initial_evaluation_context_def]) >>
  `~cx.in_deploy` by simp[initial_evaluation_context_def] >>
  drule_at (Pat `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)
    external_function_trace_observations >> disch_then irule >>
  asm_rewrite_tac[] >>
  qabbrev_tac `st0 = initial_state am [FEMPTY] with
    <|outcomes := SOME os; requests := []; gas_obs := gs; storage_trace := []|>` >>
  qpat_assum `Abbrev (st0 = _)`
    (fn th => rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  rpt gen_tac >> strip_tac >> remember_prefix_tac >>
  `state_well_typed st0 /\ accounts_well_typed st0.accounts` by
    (qpat_x_assum `machine_well_typed am` mp_tac >>
     simp[Abbr `st0`, initial_state_def, vyperTypeInvariantsTheory.state_well_typed_def,
          vyperTypeInitialStateTheory.machine_well_typed_def,
          vyperTypeInvariantsTheory.scope_well_typed_def]) >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st0.immutables` by
    (simp_tac (srw_ss()) [Abbr `st0`, initial_state_def] >>
     metis_tac[checked_contract_runtime_ready_def,
               vyperTypeContractFunctionTheory.immutables_ready_initial_evaluation_context_source]) >>
  `storage_well_formed_on cx st0 (FST H)` by
    (`storage_well_formed_on cx st0 (FST H) <=>
      storage_well_formed_on cx (initial_state am []) (FST H)` by
       (irule storage_well_formed_on_backends >> simp[Abbr `st0`, initial_state_def]) >>
     metis_tac[]) >>
  `IS_SOME st0.outcomes` by simp[Abbr `st0`] >>
  `valid_horizon cx (initial_state am []) H st0.storage_trace` by
    simp[Abbr `st0`, valid_horizon_def, storage_observations_ok_def,
         storage_trace_regions_def, storage_trace_locks_def, storage_roots_fit_def,
         storage_trace_backends_well_formed_def] >>
  qpat_assum `cx = _` (fn th =>
    qpat_x_assum `ignore_bind _ _ st0 = _` (assume_tac o REWRITE_RULE [GSYM th])) >>
  `storage_well_formed_on cx rt (FST H) /\
   storage_observations_ok cx H rt.storage_trace` by
    (drule_all explicit_entry_finite_prefix >> simp[]) >>
  qpat_assum `cx = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  first_assum ACCEPT_TAC
QED
