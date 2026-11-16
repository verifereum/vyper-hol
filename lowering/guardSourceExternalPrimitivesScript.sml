(* External-entry lifting of the checked selected-prefix evaluator invariant. *)
Theory guardSourceExternalPrimitives
Ancestors
  guardSourceExecution vyperCallStorageFootprint vyperTypeExternalDefaults
  vyperTypeContractSoundness vyperTypeEvalStoragePreservation vyperEvalOutcomeSuffix
  vyperInterpreter vyperState vyperStorageFootprint vyperStorageTrace
  vyperFiniteStoragePreservation vyperTypeExprSoundness e2eDefs

val _ = Parse.hide "body";

fun prefix_assumption_tac (asl,w) =
  if is_exists w then (qexists `sfx` >> first_assum ACCEPT_TAC) (asl,w)
  else first_assum ACCEPT_TAC (asl,w);

Theorem external_defaults_finite_prefix:
  well_typed_exprs env es /\
  runtime_consistent env cx (st with scopes := [FEMPTY]) /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs es) /\
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
      (empty_state with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>) (FST H)) /\
  eval_external_defaults cx es st = (res,out) ==>
  storage_well_formed_on cx out (FST H) /\
  storage_observations_ok cx H out.storage_trace
Proof
  simp_tac bool_ss [eval_external_defaults_run, LET_THM] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `_ with scopes := _ = out` (SUBST_ALL_TAC o SYM) >>
  simp_tac (srw_ss()) [storage_well_formed_on_scopes] >>
  irule (cj 6 eval_storage_finite_prefix_mutual) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`env`,`initial_st`,`q`,`selected`,`st with scopes := [FEMPTY]`,`es`] >>
  qpat_assum `!pre rq co sfx. _`
    (assume_tac o PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  qpat_assum `selected = _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  simp_tac (srw_ss()) [storage_well_formed_on_scopes] >>
  rpt conj_tac >> prefix_assumption_tac
QED

Theorem optional_lock_backend_trace:
  (lock_if_nr cx nr view st = (res,out) \/
   unlock_if_nr cx nr view st = (res,out)) ==>
  (storage_trace_backends_well_formed cx L out.storage_trace <=>
   storage_trace_backends_well_formed cx L st.storage_trace)
Proof
  Cases_on `cx.nonreentrant_slot` >>
  rw[lock_if_nr_def, unlock_if_nr_def,
     acquire_nonreentrant_lock_eq, release_nonreentrant_lock_eq,
     bind_def, ignore_bind_def, return_def, raise_def,
     check_not_static_def, assert_def, check_def, AllCaseEqs()] >>
  gvs[storage_trace_backends_well_formed_append,
      storage_trace_backends_well_formed_def]
QED

Theorem optional_lock_observations:
  (lock_if_nr cx nr view st = (res,out) \/
   unlock_if_nr cx nr view st = (res,out)) /\
  storage_observations_ok cx H st.storage_trace /\
  (?sfx. selected = out.storage_trace ++ sfx) /\
  EVERY (\r. MEM r (FST H)) (storage_trace_regions selected) /\
  EVERY (\l. MEM l (SND H)) (storage_trace_locks selected) /\
  storage_roots_fit selected ==>
  storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >>
  `storage_trace_backends_well_formed cx (FST H) out.storage_trace <=>
   storage_trace_backends_well_formed cx (FST H) st.storage_trace` by
    metis_tac[optional_lock_backend_trace] >>
  gvs[storage_observations_ok_def, listTheory.EVERY_APPEND]
QED

Theorem lock_if_nr_finite_prefix:
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st.storage_trace /\
  (?sfx. selected = out.storage_trace ++ sfx) /\
  EVERY (\r. MEM r (FST H)) (storage_trace_regions selected) /\
  EVERY (\l. MEM l (SND H)) (storage_trace_locks selected) /\
  storage_roots_fit selected /\ lock_if_nr cx nr view st = (res,out) ==>
  storage_well_formed_on cx out (FST H) /\
  storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >>
  `storage_observations_ok cx H out.storage_trace` by
    metis_tac[optional_lock_observations] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  drule_at (Pat `lock_if_nr _ _ _ _ = _`) lock_if_nr_storage >>
  disch_then (qspecl_then [`out.storage_trace`,`H`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >>
    drule_all explicit_lock_observed >> simp[])) >> simp[]
QED

Theorem unlock_if_nr_finite_prefix:
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st.storage_trace /\
  (?sfx. selected = out.storage_trace ++ sfx) /\
  EVERY (\r. MEM r (FST H)) (storage_trace_regions selected) /\
  EVERY (\l. MEM l (SND H)) (storage_trace_locks selected) /\
  storage_roots_fit selected /\ unlock_if_nr cx nr view st = (res,out) ==>
  storage_well_formed_on cx out (FST H) /\
  storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >>
  `storage_observations_ok cx H out.storage_trace` by
    metis_tac[optional_lock_observations] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule explicit_unlock_storage >>
  conj_tac >- metis_tac[unlock_if_nr_storage] >> metis_tac[]
QED

(* Term syntax shared by the entry wrappers; no new logical definition. *)
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

Theorem optional_lock_outcomes:
  (lock_if_nr cx nr view st = (res,out) \/
   unlock_if_nr cx nr view st = (res,out)) ==>
  out.outcomes = st.outcomes
Proof
  Cases_on `cx.nonreentrant_slot` >>
  rw[lock_if_nr_def, unlock_if_nr_def,
     acquire_nonreentrant_lock_eq, release_nonreentrant_lock_eq,
     bind_def, ignore_bind_def, return_def, raise_def,
     check_not_static_def, assert_def, check_def, AllCaseEqs()] >> gvs[]
QED

Theorem send_call_value_trace_outcomes:
  send_call_value mut cx st = (res,out) ==>
  out.storage_trace = st.storage_trace /\ out.outcomes = st.outcomes
Proof
  simp[send_call_value_def, transfer_value_def, COND_RATOR, LET_RATOR,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[COND_RATOR, LET_RATOR, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def,
      vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def,
      AllCaseEqs()]
QED


(* Exact entry syntax from call_external_function_trace, shared by the explicit
   and generated getter entry proofs. *)
val external_entry_term = ``
  do send_call_value mut cx;
     dvs <- eval_external_defaults cx (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts);
     case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
       NONE => raise (Error (RuntimeError "call bind_arguments"))
     | SOME scope => do set_scopes [scope]; lock_if_nr cx nr (is_view_mut mut);
                        eval_stmts cx body od
  od``;
val external_initial_term = ``
  initial_state am [FEMPTY] with
    <|outcomes := SOME os; requests := []; gas_obs := gs; storage_trace := []|>``;

Theorem external_function_trace_observations:
  ~cx.in_deploy /\
  EVERY (\r. MEM r (FST H)) (storage_trace_regions obs) /\
  EVERY (\l. MEM l (SND H)) (storage_trace_locks obs) /\
  storage_roots_fit obs /\
  (!rr rt.
    (^external_entry_term) (^external_initial_term) = (rr,rt) /\
    (?sfx. obs = rt.storage_trace ++ sfx) ==>
    storage_observations_ok cx H rt.storage_trace) /\
  call_external_function_trace (SOME os) gs am cx nr mut ts mods args dflts vals body ret =
    (res,am',rqs,obs) ==>
  storage_observations_ok cx H obs
Proof
  strip_tac >>
  qpat_x_assum `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [call_external_function_trace_def, LET_THM] >>
  asm_rewrite_tac[] >>
  IF_CASES_TAC >- (strip_tac >> gvs[storage_observations_ok_def,
    storage_trace_regions_def, storage_trace_locks_def, storage_roots_fit_def,
    storage_trace_backends_well_formed_def]) >>
  simp_tac bool_ss [pairTheory.pair_case_def, pairTheory.UNCURRY_DEF,
                    optionTheory.option_case_def] >>
  qmatch_goalsub_abbrev_tac `entry (initial_state am [FEMPTY] with
    <|outcomes := SOME os; requests := []; gas_obs := gs; storage_trace := []|>)` >>
  qabbrev_tac `st0 = initial_state am [FEMPTY] with
    <|outcomes := SOME os; requests := []; gas_obs := gs; storage_trace := []|>` >>
  `!rr rt. entry st0 = (rr,rt) /\ (?sfx. obs = rt.storage_trace ++ sfx) ==>
    storage_observations_ok cx H rt.storage_trace` by
    (unabbrev_all_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `entry st0` >> rename1 `entry st0 = (br,sb)` >>
  `!ur us. unlock_if_nr cx nr (is_view_mut mut) sb = (ur,us) /\
           obs = us.storage_trace ==> storage_observations_ok cx H obs` by
    (rpt strip_tac >>
     `?tail. us.storage_trace = sb.storage_trace ++ tail` by
       metis_tac[storage_trace_frame_prefix, storage_trace_frame_optional_locks] >>
     `storage_observations_ok cx H sb.storage_trace` by
       (first_x_assum irule >>
        (conj_tac >- (qexists `tail` >> fs[])) >> qexists `br` >> simp[]) >>
     rpt (qpat_x_assum `!rr rt. _` kall_tac) >>
     metis_tac[optional_lock_observations, listTheory.APPEND_NIL]) >>
  Cases_on `br` >> simp_tac bool_ss []
  >- (Cases_on `unlock_if_nr cx nr (is_view_mut mut) sb` >> Cases_on `q` >>
      simp_tac bool_ss [pairTheory.pair_case_def, sumTheory.sum_case_def,
                       pairTheory.UNCURRY_DEF] >> strip_tac >> gvs[] >> metis_tac[]) >>
  rename1 `INR ex` >> Cases_on `ex` >>
  simp_tac (srw_ss()) [Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def",
                       pairTheory.UNCURRY_DEF]
  >~ [`entry st0 = (INR (ReturnException rv),sb)`] >-
    (Cases_on `unlock_if_nr cx nr (is_view_mut mut) sb` >> Cases_on `q` >>
     simp_tac (srw_ss()) [Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def",
                         pairTheory.UNCURRY_DEF]
     >- (Cases_on `evaluate_type (type_env_all_modules mods) ret` >>
         simp_tac (srw_ss()) [] >- (strip_tac >> gvs[] >> metis_tac[]) >>
         rename1 `safe_cast tv rv` >> Cases_on `safe_cast tv rv` >>
         simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >> metis_tac[]) >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `!rr rt. entry st0 = _ /\ _ ==> _` irule >>
  simp[] >> qexists `[]` >> simp[]
QED
