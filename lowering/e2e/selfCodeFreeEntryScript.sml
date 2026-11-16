(* Entry boundaries for transaction-code independence. *)
Theory selfCodeFreeEntry
Ancestors
  selfCodeFreeInterpreter selfCodeFreeConstants selfCodeFreeContext
  selfCodeFreeInvariant selfCodeFreeSyntax vyperInterpreter vyperContext
  vyperStorageTrace

val _ = Parse.hide "body";

Theorem call_external_function_trace_self_code_free:
  self_code_free_context cx /\
  ~supported_exprs_exists is_self_code dflts /\
  ~supported_stmts_expr_exists is_self_code body /\
  (cx.in_deploy ==>
    evaluate_module_constants_trace (cx with txn := (cx.txn with code := c)) am
      cx.txn.target (constants_order mods) =
    evaluate_module_constants_trace cx am cx.txn.target (constants_order mods)) ==>
  call_external_function_trace orc gobs am
    (cx with txn := (cx.txn with code := c)) nr mut ts mods args dflts vals body ret =
  call_external_function_trace orc gobs am cx nr mut ts mods args dflts vals body ret
Proof
  strip_tac >>
  `eval_stmts (cx with txn := (cx.txn with code := c)) body =
   eval_stmts cx body` by metis_tac[eval_stmts_self_code_free] >>
  `!n. eval_exprs (cx with txn := (cx.txn with code := c)) (DROP n dflts) =
       eval_exprs cx (DROP n dflts)` by
    metis_tac[eval_exprs_self_code_free, supported_exprs_exclusion_DROP] >>
  Cases_on `cx.in_deploy` >>
  simp[call_external_function_trace_def, eval_external_defaults_def,
       send_call_value_def, lock_if_nr_def, unlock_if_nr_def, vyperStateTheory.check_not_static_def]
QED

Theorem call_external_function_self_code_free:
  self_code_free_context cx /\
  ~supported_exprs_exists is_self_code dflts /\
  ~supported_stmts_expr_exists is_self_code body /\
  (cx.in_deploy ==>
    evaluate_all_constants (cx with txn := (cx.txn with code := c)) am
      cx.txn.target mods = evaluate_all_constants cx am cx.txn.target mods) ==>
  call_external_function orc gobs am
    (cx with txn := (cx.txn with code := c)) nr mut ts mods args dflts vals body ret =
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret
Proof
  strip_tac >>
  `eval_stmts (cx with txn := (cx.txn with code := c)) body =
   eval_stmts cx body` by metis_tac[eval_stmts_self_code_free] >>
  `!n. eval_exprs (cx with txn := (cx.txn with code := c)) (DROP n dflts) =
       eval_exprs cx (DROP n dflts)` by
    metis_tac[eval_exprs_self_code_free, supported_exprs_exclusion_DROP] >>
  reverse (Cases_on `cx.in_deploy`)
  >- (simp[call_external_function_def, call_external_function_trace_def,
           eval_external_defaults_def, send_call_value_def, lock_if_nr_def,
           unlock_if_nr_def, vyperStateTheory.check_not_static_def]) >>
  gvs[evaluate_all_constants_def, evaluate_module_constants_def] >>
  Cases_on `evaluate_module_constants_trace cx am cx.txn.target (constants_order mods)` >>
  Cases_on `evaluate_module_constants_trace (cx with txn := (cx.txn with code := c)) am cx.txn.target (constants_order mods)` >>
  gvs[] >>
  simp[call_external_function_def, call_external_function_trace_def,
       eval_external_defaults_def, send_call_value_def, lock_if_nr_def,
       unlock_if_nr_def, vyperStateTheory.check_not_static_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `q` >> simp[] >>
  rename1 `initial_state am_c [FEMPTY]` >>
  qmatch_goalsub_abbrev_tac
    `entry (initial_state am_c [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := r'|>)` >>
  `storage_trace_frame entry` by
    (simp[Abbr `entry`] >>
     irule (SRULE [LET_THM, send_call_value_def, eval_external_defaults_def, lock_if_nr_def,
                   vyperStateTheory.check_not_static_def]
                  (Q.INST [`view` |-> `mut = View \/ mut = Pure`]
                    storage_trace_frame_external_entry))) >>
  drule (iffLR storage_trace_frame_def) >>
  disch_then (qspec_then
    `initial_state am_c [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs|>`
    (fn th => once_rewrite_tac[SRULE [] th])) >>
  qpat_abbrev_tac `unlock =
    if nr /\ mut <> View /\ mut <> Pure then
      case cx.nonreentrant_slot of NONE => return ()
      | SOME slot => release_nonreentrant_lock cx.txn.target slot
    else return ()` >>
  `storage_trace_frame unlock` by
    (simp[Abbr `unlock`] >>
     irule (SRULE [unlock_if_nr_def]
       (Q.INST [`view` |-> `mut = View \/ mut = Pure`]
         (cj 2 storage_trace_frame_optional_locks)))) >>
  drule (iffLR storage_trace_frame_action) >> disch_then assume_tac >>
  Cases_on `entry (initial_state am_c [FEMPTY] with
    <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|>)` >>
  rename1 `(_, st)` >>
  simp[] >>
  namedCases_on `q` ["v", "ex"]
  >- (Cases_on `unlock st` >> rename1 `(res, us)` >> Cases_on `res` >>
      simp[abstract_machine_from_state_storage_trace]) >>
  Cases_on `ex` >> simp[abstract_machine_from_state_storage_trace] >>
  Cases_on `unlock st` >> rename1 `(res, us)` >> Cases_on `res` >>
  simp[abstract_machine_from_state_storage_trace] >>
  Cases_on `evaluate_type (type_env_all_modules mods) ret` >> simp[] >>
  rename1 `safe_cast tv v` >> Cases_on `safe_cast tv v` >> simp[]
QED

Theorem singleton_sources_self_code_free:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  ~program_reads_self_code tops ==> self_code_free_context cx
Proof
  simp[self_code_free_context_def, get_module_code_def] >>
  strip_tac >> Cases_on `sid` >> simp[] >> metis_tac[]
QED

Theorem lookup_exported_function_txn_code[simp]:
  lookup_exported_function (cx with txn := (cx.txn with code := c)) am name =
  lookup_exported_function cx am name
Proof
  simp[lookup_exported_function_def]
QED
