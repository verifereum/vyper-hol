(* TOP-LEVEL: fn_entry_run_create_probe_reconstruct, fn_entry_run_probe_replay.
 * Helpers lift the canonical cut through actual setup, defaults and body. *)
Theory sourceCallCountEntryReplay
Ancestors vyperState[qualified,ignore_grammar]
  sourceCallCount vyperInterpreter vyperEvalOutcomeReplace
  vyperEvalOutcomeSuffix vyperStorageTrace vyperRuntimeAccounts vyperCallOutcome
  finite_map list option pair
Libs BasicProvers

(* Reuse the supplier's expanded contract without adding a logical constant. *)
val _ = let
  val ([f,g,s,os], rule) = strip_forall (concl source_replay_cut_bind_reachable)
  val cut = fst (dest_conj (fst (dest_imp rule)))
in overload_on ("source_wrapper_cut_at", list_mk_abs ([f,s,os], cut)) end;

Theorem outcomes_replace_entry_prefix[local]:
  (!mut cx s oc.
    send_call_value mut cx (s with outcomes := oc) =
      (FST (send_call_value mut cx s),
       SND (send_call_value mut cx s) with outcomes := oc)) /\
  (!cx nr view s oc.
    lock_if_nr cx nr view (s with outcomes := oc) =
      (FST (lock_if_nr cx nr view s),
       SND (lock_if_nr cx nr view s) with outcomes := oc))
Proof
  conj_tac
  >- (ntac 2 gen_tac >>
      simp_tac bool_ss [send_call_value_def, LET_THM] >>
      IF_CASES_TAC >- simp[vyperStateTheory.return_def] >>
      irule outcomes_replace_ignore_bind >> simp[outcomes_replace_basic] >>
      simp_tac bool_ss [transfer_value_def] >>
      IF_CASES_TAC >- simp[vyperStateTheory.return_def] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_basic] >>
      gen_tac >> simp_tac bool_ss [LET_THM] >>
      irule outcomes_replace_ignore_bind >> simp[outcomes_replace_basic] >>
      irule outcomes_replace_ignore_bind >>
      simp[outcomes_replace_basic]) >>
  ntac 3 gen_tac >> Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
  asm_simp_tac (srw_ss()) [lock_if_nr_def, option_CLAUSES,
    vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  irule outcomes_replace_ignore_bind >> conj_tac
  >- (simp_tac bool_ss [acquire_nonreentrant_lock_def] >>
      irule outcomes_replace_ignore_bind >>
      simp[vyperStateTheory.record_storage_event_def,
        vyperStateTheory.return_def] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_basic] >>
      gen_tac >> simp_tac bool_ss [LET_THM] >>
      IF_CASES_TAC >- simp[vyperStateTheory.raise_def] >>
      IF_CASES_TAC >> simp[outcomes_replace_basic,
        vyperStateTheory.return_def]) >>
  Cases_on `view` >> simp[vyperStateTheory.return_def,
    vyperStateTheory.check_not_static_def, outcomes_replace_basic]
QED

Theorem source_entry_body_probe_cut[local]:
  !cx nr mut tenv args vals dvs fbody s os.
    source_wrapper_cut_at
      (case bind_arguments tenv args (vals ++ dvs) of
         NONE => raise (Error (RuntimeError "call bind_arguments"))
       | SOME env => do
           set_scopes [env]; lock_if_nr cx nr (is_view_mut mut);
           eval_stmts cx fbody
         od) s os
Proof
  rpt gen_tac >> Cases_on `bind_arguments tenv args (vals ++ dvs)`
  >- (asm_simp_tac (srw_ss()) [vyperStateTheory.raise_def,
        Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
      rpt strip_tac >> disj1_tac >> qexists_tac `os` >>
      gvs[Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  rename1 `bind_arguments tenv args (vals ++ dvs) = SOME env` >>
  asm_simp_tac bool_ss [option_CLAUSES] >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) (s with scopes := [env])` >>
  rename1 `lock_if_nr cx nr (is_view_mut mut) (s with scopes := [env]) =
    (rl,sl)` >>
  `!xs. lock_if_nr cx nr (is_view_mut mut)
          ((s with outcomes := SOME xs) with scopes := [env]) =
          (rl,sl with outcomes := SOME xs)` by
    (gen_tac >>
     `((s with outcomes := SOME xs) with scopes := [env]) =
       ((s with scopes := [env]) with outcomes := SOME xs)` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     pop_assum SUBST1_TAC >>
     simp[outcomes_replace_entry_prefix,
       Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  reverse (Cases_on `rl`)
  >- (asm_simp_tac (srw_ss()) [vyperStateTheory.ignore_bind_def,
        vyperStateTheory.bind_def, vyperStateTheory.set_scopes_def,
        vyperStateTheory.return_def,
        Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
      rpt strip_tac >> disj1_tac >> qexists_tac `os` >>
      gvs[Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  qspecl_then [`cx`, `fbody`, `sl`, `os`] mp_tac
    (List.nth (CONJUNCTS eval_outcome_probe_cut_mutual, 1)) >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
    vyperStateTheory.set_scopes_def, vyperStateTheory.return_def,
    Excl "lock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem source_external_defaults_probe_cut[local]:
  !cx es s os. source_wrapper_cut_at (eval_external_defaults cx es) s os
Proof
  rpt gen_tac >>
  qspecl_then [`\(r,t). (r,t with scopes := s.scopes)`,
    `eval_exprs cx es`, `s with scopes := [FEMPTY]`, `os`]
    mp_tac source_replay_cut_postprocess >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
          simp[vyperStateTheory.erase_storage_trace_def] >> metis_tac[]) >>
      conj_tac >> pairarg_tac >> simp[]) >>
  simp_tac bool_ss [eval_outcome_probe_cut_mutual] >>
  simp[eval_external_defaults_run, LET_THM,
    vyperStateTheory.erase_storage_trace_def, pairTheory.pair_CASE_def,
    AllCaseEqs()]
QED

Theorem source_entry_body_support[local]:
  !cx nr mut tenv args vals dvs fbody f.
    f = (case bind_arguments tenv args (vals ++ dvs) of
           NONE => raise (Error (RuntimeError "call bind_arguments"))
         | SOME env => do
             set_scopes [env]; lock_if_nr cx nr (is_view_mut mut);
             eval_stmts cx fbody
           od) ==>
    outcomes_suffix f /\ storage_trace_frame f /\
    (!s r t. accounts_runtime_well_typed s.accounts /\
       s.outcomes = SOME [] /\ f s = (r,t) ==>
       accounts_runtime_well_typed t.accounts /\ t.outcomes = SOME [] /\
       r <> INR (Error (RuntimeError "create outcome accounts")))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  Cases_on `bind_arguments tenv args (vals ++ dvs)`
  >- (simp[storage_trace_frame_raise, vyperStateTheory.raise_def] >>
      irule outcomes_suffix_frame >> simp[]) >>
  asm_simp_tac bool_ss [option_CLAUSES] >> conj_tac
  >- (rewrite_tac[vyperStateTheory.ignore_bind_def] >>
      MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
      >- (irule outcomes_suffix_frame >> simp[]) >>
      rpt gen_tac >> strip_tac >> BETA_TAC >>
      MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
      >- (irule outcomes_suffix_frame >> Cases_on `nr` >>
          Cases_on `cx.nonreentrant_slot` >> simp[lock_if_nr_def]) >>
      rpt strip_tac >> simp[eval_outcomes_suffix_with_results]) >>
  conj_tac
  >- (irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates,
        Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_optional_locks, evaluate_storage_trace_frame,
        Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  rpt gen_tac >> strip_tac >>
  gvs[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
    vyperStateTheory.set_scopes_def, vyperStateTheory.return_def,
    AllCaseEqs(), Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  imp_res_tac (List.nth (CONJUNCTS source_exhausted_internal_call_safety, 0)) >>
  imp_res_tac (List.nth (CONJUNCTS source_exhausted_eval_safety_mutual, 1)) >>
  gvs[Excl "lock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem source_entry_defaults_body_probe_cut[local]:
  !cx nr mut tenv args vals es fbody s os.
    source_wrapper_cut_at
      (do dvs <- eval_external_defaults cx es;
          case bind_arguments tenv args (vals ++ dvs) of
            NONE => raise (Error (RuntimeError "call bind_arguments"))
          | SOME env => do
              set_scopes [env]; lock_if_nr cx nr (is_view_mut mut);
              eval_stmts cx fbody
            od
       od) s os
Proof
  rpt gen_tac >> MATCH_MP_TAC source_replay_cut_bind_reachable >>
  conj_tac >- simp[source_external_defaults_probe_cut] >>
  conj_tac
  >- (ntac 3 gen_tac >> strip_tac >> BETA_TAC >>
      MATCH_ACCEPT_TAC source_entry_body_probe_cut) >>
  qx_gen_tac `dvs` >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `outcomes_suffix continuation` >>
  qspecl_then [`cx`, `nr`, `mut`, `tenv`, `args`, `vals`, `dvs`, `fbody`,
    `continuation`] mp_tac source_entry_body_support >>
  simp[Abbr `continuation`, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  strip_tac >> gvs[Excl "lock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem source_entry_core_probe_cut[local]:
  !cx nr mut tenv args vals es fbody s os.
    source_wrapper_cut_at
      (do send_call_value mut cx;
          dvs <- eval_external_defaults cx es;
          case bind_arguments tenv args (vals ++ dvs) of
            NONE => raise (Error (RuntimeError "call bind_arguments"))
          | SOME env => do
              set_scopes [env]; lock_if_nr cx nr (is_view_mut mut);
              eval_stmts cx fbody
            od
       od) s os
Proof
  rpt gen_tac >> Cases_on `send_call_value mut cx s` >>
  rename1 `send_call_value mut cx s = (rs,ss)` >>
  `!xs. send_call_value mut cx (s with outcomes := SOME xs) =
          (rs,ss with outcomes := SOME xs)` by
    simp[outcomes_replace_entry_prefix] >>
  reverse (Cases_on `rs`)
  >- (asm_simp_tac (srw_ss()) [vyperStateTheory.ignore_bind_def,
        vyperStateTheory.bind_def,
        Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
      rpt strip_tac >> disj1_tac >> qexists_tac `os` >>
      gvs[Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  qspecl_then [`cx`, `nr`, `mut`, `tenv`, `args`, `vals`, `es`, `fbody`,
    `ss`, `os`] mp_tac source_entry_defaults_body_probe_cut >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
    Excl "lock_if_nr_def", Excl "is_view_mut_def"]
QED

(* TOP-LEVEL: replay projects only the ghost storage trace. *)
Theorem fn_entry_run_probe_replay:
  !os gobs am cx nr mut mods args dflts vals fbody res_p st_p.
    fn_entry_run (os ++ [probe_failed_outcome]) gobs am cx nr mut mods
      args dflts vals fbody = SOME (res_p,st_p) /\
    st_p.outcomes = SOME [] ==>
    OPTION_MAP (\(r,s). (r,erase_storage_trace s))
      (fn_entry_run os gobs am cx nr mut mods args dflts vals fbody) =
    OPTION_MAP (\(r,s). (r,erase_storage_trace s))
      (fn_entry_run
      (os ++ [case fn_entry_run (os ++ [empty_failed_outcome]) gobs am cx
                     nr mut mods args dflts vals fbody of
        SOME (res_e,_) =>
          if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
             res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
             ~NULL st_p.requests
          then failed_outcome (LAST st_p.requests)
          else empty_failed_outcome
      | NONE => empty_failed_outcome])
      gobs am cx nr mut mods args dflts vals fbody)
Proof
  rpt gen_tac >> simp_tac bool_ss [fn_entry_run_def, LET_THM] >>
  IF_CASES_TAC >> simp_tac (srw_ss())
    [Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  Cases_on `if cx.in_deploy then
    evaluate_all_constants cx am cx.txn.target mods else SOME am` >>
  simp_tac (srw_ss()) [Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  rename1 `(if cx.in_deploy then
    evaluate_all_constants cx am cx.txn.target mods else SOME am) = SOME am_c` >>
  qmatch_goalsub_abbrev_tac `entry_core (initial_state am_c [FEMPTY] with
    <|outcomes := SOME (os ++ [probe_failed_outcome]); requests := [];
      gas_obs := gobs|>)` >> strip_tac >>
  `source_wrapper_cut_at entry_core
    (initial_state am_c [FEMPTY] with <|requests := []; gas_obs := gobs|>) os` by
    (qunabbrev_tac `entry_core` >> BETA_TAC >>
     qspecl_then [`cx`, `nr`, `mut`, `type_env_all_modules mods`, `args`, `vals`,
       `DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts`, `fbody`,
       `initial_state am_c [FEMPTY] with <|requests := []; gas_obs := gobs|>`,
       `os`] (ACCEPT_TAC o BETA_RULE) source_entry_core_probe_cut) >>
  pop_assum (qspecl_then [`res_p`, `st_p`] mp_tac) >>
  simp[initial_state_def] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[SF CONJ_ss] >> gvs[pairTheory.pair_CASE_def]
QED

(* TOP-LEVEL: CREATE reconstruction retains the complete result and state. *)
Theorem fn_entry_run_create_probe_reconstruct:
  !os gobs am cx nr mut mods args dflts vals fbody res_e st_e st_p.
    fn_entry_run (os ++ [probe_failed_outcome]) gobs am cx nr mut mods
      args dflts vals fbody =
      SOME (INR (Error (RuntimeError "create outcome accounts")),st_p) /\
    st_p.outcomes = SOME [] /\ ~NULL st_p.requests /\
    fn_entry_run (os ++ [empty_failed_outcome]) gobs am cx nr mut mods
      args dflts vals fbody = SOME (res_e,st_e) /\
    res_e <> INR (Error (RuntimeError "create outcome accounts")) ==>
    fn_entry_run os gobs am cx nr mut mods args dflts vals fbody =
    fn_entry_run (os ++ [failed_outcome (LAST st_p.requests)]) gobs am cx
      nr mut mods args dflts vals fbody
Proof
  rpt gen_tac >> simp_tac bool_ss [fn_entry_run_def, LET_THM] >>
  IF_CASES_TAC >> simp_tac (srw_ss())
    [Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  Cases_on `if cx.in_deploy then
    evaluate_all_constants cx am cx.txn.target mods else SOME am` >>
  simp_tac (srw_ss()) [Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  rename1 `(if cx.in_deploy then
    evaluate_all_constants cx am cx.txn.target mods else SOME am) = SOME am_c` >>
  qmatch_goalsub_abbrev_tac `entry_core (initial_state am_c [FEMPTY] with
    <|outcomes := SOME (os ++ [probe_failed_outcome]); requests := [];
      gas_obs := gobs|>)` >> strip_tac >>
  `source_wrapper_cut_at entry_core
    (initial_state am_c [FEMPTY] with <|requests := []; gas_obs := gobs|>) os` by
    (qunabbrev_tac `entry_core` >> BETA_TAC >>
     qspecl_then [`cx`, `nr`, `mut`, `type_env_all_modules mods`, `args`, `vals`,
       `DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts`, `fbody`,
       `initial_state am_c [FEMPTY] with <|requests := []; gas_obs := gobs|>`,
       `os`] (ACCEPT_TAC o BETA_RULE) source_entry_core_probe_cut) >>
  pop_assum (qspecl_then
    [`INR (Error (RuntimeError "create outcome accounts"))`, `st_p`] mp_tac) >>
  simp[initial_state_def] >> strip_tac >> gvs[]
QED

Theorem source_entry_core_outcomes_suffix[local]:
  !cx nr mut tenv args vals es fbody.
    outcomes_suffix
      (do send_call_value mut cx;
          dvs <- eval_external_defaults cx es;
          case bind_arguments tenv args (vals ++ dvs) of
            NONE => raise (Error (RuntimeError "call bind_arguments"))
          | SOME env => do
              set_scopes [env]; lock_if_nr cx nr (is_view_mut mut);
              eval_stmts cx fbody
            od
       od)
Proof
  rpt gen_tac >> rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
  >- (irule outcomes_suffix_frame >> simp[send_call_value_def]) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
  >- (rewrite_tac[eval_external_defaults_def] >>
      MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
      >- (irule outcomes_suffix_frame >> simp[]) >>
      rpt gen_tac >> strip_tac >> BETA_TAC >>
      MATCH_MP_TAC outcomes_suffix_finally >> conj_tac
      >- (rewrite_tac[vyperStateTheory.ignore_bind_def] >>
          MATCH_MP_TAC outcomes_suffix_bind_guarded >> conj_tac
          >- (irule outcomes_suffix_frame >> simp[]) >>
          rpt strip_tac >> simp[eval_outcomes_suffix_with_results]) >>
      irule outcomes_suffix_frame >> simp[]) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  rename1 `eval_external_defaults cx es _ = (INL dvs,_)` >>
  qmatch_goalsub_abbrev_tac `outcomes_suffix continuation` >>
  qspecl_then [`cx`, `nr`, `mut`, `tenv`, `args`, `vals`, `dvs`, `fbody`,
    `continuation`] mp_tac source_entry_body_support >>
  simp[Abbr `continuation`, vyperStateTheory.ignore_bind_def,
    Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  strip_tac >> gvs[vyperStateTheory.ignore_bind_def,
    Excl "lock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem fn_entry_run_selection_invariant:
  !os os' gobs am cx nr mut mods args dflts vals fbody.
    IS_SOME (fn_entry_run os gobs am cx nr mut mods args dflts vals fbody) =
    IS_SOME (fn_entry_run os' gobs am cx nr mut mods args dflts vals fbody)
Proof
  rpt gen_tac >> simp_tac bool_ss [fn_entry_run_def, LET_THM] >>
  IF_CASES_TAC >> simp_tac (srw_ss())
    [Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  Cases_on `if cx.in_deploy then
    evaluate_all_constants cx am cx.txn.target mods else SOME am` >>
  simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem fn_entry_run_outcomes_suffix:
  !os gobs am cx nr mut mods args dflts vals fbody res st.
    fn_entry_run os gobs am cx nr mut mods args dflts vals fbody = SOME (res,st) ==>
    outcome_suffix (SOME os) st.outcomes
Proof
  rpt gen_tac >> simp_tac bool_ss [fn_entry_run_def, LET_THM] >>
  IF_CASES_TAC >> simp_tac (srw_ss())
    [Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  Cases_on `if cx.in_deploy then
    evaluate_all_constants cx am cx.txn.target mods else SOME am` >>
  simp_tac (srw_ss()) [Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  strip_tac >> qmatch_assum_abbrev_tac `entry_core entry_seed = (res,st)` >>
  `outcomes_suffix entry_core` by
    (qunabbrev_tac `entry_core` >> BETA_TAC >>
     MATCH_ACCEPT_TAC source_entry_core_outcomes_suffix) >>
  drule_all outcomes_suffix_result >> simp[Abbr `entry_seed`]
QED

val _ = clear_overloads_on "source_wrapper_cut_at";
