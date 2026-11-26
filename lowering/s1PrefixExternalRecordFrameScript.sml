Theory s1PrefixExternalRecordFrame
Ancestors
  vyperInterpreter vyperState vyperCallOutcomeFrame finite_map list pair sum option
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = hide "body";

Theorem prefix_record_frame_bind[local]:
  state_rel_frame (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) f /\
  (!v. state_rel_frame (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) (g v)) ==>
  state_rel_frame (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace)
    (vyperState$bind f g)
Proof
  strip_tac >> irule state_rel_frame_bind_guarded >> simp[]
QED

Theorem prefix_record_frame_defaults[local]:
  state_rel_frame (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace)
    (eval_exprs cx ds) ==>
  state_rel_frame (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace)
    (eval_external_defaults cx ds)
Proof
  simp[state_rel_frame_def, eval_external_defaults_run] >> strip_tac >>
  qx_gen_tac `st` >>
  first_x_assum (qspec_then `st with scopes := [FEMPTY]` mp_tac) >>
  Cases_on `eval_exprs cx ds (st with scopes := [FEMPTY])` >> simp[]
QED

Theorem prefix_record_frame_entry[local]:
  state_rel_frame (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace)
    (eval_exprs cx ds) /\
  state_rel_frame (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace)
    (send_call_value mut cx) /\
  state_rel_frame (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace)
    (lock_if_nr cx nr (is_view_mut mut)) /\
  state_rel_frame (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace)
    (eval_stmts cx body) ==>
  state_rel_frame (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace)
    (do send_call_value mut cx;
        dvs <- eval_external_defaults cx ds;
        case binding dvs of
          NONE => raise (Error (RuntimeError "call bind_arguments"))
        | SOME env => do
            set_scopes [env]; lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body
          od
     od)
Proof
  strip_tac >> simp[ignore_bind_def, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  irule prefix_record_frame_bind >> simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  irule prefix_record_frame_bind >>
  reverse conj_tac >- (irule prefix_record_frame_defaults >> simp[]) >>
  qx_gen_tac `dvs` >> Cases_on `binding dvs` >>
  simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"]
  >- simp[state_rel_frame_def, raise_def] >>
  irule prefix_record_frame_bind >>
  reverse conj_tac >- simp[state_rel_frame_def, set_scopes_def, return_def] >>
  simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  irule prefix_record_frame_bind >> simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem prefix_function_trace_from_frames[local]:
  !P. P [] [] /\
  (!cx body. state_rel_frame
    (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) (eval_stmts cx body)) /\
  (!cx ds. state_rel_frame
    (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) (eval_exprs cx ds)) /\
  (!mut cx. state_rel_frame
    (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) (send_call_value mut cx)) /\
  (!cx nr view. state_rel_frame
    (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) (lock_if_nr cx nr view)) /\
  (!cx nr view. state_rel_frame
    (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) (unlock_if_nr cx nr view)) ==>
  !orc gs am cx nr mut (ts : toplevel list) mods args dflts vals body ret res am' rqs obs.
    call_external_function_trace orc gs am cx nr mut ts mods args dflts vals body ret =
      (res,am',rqs,obs) ==> ~cx.in_deploy ==> P rqs obs
Proof
  gen_tac >> strip_tac >> rpt gen_tac >> ntac 2 strip_tac >>
  qpat_x_assum `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [call_external_function_trace_def, LET_THM] >>
  asm_rewrite_tac[] >> IF_CASES_TAC >- simp[] >>
  simp_tac bool_ss [pairTheory.pair_case_def, pairTheory.UNCURRY_DEF,
                    optionTheory.option_case_def] >>
  qmatch_goalsub_abbrev_tac `entry (initial_state am [FEMPTY] with
    <|outcomes := orc; requests := []; gas_obs := gs; storage_trace := []|>)` >>
  qabbrev_tac `st0 = initial_state am [FEMPTY] with
    <|outcomes := orc; requests := []; gas_obs := gs; storage_trace := []|>` >>
  `state_rel_frame (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace)
     entry` by
    (simp[Abbr `entry`, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
     ho_match_mp_tac prefix_record_frame_entry >>
     simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  Cases_on `entry st0` >> rename1 `entry st0 = (br,sb)` >>
  `P sb.requests sb.storage_trace` by
    (drule_all state_rel_frame_at >> simp[Abbr `st0`]) >>
  `P (SND (unlock_if_nr cx nr (is_view_mut mut) sb)).requests
     (SND (unlock_if_nr cx nr (is_view_mut mut) sb)).storage_trace` by
    (qpat_assum `!cx nr view. state_rel_frame _ (unlock_if_nr cx nr view)`
       (qspecl_then [`cx`,`nr`,`is_view_mut mut`] mp_tac) >>
     pure_rewrite_tac[state_rel_frame_def] >>
     disch_then (qspec_then `sb` mp_tac) >> simp[]) >>
  Cases_on `unlock_if_nr cx nr (is_view_mut mut) sb` >>
  rename1 `unlock_if_nr cx nr (is_view_mut mut) sb = (ur,su)` >>
  gvs[Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  Cases_on `br` >> Cases_on `ur` >>
  simp[ELIM_UNCURRY, AllCaseEqs(), Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  rpt strip_tac >> gvs[]
QED

Theorem prefix_call_trace_from_frames:
  P [] [] /\
  (!cx body. state_rel_frame
    (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) (eval_stmts cx body)) /\
  (!cx ds. state_rel_frame
    (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) (eval_exprs cx ds)) /\
  (!mut cx. state_rel_frame
    (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) (send_call_value mut cx)) /\
  (!cx nr view. state_rel_frame
    (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) (lock_if_nr cx nr view)) /\
  (!cx nr view. state_rel_frame
    (\s t. P s.requests s.storage_trace ==> P t.requests t.storage_trace) (unlock_if_nr cx nr view)) /\
  call_external_trace orc gs am tx = (res,am',rqs,obs) ==>
  P rqs obs
Proof
  strip_tac >>
  qspec_then `P` mp_tac prefix_function_trace_from_frames >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >> strip_tac >>
  qpat_x_assum `call_external_trace _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once call_external_trace_def, LET_THM] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx
                      (find_function_module am tx.target tx.function_name)` >>
  `~cx.in_deploy` by simp[Abbr `cx`, initial_evaluation_context_def] >>
  ntac 3 (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  rename1 `lookup_exported_function cx am tx.function_name = SOME decl` >>
  PairCases_on `decl` >> simp[] >>
  BasicProvers.TOP_CASE_TAC >>
  rename1 `call_external_function_trace _ _ _ cx _ _ _ _ _ _ _ _ _ = (rr,rest)` >>
  PairCases_on `rest` >>
  rename1 `call_external_function_trace _ _ _ cx _ _ _ _ _ _ _ _ _ = (rr,ar,rs,os)` >>
  `P rs os` by (first_x_assum drule >> simp[]) >>
  Cases_on `rr` >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED
