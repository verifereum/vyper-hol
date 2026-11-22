(* Exact immutable-store frames for a guarded runtime entry. *)
Theory vyperLiveRuntimeEntryFrame
Ancestors
  list rich_list vyperState vyperInterpreter vyperTypeSystem
  vyperTypeCallGraph vyperRuntimeWriteSafety vyperCallOutcomeFrame
  vyperLiveObservationFrame vyperGuardedCellMutations
  vyperNonimmutablePlaceMutations vyperReadOnlyEval

val guard = ``runtime_write_root R``;
val same_initial_store = ``\(s:evaluation_state) (t:evaluation_state).
  s.immutables = initial_imms ==> t.immutables = initial_imms``;

Theorem live_runtime_entry_immutable_frames:
  ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
  (!sid fn ts mut nr args ds rt b.
    P (sid,fn) /\ get_module_code cx sid = SOME ts /\
    lookup_callable_function F fn ts = SOME (mut,nr,args,ds,rt,b) ==>
    EVERY (expr_writes_ok ^guard) ds /\ stmts_writes_ok ^guard b /\
    EVERY P (function_int_calls ds b)) /\
  EVERY (expr_writes_ok ^guard) ds /\ stmts_writes_ok ^guard b /\
  EVERY P (function_int_calls ds b) ==>
  (!n st r st'. eval_exprs cx (DROP n ds) st = (r,st') ==>
     st'.immutables = st.immutables) /\
  (!st r st'. eval_stmts cx b st = (r,st') ==>
     st'.immutables = st.immutables)
Proof
  strip_tac >>
  `!initial_imms.
     (!n. state_rel_frame ^same_initial_store (eval_exprs cx (DROP n ds))) /\
     state_rel_frame ^same_initial_store (eval_stmts cx b)` by
    (gen_tac >>
     mp_tac (Q.INST [`M` |-> `get_module_code cx`, `deploy` |-> `F`,
                     `addr` |-> `cx.txn.target`, `G` |-> `^guard`,
                     `obs` |-> `\i. i = initial_imms`]
              (BETA_RULE live_guarded_list_observation_frames_code)) >>
     simp_tac bool_ss [] >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >>
        rpt gen_tac >> strip_tac >>
        rename1 `get_module_code cy = get_module_code cx` >>
        `runtime_write_roots_resolve cy R` by
          fs[runtime_write_roots_resolve_def] >>
        drule_all runtime_resolved_target_not_immutable >> strip_tac >>
        drule nonimmutable_place_mutations_frame >>
        simp[state_rel_frame_result] >> metis_tac[])) >>
     strip_tac >>
     fs[function_int_calls_def, EVERY_APPEND,
        int_calls_exprs_FLAT_MAP, EVERY_FLAT, EVERY_MAP] >>
     simp[EVERY_DROP]) >>
  fs[state_rel_frame_result] >> metis_tac[]
QED
