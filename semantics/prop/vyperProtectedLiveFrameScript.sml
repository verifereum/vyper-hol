(* Protect a named immutable cell along a closed set of internal calls. *)
Theory vyperProtectedLiveFrame
Ancestors
  list alist finite_map vyperState vyperContext vyperInterpreter
  vyperTypeSystem vyperTypeCallGraph vyperBareGlobalName
  vyperRuntimeWriteSafety vyperCallOutcomeFrame
  vyperLiveObservationFrame vyperGuardedCellMutations

val guard = ``runtime_write_root (\s id. (s,id) <> (sid,nm))``;
val observes_initial = ``\imms. (case ALOOKUP imms cx.txn.target of
    NONE => NONE
  | SOME store => FLOOKUP (get_source_immutables sid store) nm) =
  lookup_immutable cx st sid nm``;

Theorem live_protected_evaluation_frames:
  (!src fn ts mut nr args ds rt b.
    P (src,fn) /\ get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,ds,rt,b) ==>
    EVERY (expr_writes_ok ^guard) ds /\ stmts_writes_ok ^guard b /\
    EVERY P (function_int_calls ds b)) ==>
  (!es st res st'.
    EVERY (expr_writes_ok ^guard) es /\ EVERY P (int_calls_exprs es) /\
    eval_exprs cx es st = (res,st') ==>
    lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!ss st res st'.
    stmts_writes_ok ^guard ss /\ EVERY P (int_calls_stmts ss) /\
    eval_stmts cx ss st = (res,st') ==>
    lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm)
Proof
  strip_tac >> conj_tac >> map_every qx_gen_tac [`items`,`st`,`res`,`st'`] >>
  strip_tac >>
  mp_tac (Q.INST [`M` |-> `get_module_code cx`, `deploy` |-> `cx.in_deploy`,
                  `addr` |-> `cx.txn.target`, `G` |-> `^guard`,
                  `obs` |-> `^observes_initial`]
           (BETA_RULE live_guarded_list_observation_frames)) >>
  simp_tac bool_ss [] >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >> drule_all runtime_guarded_cell_mutations >>
     simp[state_rel_frame_result, lookup_immutable_def] >> metis_tac[])) >>
  fs[state_rel_frame_result, lookup_immutable_def] >> metis_tac[]
QED
