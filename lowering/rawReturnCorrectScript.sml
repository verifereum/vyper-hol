Theory rawReturnCorrect
Ancestors
  rawReturnHalt rawReturnValue vyperLoweringCorrect loweringHalt
  fragExec e2eDefs valueEncoding vyperTyping

Theorem external_raw_halt_unlock_result[local]:
  !func cenv cx es es' s ss nr nkey iv tops tx srcs exps layouts v bs ret.
    lookup_raw_return_or_F (NONE:num option) tx.function_name External tops /\
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    state_rel func cenv cx es s /\
    (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ()) es = (INL (), es') /\
    raw_return_bytes v = SOME bs /\ ss.vs_returndata = bs /\
    ss.vs_accounts = s.vs_accounts /\
    ss.vs_transient = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s).vs_transient /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
    external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es'), es'.requests)
      (Halt ss)
Proof
  rpt strip_tac >>
  `ss.vs_transient =
     (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
      else s.vs_transient)` by
    (Cases_on `nr /\ ~iv` >> fs[]) >>
  `accounts_agree (initial_evaluation_context srcs layouts tx NONE)
     (finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es')).accounts ss.vs_accounts /\
   transient_agree (initial_evaluation_context srcs layouts tx NONE)
     (finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es')).tStorage ss.vs_transient /\
   logs_correspond (compiled_event_info tops) (type_env tops) tx.target
     (finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es')).logs ss.vs_logs /\
   LIST_REL (request_agree (initial_evaluation_context srcs layouts tx NONE))
     es'.requests ss.vs_requests` by
    metis_tac[external_halt_success_unlock] >>
  gvs[external_call_result_rel_def, tx_return_bytes_def,
      vyperInterpreterTheory.abstract_machine_from_state_def]
QED

(* A raw return reads the value's length prefix and payload directly.
   The memory bound describes the representation at the return point. *)
Theorem external_return_raw_unlock_result_rel:
  !ctx op prim ei msz nr nkey ut iv st x st' func cenv cx es es' ret tv v0 v
     tops tx srcs exps layouts Q.
    lookup_raw_return_or_F (NONE : num option) tx.function_name External tops /\
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) prim T ei msz nr nkey ut iv st =
      (x, st') /\
    (nr /\ ~iv ==> ut) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ()) es = (INL (), es') /\
    evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    is_bytestring_type ret ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           (?p. eval_operand op s = SOME p /\
                val_in_memory tv v0 (w2n p) s.vs_memory /\
                w2n p + val_footprint tv v0 <= dimword (:256)))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es'),
          es'.requests))
Proof
  rpt strip_tac >>
  `v = v0` by metis_tac[safe_cast_some_eq] >>
  `value_has_type tv v0` by metis_tac[safe_cast_result_well_typed] >>
  irule frag_exec_pointwise >>
  gen_tac >> disch_then (strip_assume_tac o BETA_RULE) >>
  drule_all raw_return_value_read >> strip_tac >>
  irule compile_external_return_raw_unlock_frag >>
  qexistsl_tac [`bs`, `ei`, `iv`, `msz`, `nkey`, `nr`, `op`, `p`,
               `prim`, `ut`, `x`] >>
  simp[] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[external_raw_halt_unlock_result]
QED
