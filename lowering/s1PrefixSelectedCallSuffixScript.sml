(* Align a selected bound call with the source body's trace, including unlock. *)
Theory s1PrefixSelectedCallSuffix
Ancestors
  externalCallSelected e2eRequestCutDefs vyperStorageTrace nonreentrantEquiv

Theorem selected_bound_call_trace_suffix:
  !tops am tx ret mut nr args dflts fbody os prefix gas cx es0 es_lock
    r am' rqs obs.
    cx = initial_evaluation_context am.sources am.layouts tx NONE /\
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    external_entry_bound tops am tx os (prefix ++ gas) mut args dflts
      (es0 with gas_obs := gas) /\
    lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es_lock) /\
    call_external_trace (SOME os) (prefix ++ gas) am tx =
      (r,am',rqs,obs) ==>
    ?ans ee suffix.
      eval_stmts cx fbody (es_lock with gas_obs := gas) = (ans,ee) /\
      obs = ee.storage_trace ++ suffix /\
      recorded_outcomes_count suffix = 0
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  Cases_on `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
    fbody (es_lock with gas_obs := gas)` >>
  rename1 `_ = (ans,ee)` >>
  `?eu suffix.
     unlock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
       nr (is_view_mut mut) ee = (INL (),eu) /\
     eu.storage_trace = ee.storage_trace ++ suffix /\
     recorded_outcomes_count suffix = 0` by
    (Cases_on `(initial_evaluation_context am.sources am.layouts tx NONE).
                nonreentrant_slot`
     >- (Cases_on `nr`
         >- (qexists_tac `ee` >> qexists_tac `[]` >>
             simp[vyperInterpreterTheory.unlock_if_nr_def,
                  vyperStateTheory.return_def,
                  recorded_outcomes_count_def])
         >- simp[vyperInterpreterTheory.unlock_if_nr_def,
                 vyperStateTheory.return_def, recorded_outcomes_count_def])
     >- (mp_tac (Q.INST [`cx` |->
              `initial_evaluation_context am.sources am.layouts tx NONE`,
              `key` |-> `x`, `es` |-> `ee`,
              `iv` |-> `is_view_mut mut`]
             (SPEC_ALL unlock_if_nr_success_trace)) >>
         impl_tac >- simp[] >>
         strip_tac >>
         qexists_tac `se` >>
         qexists_tac `if nr /\ ~is_view_mut mut then
                        [StorageLock x] else []` >>
         Cases_on `nr` >> Cases_on `mut` >>
         simp[recorded_outcomes_count_def])) >>
  mp_tac (Q.SPECL [`tops`,`am`,`tx`,`ret`,`mut`,`nr`,`args`,`dflts`,`fbody`,
    `os`,`prefix`,`gas`,`es0`,`es_lock`,`ans`,`ee`,`eu`]
    selected_call_trace_result_nr) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `call_external_trace _ _ _ _ = (r,am',rqs,obs)`
    (fn orig => PURE_REWRITE_TAC [orig]) >>
  strip_tac >>
  qexists_tac `ans` >> qexists_tac `ee` >>
  qpat_assum `(r,am',rqs,obs) = (r'',am'',rqs',obs')`
    (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  Cases_on `ans = INL () \/ (?v. ans = INR (ReturnException v))`
  >- (qexists_tac `suffix` >>
      simp[recorded_outcomes_count_def] >> metis_tac[])
  >- (qexists_tac `[]` >>
      simp[recorded_outcomes_count_def] >> metis_tac[])
QED
