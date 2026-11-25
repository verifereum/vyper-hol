(* Only the oracle take can add a StorageOutcome in the raw-call tail. *)
Theory s1PrefixRawCallSourceTail
Ancestors
  s1PrefixFrame s1PrefixProps exprSimRawCall exprSimRawCallCalldata
  s1PrefixDefs vyperCallOutcome vyperCallOutcomeProps vyperStorageTrace list

Theorem raw_call_eval_prefix_from_take:
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0) /\
  IS_SOME es.outcomes /\ outcomes_accounts_typed es.outcomes /\
  accounts_runtime_well_typed es.accounts /\ ~s.vs_halted /\
  (!rq outcome mid.
    (if flags.rcf_is_delegate then take_delegate_outcome else take_call_outcome)
      (OPTION_BIND gasarg dest_NumV) target bs
      (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount) es =
        (INL (rq,outcome),mid) ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
      ((if flags.rcf_is_delegate then take_delegate_outcome else take_call_outcome)
        (OPTION_BIND gasarg dest_NumV) target bs
        (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount))
      (es,s,G,tn)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_raw_call cx flags target bs amount gasarg) (es,s,G,tn)
Proof
  strip_tac >>
  Cases_on `cx.txn.is_static /\ amount <> 0 \/ es.outcomes = SOME []`
  >- (`!gs. SND (eval_raw_call cx flags target bs amount gasarg
                 (es with gas_obs := gs)) = es with gas_obs := gs` by
        (gen_tac >> Cases_on `cx.txn.is_static /\ amount <> 0`
         >- (`~flags.rcf_is_delegate /\ ~flags.rcf_is_static` by metis_tac[] >>
             simp[raw_call_static_value_abort]) >>
         `es.outcomes = SOME [] /\
          ((flags.rcf_is_delegate \/ flags.rcf_is_static \/ cx.txn.is_static) ==>
           amount = 0)` by metis_tac[] >>
         `eval_raw_call cx flags target bs amount gasarg (es with gas_obs := gs) =
            (INR (Error (RuntimeError "take_call_outcome")), es with gas_obs := gs)` by
           (irule raw_call_oracle_empty >> simp[] >> metis_tac[]) >> simp[]) >>
      irule gas_prefix_full_no_outcome >>
      simp[storage_trace_frame_raw_call] >> rpt strip_tac >>
      first_x_assum (qspec_then `gobs` mp_tac) >> simp[DROP_LENGTH_NIL]) >>
  mp_tac (Q.INST [`bytes` |-> `bs`, `gas` |-> `gasarg`] raw_call_kind_source_tail) >>
  impl_tac >- metis_tac[] >>
  disch_then (DISJ_CASES_THEN2 (assume_tac o CONJUNCT1) strip_assume_tac)
  >- metis_tac[] >>
  qabbrev_tac `take = (if flags.rcf_is_delegate then take_delegate_outcome else take_call_outcome)
    (OPTION_BIND gasarg dest_NumV) target bs
    (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount)` >>
  `gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 take (es,s,G,tn)` by
    metis_tac[] >>
  `!gs. take (es with gas_obs := gs) = (INL (rq,outcome),es1 with gas_obs := gs)` by
    (qpat_assum `take es = _` mp_tac >> qunabbrev_tac `take` >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `flags.rcf_is_delegate` >>
     simp[take_delegate_gas_obs,take_call_outcome_gas_obs]) >>
  `es1.storage_trace = es.storage_trace ++ [StorageOutcome rq outcome]` by
    (qpat_assum `take es = _` mp_tac >> qunabbrev_tac `take` >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `flags.rcf_is_delegate` >>
     simp[take_call_outcome_def,take_delegate_outcome_def] >>
     strip_tac >> drule take_request_outcome_success >> strip_tac >> gvs[]) >>
  Q.SUBGOAL_THEN
    `?back. es2.storage_trace = es.storage_trace ++ StorageOutcome rq outcome :: back /\
      (back = [] \/ back = [StorageBackend outcome.co_accounts outcome.co_tStorage])`
    (qx_choose_then `back` (CONJUNCTS_THEN2 assume_tac assume_tac))
  >- (qpat_assum `adopt_call_outcome _ _ _ = _` mp_tac >>
      qpat_assum `es1.storage_trace = _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rw[adopt_call_outcome_equation] >>
      fs[APPEND_ASSOC]) >>
  qpat_x_assum `gas_prefix_full _ _ _ take _` mp_tac >>
  pure_rewrite_tac[gas_prefix_full_def] >>
  disch_then (qx_choose_then `marks` (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qexists_tac `marks` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `es2.storage_trace = obs_pre ++ StorageOutcome rq' outcome' :: sfx` by
    (qpat_x_assum `eval_raw_call _ _ _ _ _ _ (_ with gas_obs := _) = _` mp_tac >> simp[] >>
     strip_tac >> gvs[]) >>
  `obs_pre = es.storage_trace /\ rq' = rq /\ outcome' = outcome` by
    (qpat_assum `es2.storage_trace = es.storage_trace ++ _` (fn th =>
       qpat_assum `es2.storage_trace = obs_pre ++ _`
         (mp_tac o REWRITE_RULE[th])) >>
     pure_once_rewrite_tac[APPEND_EQ_APPEND] >>
     disch_then (DISJ_CASES_THEN (qx_choose_then `extra` strip_assume_tac))
     >- (`LENGTH extra = 0` by
           (qpat_assum `es.storage_trace = obs_pre ++ extra`
              (mp_tac o AP_TERM ``LENGTH : storage_trace_event list -> num``) >>
            qpat_assum `LENGTH es.storage_trace <= LENGTH obs_pre` mp_tac >>
            pure_rewrite_tac[LENGTH_APPEND] >> decide_tac) >> gvs[]) >>
     Cases_on `extra` >- gvs[] >>
     rename1 `StorageOutcome rq outcome :: back = (h::rest) ++ _` >>
     qpat_x_assum `StorageOutcome rq outcome :: back = (h::rest) ++ _` mp_tac >>
     qpat_x_assum `back = [] \/ _` mp_tac >>
     disch_then (DISJ_CASES_THEN SUBST1_TAC) >>
     Cases_on `rest` >> simp[NoAsms]) >>
  gvs[] >> first_x_assum irule >> simp[] >> qexists_tac `[]` >> simp[]
QED
