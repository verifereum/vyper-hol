(* Source reply for a prepared linked raw call, independent of the fetched
   instruction. The reply and adopted state are shared by all horizons. *)
Theory bodyRawOracleSourceMods
Ancestors
  exprSimRawCall exprSimHypsDefs vyperTypeExtCallCore vyperCallOutcome
  vyperStorageFootprint vyperStorageTrace vyperFiniteStoragePreservation

Theorem raw_call_oracle_source_mods:
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  (flags.rcf_is_delegate ==> amount = 0) /\
  (flags.rcf_is_static ==> amount = 0) /\
  (cx.txn.is_static ==> amount = 0) /\
  expr_sim_inv_mods mods cenv cx env esK /\ esK.gas_obs = [] /\
  esK.outcomes <> SOME [] /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
       storage_well_formed_on cx esK (FST H)) ==>
  ?rq outcome es1 es2.
    (if flags.rcf_is_delegate then take_delegate_outcome else take_call_outcome)
      (OPTION_BIND gas dest_NumV) target bs
      (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount) esK =
        (INL (rq,outcome),es1) /\
    adopt_call_outcome rq outcome es1 = (INL (),es2) /\
    eval_raw_call cx flags target bs amount gas esK =
      (if flags.rcf_revert_on_failure /\ ~outcome.co_success then
         INR (Error (RevertData outcome.co_returnData))
       else INL (Value
         (if flags.rcf_revert_on_failure then
            if flags.rcf_max_outsize = 0 then NoneV
            else BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)
          else if flags.rcf_max_outsize = 0 then BoolV outcome.co_success
          else ArrayV (TupleV [BoolV outcome.co_success;
            BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)]))),es2) /\
    (!gs. eval_raw_call cx flags target bs amount gas (esK with gas_obs := gs) =
      (FST (eval_raw_call cx flags target bs amount gas esK),es2 with gas_obs := gs)) /\
    es2.scopes = esK.scopes /\ es2.immutables = esK.immutables /\
    es2.gas_obs = [] /\ LENGTH outcome.co_returnData < dimword (:256) /\
    (!H. valid_horizon cx st0 H es2.storage_trace ==>
         valid_horizon cx st0 H esK.storage_trace /\
         storage_well_formed_on cx es2 (FST H))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `IS_SOME esK.outcomes /\ outcomes_accounts_typed esK.outcomes /\
   accounts_runtime_well_typed esK.accounts` by
    (qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
     simp[expr_sim_inv_mods_def, accounts_runtime_well_typed_accounts_well_typed]) >>
  mp_tac (Q.INST [`es` |-> `esK`, `bytes` |-> `bs`] raw_call_kind_source_tail) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (DISJ_CASES_THEN2 (assume_tac o CONJUNCT1)
    (qx_choose_then `rq` (qx_choose_then `outcome` (qx_choose_then `es1`
      (qx_choose_then `es2` (map_every assume_tac o CONJUNCTS))))))
  >- fs[] >>
  qpat_assum `adopt_call_outcome _ _ _ = _` (fn adopt =>
    drule raw_call_kind_take_adopt_fields >>
    disch_then (strip_assume_tac o REWRITE_RULE [adopt, pairTheory.SND])) >>
  qexistsl [`rq`,`outcome`,`es1`,`es2`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 H esK.storage_trace` by
    (qpat_assum `eval_raw_call _ _ _ _ _ _ esK = _`
       (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_raw_call]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule eval_raw_call_preserves_storage_well_formed_on >>
  conj_tac >- fs[valid_horizon_def] >>
  goal_assum (drule_at Any) >> simp[]
QED
