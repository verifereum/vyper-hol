(* Raw selected-word history for the oracle instruction, not its prefixes. *)
Theory augAssignCallHistory
Ancestors
  extCallOracleStep compileEnv vyperStorageBackend venomCallOracleDefs
  vyperCallOutcome extCallOracle venomExecSemantics venomState vfmState

Theorem exec_ext_call_saved_word_history:
  state_rel func cenv cx es s /\ inst.inst_outputs = [out] /\
  w2w aw = target /\
  w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq, outcome), es1) /\
  (if tr then tload saved s else sload saved s) =
    lookup_storage saved (get_storage cx es tr) ==>
  ?u. exec_ext_call inst s gas aw vw ao az ro rz stat = OK u /\
    (if tr then tload saved u else sload saved u) =
    lookup_storage saved (get_storage cx (SND (adopt_call_outcome rq outcome es1)) tr)
Proof
  strip_tac >>
  `accounts_rel cx es s /\ es.outcomes = SOME s.vs_outcomes /\
   ~s.vs_call_ctx.cc_static /\ s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[state_rel_def, call_ctx_rel_def] >>
  `?rest. rq = call_outcome_request target (read_memory (w2n ao) (w2n az) s)
                 value_opt es /\
          take_outcome rq s.vs_outcomes = (outcome, rest) /\
          es1 = es with <| outcomes := SOME rest;
                           requests := record_request rq es.requests |>` by
    (qpat_x_assum `take_call_outcome _ _ _ _ = _` mp_tac >>
     simp[take_call_outcome_def] >> pairarg_tac >> simp[] >> rw[] >>
     qexists_tac `rest` >> simp[]) >>
  `request_agree cx rq (venom_call_request s aw vw ao az stat)` by
    (qpat_x_assum `rq = _` SUBST1_TAC >>
     irule venom_call_request_source >> simp[]) >>
  simp[exec_ext_call_def] >>
  simp[consume_call_outcome_def] >>
  Cases_on `s.vs_outcomes`
  >- (gvs[take_outcome_def] >>
      Cases_on `tr` >> Cases_on `value_opt` >>
      gvs[adopt_outcome_def, failed_outcome_def, adopt_call_outcome_equation,
          venom_call_request_def, call_outcome_request_def,
          sload_def, tload_def, update_var_def, contract_storage_def,
          contract_transient_def, get_storage_def]) >>
  `computed_precompile rq = computed_precompile (venom_call_request s aw vw ao az stat)` by
    (Cases_on `value_opt` >>
     gvs[computed_precompile_def, call_outcome_request_def, venom_call_request_def]) >>
  Cases_on `computed_precompile rq`
  >- (gvs[take_outcome_def] >>
      Cases_on `tr` >> Cases_on `value_opt` >> Cases_on `h.co_success` >>
      gvs[venom_call_request_def, call_outcome_request_def] >>
      gvs[AllCaseEqs()] >>
      gvs[adopt_outcome_def, failed_outcome_def, adopt_call_outcome_equation,
          venom_call_request_def, call_outcome_request_def,
          sload_def, tload_def, update_var_def, contract_storage_def,
          contract_transient_def, get_storage_def]) >>
  gvs[take_outcome_def] >>
  Cases_on `tr` >> Cases_on `value_opt` >> Cases_on `h.co_success` >>
  gvs[adopt_outcome_def, adopt_call_outcome_equation,
      venom_call_request_def, call_outcome_request_def,
      sload_def, tload_def, update_var_def, contract_storage_def,
      contract_transient_def, get_storage_def, lookup_account_def]
QED
