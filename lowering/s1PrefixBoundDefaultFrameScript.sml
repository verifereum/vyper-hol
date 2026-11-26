Theory s1PrefixBoundDefaultFrame
Ancestors
  externalEntryBound externalBodySupport groupedDefaultHorizon
  e2eDefs vyperInterpreter vyperState list pair finite_map

Theorem guarded_external_entry_request_frame:
  ds = DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts /\
  source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  EVERY (runtime_constant_expr [(NONE,tops)]) ds /\
  no_sha256_exprs ds /\
  external_entry_bound tops am tx os gs mut args dflts es ==>
  es.requests = [] /\ es.storage_trace = []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `external_entry_bound _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [external_entry_bound_def]) >>
  drule_all source_typing_ok_runtime_ready >> strip_tac >>
  qpat_x_assum `ds = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `s1.scopes = [FEMPTY] /\ s1.requests = [] /\ s1.storage_trace = []` by
    (drule external_send_call_value_frame >>
     simp[evaluation_state_component_equality, initial_state_def]) >>
  qpat_x_assum `eval_external_defaults _ _ _ = _` mp_tac >>
  PURE_REWRITE_TAC [eval_external_defaults_run] >>
  strip_tac >>
  Cases_on `eval_exprs (initial_evaluation_context am.sources am.layouts tx NONE)
    (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts)
    (s1 with scopes := [FEMPTY])` >>
  qpat_assum `_ = (INL dflt_vs,s2)`
    (assume_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  `ALOOKUP (initial_evaluation_context am.sources am.layouts tx NONE).sources
      tx.target = SOME [(NONE,tops)]` by
    fs[initial_evaluation_context_def, source_deployment_rel_def] >>
  qabbrev_tac `rr = r` >>
  qabbrev_tac `cx0 = initial_evaluation_context am.sources am.layouts tx NONE` >>
  qabbrev_tac `ds0 = DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts` >>
  qabbrev_tac `st0 = s1 with scopes := [FEMPTY]` >>
  qabbrev_tac `lay0 = am.layouts` >>
  qabbrev_tac `addr0 = tx.target` >>
  qabbrev_tac `art0 = art` >>
  qabbrev_tac `tops0 = tops` >>
  qabbrev_tac `tx0 = tx` >>
  `ALOOKUP cx0.sources cx0.txn.target = SOME [(NONE,tops0)]` by
    fs[Abbr `cx0`, Abbr `tops0`, Abbr `addr0`, Abbr `tx0`,
       initial_evaluation_context_def, source_deployment_rel_def] >>
  drule_all (Q.INST
    [`cx` |-> `cx0`, `es` |-> `ds0`, `st` |-> `st0`, `ee` |-> `rr`,
     `layouts` |-> `lay0`, `addr` |-> `addr0`, `art` |-> `art0`,
     `tops` |-> `tops0`]
    grouped_checked_default_source_frame) >>
  strip_tac >>
  gvs[evaluation_state_component_equality, Abbr `rr`, Abbr `st0`,
      Abbr `cx0`, Abbr `ds0`, Abbr `art0`, Abbr `lay0`, Abbr `addr0`,
      Abbr `tops0`, Abbr `tx0`]
QED
