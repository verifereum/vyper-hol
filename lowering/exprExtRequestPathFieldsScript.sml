Theory exprExtRequestPathFields
Ancestors
  fragGasMode fragGasPath venomExecProofs venomInstProofs venomState
  venomExecSemantics venomInst venomCallOracleDefs extCallOracle

Theorem extrequest_step_contexts:
  !fuel ctx inst s t.
    step_inst fuel ctx inst s = OK t ==>
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
      qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[Once step_inst_def] >>
      simp[step_inst_base_opcode_eqs, jump_to_def] >>
      gvs[AllCaseEqs(), PULL_EXISTS] >>
      rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
      rw[] >> gvs[] >>
      pairarg_tac >> gvs[]) >>
  metis_tac[step_preserves_tx_ctx, step_preserves_block_ctx]
QED

Theorem extrequest_phis_contexts:
  !insts s t. eval_phis s insts = OK t ==>
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx
Proof
  rpt strip_tac >> drule eval_phis_only_updates_vs_vars >>
  disch_then SUBST1_TAC >> simp[]
QED

Theorem extrequest_edge_contexts:
  gas_path_edge ctx fn s n (OK t) ==>
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx
Proof
  rw[gas_path_edge_def] >>
  gvs[fragExecTheory.exit_result_def, jump_to_def] >>
  metis_tac[extrequest_step_contexts, extrequest_phis_contexts]
QED

Theorem extrequest_path_contexts:
  gas_marked_path F ctx fn s n (OK t) ==>
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx
Proof
  simp[gas_marked_path_def] >>
  `!ctx fn s n r. gas_path ctx fn s n r ==>
    !t. r = OK t ==>
      t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx`
    suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[] >> metis_tac[extrequest_edge_contexts]) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

(* Computed precompiles consume the oracle even though no request is recorded.
   Thus request equality alone is not a global oracle-history frame. *)
Theorem extrequest_computed_oracle_history_probe:
  computed_precompile rq /\ s.vs_outcomes = oc::rest ==>
  (SND (consume_call_outcome rq ro rz s)).vs_requests = s.vs_requests /\
  (SND (consume_call_outcome rq ro rz s)).vs_outcomes = rest
Proof
  simp[consume_call_outcome_eq, record_request_def, take_outcome_rest]
QED
