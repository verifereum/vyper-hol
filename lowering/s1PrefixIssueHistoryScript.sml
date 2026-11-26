(* Requests only grow on recorder paths, so an issuing history bounds the cut. *)
Theory s1PrefixIssueHistory
Ancestors
  loweringBudgetPathDeterminism loweringBudgetStoreRecorder loweringBudgetDallocaWindows
  dftGasRequestObservation concretizeLayoutRequestRelations
  jointRequestCut calleeTransport
  loweringCallBudgetHistory venomExecSemantics venomExecProofs venomInst venomState
  e2eRequestCutDefs list rich_list arithmetic

Theorem lower_budget_path_prefix_requests[local]:
  !checked cfg root h marks q.
    lower_budget_path checked cfg root h marks q ==>
    !n mn p. n <= LENGTH h /\
      lower_budget_path checked cfg root (TAKE n h) mn p ==>
      p.bp_state.vs_requests <<= q.bp_state.vs_requests
Proof
  Induct_on `h` using SNOC_INDUCT >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac
  >- (fs[] >>
      qpat_x_assum `lower_budget_path _ _ _ [] marks _` mp_tac >>
      qpat_x_assum `lower_budget_path _ _ _ [] mn _` mp_tac >>
      simp[Once lower_budget_path_cases, GSYM SNOC_APPEND] >>
      simp[Once lower_budget_path_cases, GSYM SNOC_APPEND] >>
      rw[] >> simp[IS_PREFIX_REFL]) >>
  fs[SNOC_APPEND] >>
  Cases_on `n = LENGTH (h ++ [x])`
  >- (`TAKE n (h ++ [x]) = h ++ [x]` by simp[TAKE_LENGTH_TOO_LONG] >>
      `p = q` by metis_tac[lower_budget_path_history_unique] >> simp[]) >>
  `n <= LENGTH h` by fs[] >> fs[TAKE_APPEND1] >>
  qpat_x_assum `lower_budget_path _ _ _ (h ++ [x]) marks q` mp_tac >>
  once_rewrite_tac[lower_budget_path_cases] >> strip_tac >>
  gvs[GSYM SNOC_APPEND] >>
  `p.bp_state.vs_requests <<= p'.bp_state.vs_requests` by metis_tac[]
  >- (drule_all step_inst_requests_prefix >> metis_tac[IS_PREFIX_TRANS])
  >- (`i.inst_opcode <> INVOKE` by metis_tac[is_terminator_not_invoke] >>
      drule_all step_inst_requests_prefix >>
      drule_all enters_block_requests >> metis_tac[IS_PREFIX_TRANS])
  >- (drule_all setup_callee_oracle >>
      drule_all enters_block_requests >> simp[]) >>
  drule_all bind_outputs_oracle >>
  drule_all step_inst_intret_requests >> simp[]
QED

(* Compare points, not the recorded fuel choices of the two paths. *)
Theorem issue_history_bounds_frame_history:
  root.bp_stack = [] /\ MEM root.bp_fn ctx.ctx_functions /\
  (!fn. MEM fn ctx.ctx_functions ==>
    ALL_DISTINCT (fn_labels fn) /\
    !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  lower_budget_path T (D,lo,explicit,ctx) root h marks p /\
  lower_budget_path F (D,lo,explicit,ctx) root hr mr q /\
  active_inst p.bp_fn issue p.bp_state /\ issue.inst_opcode <> INVOKE /\
  LENGTH p.bp_state.vs_requests = k /\ step_inst fuel ctx issue p.bp_state = OK t /\
  k < LENGTH t.vs_requests /\ request_cut k q.bp_state ==>
  LENGTH hr <= LENGTH h
Proof
  strip_tac >> spose_not_then assume_tac >>
  `LENGTH h < LENGTH hr` by decide_tac >>
  qpat_assum `lower_budget_path F _ _ hr mr q`
    (mp_then Any (qspec_then `LENGTH h` mp_tac) lower_budget_path_take) >>
  (impl_tac >- decide_tac) >>
  disch_then (qx_choose_then `at_issue` (qx_choose_then `pre_marks` strip_assume_tac)) >>
  `LENGTH (TAKE (LENGTH h) hr) = LENGTH h` by simp[LENGTH_TAKE] >>
  `at_issue = p` by metis_tac[lower_budget_path_equal_length_sync] >>
  `MEM p.bp_fn ctx.ctx_functions` by metis_tac[lower_budget_path_current_fn_mem] >>
  `ALL_DISTINCT (fn_labels p.bp_fn)` by metis_tac[] >>
  `LENGTH p.bp_state.vs_requests < LENGTH t.vs_requests` by simp[] >>
  drule_all step_inst_request_outcomes >> disch_then (assume_tac o CONJUNCT1) >>
  `~is_terminator issue.inst_opcode` by
    (qpat_x_assum `MEM issue.inst_opcode _` mp_tac >> simp[is_terminator_def] >>
     metis_tac[is_terminator_def]) >>
  qpat_x_assum `at_issue = p` SUBST_ALL_TAC >>
  drule_all lower_budget_window_index_next >> strip_tac >>
  rename1 `step_inst_base issue p.bp_state = OK post` >>
  rename1 `lower_budget_path F _ _ (TAKE (SUC (LENGTH h)) hr) _ after` >>
  `post = t` by metis_tac[step_inst_non_invoke, exec_result_11] >>
  `SUC (LENGTH h) <= LENGTH hr` by decide_tac >>
  `after.bp_state.vs_requests <<= q.bp_state.vs_requests` by
    metis_tac[lower_budget_path_prefix_requests] >>
  fs[request_cut_def] >> drule IS_PREFIX_LENGTH >> simp[] >> decide_tac
QED
