(* Deferred single-emission progress. The source abort state is frozen;
   only the separate ghost executes safe instructions. *)
Theory acDeferredEmissionProofs
Ancestors
  acMergeRuntimeDefs acMergeCursorDefs acMergeSimulationProofs
  acMergeStepProofs acAbortRelProofs acChainProofs acBaseProofs
  assertCombinerDefs stateEquiv stateEquivProps venomExecSemantics
  venomExecProofs venomState venomInst analysisSimDefs basePtrProofs finite_map list words

Theorem ac_deferred_pending_step[local]:
  ac_merge_runtime_laws xs dfg fuel ctx cert /\
  ac_merge_operand_origin xs dfg X n p /\ n < LENGTH xs /\
  (!v. MEM v (EL n xs).inst_outputs ==> v NOTIN X) /\
  step_inst fuel ctx (EL n xs) t = OK u ==>
  eval_operand p u = eval_operand p t
Proof
  rpt strip_tac >> fs[ac_merge_operand_origin_def]
  >- (simp[eval_operand_def] >> irule step_inst_preserves_lookup >> metis_tac[]) >>
  irule ac_merge_runtime_laws_prior_operand >> metis_tac[]
QED

Theorem ac_deferred_end:
  ac_merge_cursor_laws xs dfg cs X su0 shape pending ==>
  ~ac_merge_revert_deferred X cert shape pending (LENGTH xs) mp su a sa g t
Proof
  simp[ac_merge_cursor_laws_def, ac_merge_revert_deferred_def,
       ac_merge_deferred_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem ac_deferred_emission_contract:
  ac_merge_cursor_laws xs dfg cs X su0 shape pending /\
  ac_merge_runtime_laws xs dfg fuel ctx cert /\
  (!n c q v. n < LENGTH xs /\ (EL n xs).inst_opcode = ASSERT /\
    (EL n xs).inst_operands = [c] /\
    ac_get_iszero_operand dfg {} c = SOME q /\ q = Var v ==> v NOTIN X) ==>
  ac_deferred_emission_contract xs cs fuel ctx ac_abort_equiv
    (ac_merge_revert_deferred X cert shape pending)
Proof
  rpt strip_tac >> simp[ac_deferred_emission_contract_def] >>
  rpt gen_tac >> strip_tac >>
  fs[ac_merge_revert_deferred_def, ac_merge_deferred_def] >>
  `shape (SUC n) mp' su' /\
   ac_merge_emission_form dfg X (EL n xs)
     (pending n mp su) (pending (SUC n) mp' su') out` by
    (fs[ac_merge_cursor_laws_def] >> metis_tac[]) >>
  qpat_x_assum `ac_merge_emission_form _ _ _ _ _ _` mp_tac >>
  simp[ac_merge_emission_form_def] >> strip_tac
  >- suspend "gap"
  >- suspend "equal"
  >> suspend "generated"
QED

Resume ac_deferred_emission_contract[gap]:
  `?g'. step_inst fuel ctx (EL n xs) g = OK g'` by
    metis_tac[ac_merge_runtime_laws_safe_total] >>
  `cert (SUC n) g'` by metis_tac[ac_merge_runtime_laws_step] >>
  `!v. MEM (Var v) (EL n xs).inst_operands ==> v NOTIN X` by
    (fs[ac_merge_cursor_laws_def] >> metis_tac[EL_MEM]) >>
  drule_all ac_unchanged_step >>
  disch_then (qspecl_then [`fuel`,`ctx`] mp_tac) >>
  simp[lift_result_def] >>
  Cases_on `step_inst fuel ctx (EL n xs) t` >>
  simp[lift_result_def] >> strip_tac >>
  `ac_merge_operand_origin xs dfg X n p /\
   (!v. MEM v (EL n xs).inst_outputs ==> v NOTIN X)` by
    (fs[ac_merge_cursor_laws_def] >> metis_tac[EL_MEM]) >>
  `eval_operand p v' = eval_operand p t` by
    (irule ac_deferred_pending_step >> metis_tac[]) >>
  `ac_abort_equiv (revert_state (set_returndata [] g))
     (revert_state (set_returndata [] g'))` by
    metis_tac[ac_safe_step_revert_abort_equiv] >>
  disj2_tac >> qexistsl [`v'`,`g'`] >>
  simp[run_insts_def] >> metis_tac[ac_abort_equiv_trans]
QED
Resume ac_deferred_emission_contract[equal]:
  FAIL_TAC "equal"
QED
Resume ac_deferred_emission_contract[generated]:
  FAIL_TAC "generated"
QED
Finalise ac_deferred_emission_contract
