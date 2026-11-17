Theory lowerDloadPtrDelegateInterfaces
Ancestors lowerDloadPtrCall lowerDloadPtrRel ptrDiscipline venomExecSemantics
  venomState finite_map pred_set list pointerConfinedDefs memLocDefs
  lowerDloadPtrResidualInterfaces lowerDloadPtrPhi
  venomCallOracleProps venomCallOracleDefs extCallOracle

Theorem dload_delegate_scalar_safety:
  i.inst_opcode = DELEGATECALL /\
  i.inst_operands = [gas;addr;a;sz;r;rs] /\ MEM op [gas;addr;sz;rs] /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\ taint_ok f tn i s ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v. op = Var v ==> v NOTIN pv` by
    (rpt strip_tac >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_read_ops_def, mem_write_ops_def] >>
     qpat_x_assum `!v. _` (qspec_then `v` mp_tac) >> simp[] >>
     Cases_on `a = Var v` >> Cases_on `r = Var v` >> gvs[] >>
     rpt (IF_CASES_TAC >> gvs[]) >> rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  gvs[taint_ok_def] >>
  qmatch_goalsub_abbrev_tac `op_taint tn arg` >>
  qpat_x_assum `!op'. _ \/ op_taint tn op' = {}`
    (qspec_then `arg` mp_tac) >> simp[Abbr `arg`]
QED

Theorem dload_delegate_scalar_equal:
  i.inst_opcode = DELEGATECALL /\
  i.inst_operands = [gas;addr;a;sz;r;rs] /\ MEM op [gas;addr;sz;rs] /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\ taint_ok f tn i s /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    (drule_all dload_delegate_scalar_safety >> simp[]) >>
  `MEM op i.inst_operands` by gvs[] >>
  `eval_operand op s = NONE <=> eval_operand op t = NONE` by
    (irule eval_operand_definedness >> metis_tac[]) >>
  drule scalar_operand_equal >> disch_then irule >> metis_tac[]
QED

(* Both runs consume the shared oracle with one delegate request, so they
   take the same outcome.  Each run's accounts are its own unless the outcome
   is adopted, as for CALL. *)
Theorem dload_delegate_exec_success:
  dload_equal_environment s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n az) t /\
  exec_delegatecall i s gas addr ao az ro rz = OK s' ==>
  ?t'. exec_delegatecall i t gas addr bo az tr rz = OK t' /\
    dload_equal_environment s' t' /\
    (!out. MEM out i.inst_outputs ==> lookup_var out s' = lookup_var out t')
Proof
  strip_tac >> drule_all dload_delegate_full_stores >> strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_outcomes = t.vs_outcomes /\
   s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions` by
    gvs[dload_equal_environment_def, venom_state_component_equality] >>
  qabbrev_tac `rq = venom_call_request s addr 0w ao az F with
                      cr_kind := DelegateMessageCall` >>
  `venom_call_request t addr 0w bo az F with
     cr_kind := DelegateMessageCall = rq` by
    simp[Abbr `rq`, venom_call_request_def] >>
  Cases_on `consume_call_outcome rq (w2n ro) (w2n rz) s` >>
  rename1 `consume_call_outcome rq _ _ s = (w1,r1)` >>
  `?out. i.inst_outputs = [out] /\ s' = update_var out w1 r1` by
    (fs[Abbr `rq`, exec_delegatecall_def,
        Excl "consume_call_outcome_eq", AllCaseEqs()] >> metis_tac[]) >>
  drule_at (Pat `consume_call_outcome _ _ _ _ = _`)
    consume_call_outcome_state_transport >>
  disch_then (qspec_then `t` mp_tac) >> simp[Excl "consume_call_outcome_eq"] >>
  disch_then (qspec_then `w2n tr` strip_assume_tac) >>
  qexistsl [`w1`,`r1`,`rq`] >>
  asm_simp_tac (srw_ss()) [exec_delegatecall_def,
                           Excl "consume_call_outcome_eq"] >>
  simp[venom_state_component_equality]
QED
