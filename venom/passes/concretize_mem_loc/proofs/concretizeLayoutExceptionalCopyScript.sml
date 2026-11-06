Theory concretizeLayoutExceptionalCopy
Ancestors concretizeLayoutLocalReturnCopy concretizeLayoutRankedCorridor
  concretizeLayoutLocalCalldataCopy frameResolvedTrace concretizePtrParamSupport
  frameRelocationReachableSupport frameRelocationLocal frameRelocationValues
  frameRelocationGuardedValues frameRelocationEnvironment
  ptrDiscipline venomExecSemantics venomState list

Theorem concretize_returncopy_success_complete:
  ptr_discipline lo C vs0 /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  frame_reachable vs0 C stk PG G tn fn inst s /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\ relocation_env s t /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R concretize_local_obs s t /\
  step_inst_base inst s = OK post ==>
  ?tpost. step_inst_base inst t = OK tpost
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  `eval_operand ops s = eval_operand ops t /\ eval_operand opn s = eval_operand opn t` by
    (drule_at (Pat `local_rel _ _ _ _ _ _ _`) calldatacopy_scalar_agreement >>
     disch_then irule >> simp[MEM] >> metis_tac[]) >>
  `?dstT. eval_operand opd t = SOME dstT` by
    (drule local_rel_domains >> strip_tac >>
     drule_all operand_domain_agreement >> disch_then (qspec_then `opd` mp_tac) >>
     Cases_on `eval_operand opd t` >> simp[]) >>
  `s.vs_returndata = t.vs_returndata` by
    metis_tac[local_rel_observation, local_obs_returndata] >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  gvs[] >> simp[step_inst_base_def] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> gvs[] >> simp[step_inst_base_def]
QED

Theorem concretize_returncopy_atomic_abort:
  ptr_discipline lo C vs0 /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  frame_reachable vs0 C stk PG G tn fn inst s /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\ relocation_env s t /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R concretize_local_obs s t /\
  step_inst_base inst s = OK post /\
  ranked_terminal_corridor bb bb' (SUC s.vs_inst_idx) (SUC t.vs_inst_idx) n /\
  exec_block fuel C bb (post with vs_inst_idx := SUC post.vs_inst_idx) = Abort a final ==>
  ?tpost final'. step_inst_base inst t = OK tpost /\
    exec_block fuel C' bb' (tpost with vs_inst_idx := SUC tpost.vs_inst_idx) =
      Abort a final' /\ dead_result_rel D (Abort a final) (Abort a final')
Proof
  strip_tac >>
  drule_all concretize_returncopy_success_complete >> strip_tac >>
  `variable_domains s t` by metis_tac[local_rel_domains] >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  drule_all layout_returncopy_ranked_abort >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

val _ = export_theory();
