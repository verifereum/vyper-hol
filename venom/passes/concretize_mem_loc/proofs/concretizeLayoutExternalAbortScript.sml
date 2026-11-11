Theory concretizeLayoutExternalAbort
Ancestors concretizeLayoutPhaseAbort concretizeLayoutExternalCall
  concretizeLayoutExternalCreate concretizeLayoutLocalTerminals
  frameRelocationValues venomExecSemantics venomState ptrDiscipline list
  concretizeLayoutPhaseOrigin frameJointTrace frameJointTransition frameOriginReachable
  frameOriginHistory frameResolvedTrace frameRelocationReachableSupport
  frameRelocationLocal frameRelocationEnvironment

Theorem external_call_not_abort[local]:
  exec_ext_call inst s gas addr value ao sz ro rs stat <> Abort a post
Proof
  simp[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >> simp[]
QED

Theorem concretize_external_abort_complete:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  variable_domains s t /\ s.vs_labels = t.vs_labels /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t /\
  MEM inst.inst_opcode [CALL; CREATE; CREATE2] /\
  step_inst_base inst s = Abort a post ==>
  ?tpost. step_inst_base inst t = Abort a tpost /\
    dead_result_rel D (Abort a post) (Abort a tpost)
Proof
  strip_tac >>
  `!op. eval_operand op s = NONE <=> eval_operand op t = NONE` by
    (gen_tac >> irule operand_domain_agreement >> simp[]) >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule eval_operands_domain_agreement >> simp[]) >>
  qpat_x_assum `MEM inst.inst_opcode _` mp_tac >>
  pure_rewrite_tac[MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = Abort a post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs(), exec_create_abort_iff, external_call_not_abort,
       Excl "consume_create_outcome_eq"] >>
  rpt strip_tac >> gvs[]
  >- (`eval_operand val_op s = eval_operand val_op t` by
        (drule_at (Pat `local_rel _ _ _ _ _ _ _`)
           (GEN_ALL (SRULE [] (Q.INST [`vals` |-> `[val_op]`]
             (SPEC_ALL ext_call_scalar_agreement)))) >>
         disch_then assume_tac >> first_x_assum irule >> simp[] >>
         (conj_tac >- (qexists_tac `P` >> simp[])) >>
         (conj_tac >- (qexists_tac `C` >> simp[])) >>
         goal_assum (drule_at (Pat `_ .inst_operands = _`)) >> simp[]) >>
      qexists_tac `halt_state (set_returndata [] t)` >>
      simp[dead_result_rel_def] >>
      metis_tac[optionTheory.option_nchotomy, optionTheory.NOT_NONE_SOME]) >>
  gvs[eval_operands_def] >>
  TRY (qpat_assum `t.vs_call_ctx.cc_static` kall_tac >>
       qexists_tac `halt_state (set_returndata [] t)` >>
       simp[dead_result_rel_def] >> NO_TAC) >>
  (`eval_operand sz_op s = eval_operand sz_op t` by
     (drule_at (Pat `local_rel _ _ _ _ _ _ _`) create_scalar_agreement >>
      disch_then assume_tac >> first_x_assum irule >> simp[] >>
      (conj_tac >- (qexists_tac `P` >> simp[])) >>
      (conj_tac >- (qexists_tac `C` >> simp[])) >>
      goal_assum (drule_at (Pat `_ .inst_operands = _`)) >> simp[]) >>
   qexists_tac `halt_state (set_returndata [] t)` >>
   simp[dead_result_rel_def] >>
   metis_tac[optionTheory.option_nchotomy, optionTheory.NOT_NONE_SOME])
QED

Theorem layout_external_abort_step:
  ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [CALL; CREATE; CREATE2] /\
  step_inst_base inst s = Abort a post ==>
  ?tpost. step_inst_base inst t = Abort a tpost /\
    dead_result_rel D (Abort a post) (Abort a tpost) /\
    layout_scoped_outcome D Ret Entry (INL g) (INL g)
      (Abort a post) (Abort a tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_config_reachable vs0 C g.lop_config` by
    (fs[layout_ordinary_trace_def] >>
     drule joint_trace_prefix_reachable >> pure_rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `g.lop_cursor` mp_tac) >> simp[]) >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (gvs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `resolved_config_ok g.lop_config g.lop_ids g.lop_anns` by
    fs[layout_ordinary_trace_def] >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (qpat_x_assum `resolved_config_ok _ _ _` mp_tac >>
     asm_rewrite_tac[] >> strip_tac >> drule resolved_config_current >>
     simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  `variable_domains s t /\ s.vs_labels = t.vs_labels /\
   s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static` by
    (fs[relocation_env_def] >> metis_tac[local_rel_domains]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) concretize_external_abort_complete >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  simp[] >> strip_tac >>
  metis_tac[layout_scoped_abort_embedding]
QED
