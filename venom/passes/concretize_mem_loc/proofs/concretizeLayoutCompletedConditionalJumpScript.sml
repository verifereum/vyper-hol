Theory concretizeLayoutCompletedConditionalJump
Ancestors concretizeLayoutCompletedJump concretizeLayoutEntryFlags
  concretizeLayoutLocalConditionalJump concretizeLayoutPhaseOrigin
  frameJointTrace frameJointTransition frameOriginHistory frameOriginReachable
  frameRelocationLocal frameRelocationEnvironment ptrDiscipline
  venomExecSemantics venomState venomInst list

Theorem layout_completed_conditional_jump:
  ~a.lop_pending /\
  layout_ordinary_entry D lo vs0 C C' q0 es qs q a s t /\
  a.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  vs0.vs_allocas = FEMPTY /\ ~vs0.vs_halted /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  get_instruction a.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  get_instruction a.lop_origin.lbo_target t.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode [JNZ; DJMP] /\
  step_inst_base inst s = OK post ==>
  ?tpost. layout_completed_jump D lo vs0 C C' q0 es qs q a inst inst s t post tpost
Proof
  strip_tac >>
  drule_all layout_ordinary_entry_nonhalting >> strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q a s /\
   layout_ordinary_state D lo C' q0 es qs a s t` by
    fs[layout_ordinary_entry_def] >>
  gvs[layout_ordinary_trace_def, layout_ordinary_state_def] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (drule joint_trace_prefix_reachable >> rewrite_tac[EVERY_EL] >> strip_tac >>
     qpat_x_assum `!n. _` (qspec_then `a.lop_cursor` mp_tac) >>
     simp[joint_config_reachable_def] >> strip_tac >>
     drule joint_origin_history_erasure >> strip_tac >>
     drule origin_frame_erasure >> simp[]) >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    metis_tac[conditional_jump_operands, MEM] >>
  `?lbl. post = jump_to lbl s /\ step_inst_base inst t = OK (jump_to lbl t)` by
    metis_tac[conditional_jump_execution, MEM] >>
  qexists `jump_to lbl t` >>
  simp[layout_completed_jump_def] >>
  gvs[MEM, venomInstTheory.is_terminator_def, jump_to_def] >>
  qexists `lbl` >> simp[]
QED

val _ = if null (hyp layout_completed_conditional_jump) then ()
        else raise Fail "completed conditional jump export has hypotheses";
val _ = export_theory();
