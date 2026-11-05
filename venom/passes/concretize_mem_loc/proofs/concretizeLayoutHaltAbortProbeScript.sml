Theory concretizeLayoutHaltAbortProbe
Ancestors concretizeLayoutLocalLog concretizeLayoutLocalValues
  frameRelocationBinding frameJointTaint venomExecSemantics venomState ptrDiscipline

Theorem final_demand_excludes_taint:
  EL (LENGTH es) (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  a IN tn.t_mem ==>
  ~joint_relocation_demand lo positions q0 es qs (LENGTH es) a z
Proof
  rpt strip_tac >> fs[joint_relocation_demand_def] >>
  `j = LENGTH es` by decide_tac >>
  gvs[joint_observed_read_def, joint_mem_taint_def]
QED

Definition probe_return_def:
  probe_return = <| inst_id := 0; inst_opcode := RETURN;
    inst_operands := [Lit 0w; Lit 1w]; inst_outputs := [] |>
End

Definition probe_state_def:
  probe_state b = (init_venom_state "entry") with vs_memory := [b]
End

Theorem probe_return_zero:
  step_inst_base probe_return (probe_state 0w) =
  Halt (halt_state (set_returndata [0w] (probe_state 0w)))
Proof
  EVAL_TAC >> simp[wordsTheory.word_0_n2w, wordsTheory.word_1_n2w,
                   wordsTheory.w2n_n2w]
QED

Theorem probe_return_one:
  step_inst_base probe_return (probe_state 1w) =
  Halt (halt_state (set_returndata [1w] (probe_state 1w)))
Proof
  EVAL_TAC >> simp[wordsTheory.word_0_n2w, wordsTheory.word_1_n2w,
                   wordsTheory.w2n_n2w]
QED

Theorem probe_return_not_related:
  D.d_ret [0w] = {} ==>
  ~dead_result_rel D
    (step_inst_base probe_return (probe_state 0w))
    (step_inst_base probe_return (probe_state 1w))
Proof
  simp[probe_return_zero, probe_return_one, dead_result_rel_def,
       halt_state_def, set_returndata_def, probe_state_def,
       init_venom_state_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED
