Theory concretizePtrMcopySource
Ancestors concretizePtrValueTransport venomExecSemantics ptrDiscipline words

Theorem ptr_mcopy_source_success:
  !births positions TG tn s t inst dop sop nop dt rt (n_target:bytes32) fuel ctx.
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dop;sop;nop] /\
  ptr_vars_transport births positions TG tn s t /\ s.vs_labels = t.vs_labels /\
  eval_operand dop t = SOME dt /\ eval_operand sop t = SOME rt /\
  eval_operand nop t = SOME n_target ==>
  ?d r n.
    eval_operand dop s = SOME d /\ eval_operand sop s = SOME r /\
    eval_operand nop s = SOME n /\
    ptr_value_transport births positions (op_prov TG dop) (op_taint tn dop) d dt /\
    ptr_value_transport births positions (op_prov TG sop) (op_taint tn sop) r rt /\
    ptr_value_transport births positions (op_prov TG nop) (op_taint tn nop) n n_target /\
    step_inst fuel ctx inst s = OK (mcopy (w2n d) (w2n r) (w2n n) s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ptr_vars_transport_eval_source >>
  disch_then (qx_choose_then `n` strip_assume_tac) >>
  qpat_x_assum `eval_operand nop t = SOME n_target` kall_tac >>
  drule_all ptr_vars_transport_eval_source >>
  disch_then (qx_choose_then `r` strip_assume_tac) >>
  qpat_x_assum `eval_operand sop t = SOME rt` kall_tac >>
  drule_all ptr_vars_transport_eval_source >>
  disch_then (qx_choose_then `d` strip_assume_tac) >>
  qexistsl [`d`, `r`, `n`] >>
  simp[step_inst_non_invoke, step_inst_base_def]
QED
