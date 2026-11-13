(* Source inputs required by the complete LOG-plan simulation.
   TOP-LEVEL: log_instruction_inputs.
   Helpers: canonical operand order and successful operand evaluation. *)
Theory logInputs
Ancestors
  venomWf venomInst venomState venomExecSemantics
  stackPlanTypes list rich_list arithmetic

Theorem log_operand_shape:
  !(tc:bytes32) (operands:operand list).
    LENGTH operands = w2n tc + 2 ==>
    ?off_op sz_op topic_ops.
      operands = REVERSE (off_op::sz_op::topic_ops) /\
      w2n tc = LENGTH topic_ops
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH (REVERSE operands) = w2n tc + 2` by simp[] >>
  Cases_on `REVERSE operands` >- (gvs[] >> decide_tac) >>
  rename1 `REVERSE operands = off_op::rest` >>
  Cases_on `rest` >- (gvs[] >> decide_tac) >>
  rename1 `REVERSE operands = off_op::sz_op::topic_ops` >>
  qexistsl_tac [`off_op`,`sz_op`,`topic_ops`] >> conj_tac
  >- (qpat_assum `REVERSE operands = _`
        (ACCEPT_TAC o REWRITE_RULE [REVERSE_REVERSE] o
         AP_TERM ``REVERSE:operand list -> operand list``)) >>
  fs[] >> decide_tac
QED

Theorem log_instruction_shape:
  !inst.
    inst.inst_opcode = LOG /\ inst_wf inst ==>
    ?tc off_op sz_op topic_ops.
      inst.inst_operands = Lit tc::REVERSE (off_op::sz_op::topic_ops) /\
      inst.inst_outputs = [] /\ w2n tc = LENGTH topic_ops
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inst_wf inst` (mp_tac o REWRITE_RULE [inst_wf_def]) >>
  qpat_assum `inst.inst_opcode = LOG` (fn th => PURE_REWRITE_TAC [th]) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `inst.inst_operands = Lit tc::operands` >>
  mp_tac (Q.SPECL [`tc`,`operands`] log_operand_shape) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `off_op` (qx_choose_then `sz_op`
    (qx_choose_then `topic_ops` strip_assume_tac))) >>
  qexistsl_tac [`tc`,`off_op`,`sz_op`,`topic_ops`] >> asm_simp_tac (srw_ss()) []
QED

Theorem log_inputs_evaluate:
  !inst tc off_op sz_op topic_ops fuel ctx vs vs'.
    inst.inst_opcode = LOG /\
    inst.inst_operands = Lit tc::REVERSE (off_op::sz_op::topic_ops) /\
    w2n tc = LENGTH topic_ops /\ step_inst fuel ctx inst vs = OK vs' ==>
    ?off sz topics.
      eval_operand off_op vs = SOME off /\ eval_operand sz_op vs = SOME sz /\
      eval_operands topic_ops vs = SOME topics
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> ONCE_REWRITE_TAC [step_inst_base_def] >>
  qpat_assum `inst.inst_opcode = LOG` (fn th => PURE_REWRITE_TAC [th]) >>
  asm_simp_tac (srw_ss()) [LET_THM, ADD_COMM, REVERSE_APPEND] >>
  Cases_on `eval_operand off_op vs` >> simp[] >>
  Cases_on `eval_operand sz_op vs` >> simp[] >>
  Cases_on `eval_operands topic_ops vs` >> simp[] >> rw[]
QED

Theorem log_instruction_inputs:
  !inst fuel ctx vs vs'.
    inst.inst_opcode = LOG /\ inst_wf inst /\
    step_inst fuel ctx inst vs = OK vs' ==>
    ?tc off_op sz_op topic_ops off sz topics.
      inst.inst_operands = Lit tc::REVERSE (off_op::sz_op::topic_ops) /\
      inst.inst_outputs = [] /\ w2n tc = LENGTH topic_ops /\
      eval_operand off_op vs = SOME off /\ eval_operand sz_op vs = SOME sz /\
      eval_operands topic_ops vs = SOME topics
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPEC `inst` log_instruction_shape) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `tc` (qx_choose_then `off_op`
    (qx_choose_then `sz_op` (qx_choose_then `topic_ops` strip_assume_tac)))) >>
  mp_tac (Q.SPECL [`inst`,`tc`,`off_op`,`sz_op`,`topic_ops`,`fuel`,`ctx`,`vs`,`vs'`]
    log_inputs_evaluate) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `off` (qx_choose_then `sz`
    (qx_choose_then `topics` strip_assume_tac))) >>
  qexistsl_tac [`tc`,`off_op`,`sz_op`,`topic_ops`,`off`,`sz`,`topics`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
