Theory readonlyInvokeCopyFwdStepsAborts
Ancestors
  readonlyInvokeCopyFwdStepsControl venomExecSemantics venomExecProofs
  venomState words list

(* Only the abort reason is observable: reverted machine states need not
   agree. Static checks precede even the operand-count/output checks. *)
Theorem ricf_static_effect_abort:
  MEM inst.inst_opcode [SSTORE; TSTORE; LOG; SELFDESTRUCT; CREATE; CREATE2] /\
  s.vs_call_ctx.cc_static /\ t.vs_call_ctx.cc_static /\
  IS_SOME (eval_operands inst.inst_operands s) /\
  IS_SOME (eval_operands inst.inst_operands t) ==>
  ricf_control_result D ids stk PG fn sites maps targets H un cur curs
    (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >> fs[MEM] >>
  simp[step_inst_base_opcode_eqs, ricf_control_result_def]
QED

(* Pointer-valued offsets can differ; only availability and the value
   guard are compared. No output-envelope check precedes this abort. *)
Theorem ricf_static_call_abort:
  inst.inst_opcode = CALL /\
  inst.inst_operands = [gas; addr; value; ao; sz; ro; rs] /\
  s.vs_call_ctx.cc_static /\ t.vs_call_ctx.cc_static /\
  (!op. MEM op inst.inst_operands ==>
    IS_SOME (eval_operand op s) /\ IS_SOME (eval_operand op t)) /\
  eval_operand value s = SOME v /\ eval_operand value t = SOME v' /\
  v <> 0w /\ v' <> 0w ==>
  ricf_control_result D ids stk PG fn sites maps targets H un cur curs
    (step_inst_base inst s) (step_inst_base inst t)
Proof
  strip_tac >>
  map_every (fn q => q by metis_tac[MEM])
    [`IS_SOME (eval_operand gas s) /\ IS_SOME (eval_operand gas t)`,
     `IS_SOME (eval_operand addr s) /\ IS_SOME (eval_operand addr t)`,
     `IS_SOME (eval_operand ao s) /\ IS_SOME (eval_operand ao t)`,
     `IS_SOME (eval_operand sz s) /\ IS_SOME (eval_operand sz t)`,
     `IS_SOME (eval_operand ro s) /\ IS_SOME (eval_operand ro t)`,
     `IS_SOME (eval_operand rs s) /\ IS_SOME (eval_operand rs t)`] >>
  fs[optionTheory.IS_SOME_EXISTS] >>
  gvs[step_inst_base_opcode_eqs, ricf_control_result_def]
QED

Theorem ricf_returndatacopy_abort:
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dst; off; sz] /\
  LENGTH s.vs_returndata = LENGTH t.vs_returndata /\
  eval_operand off s = eval_operand off t /\
  eval_operand sz s = eval_operand sz t /\
  (IS_SOME (eval_operand dst s) <=> IS_SOME (eval_operand dst t)) /\
  step_inst_base inst s = Abort reason u ==>
  ?v. step_inst_base inst t = Abort reason v
Proof
  strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand dst t` >> gvs[]
QED

(* Reuse the primitive's existing inversion theorem for its output and
   size guards, independently of the relocated offset/value/salt. *)
Theorem ricf_create_abort:
  inst.inst_opcode = CREATE /\ inst.inst_operands = [value; off; sz] /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  (!op. MEM op inst.inst_operands ==>
    (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))) /\
  eval_operand sz s = eval_operand sz t /\
  step_inst_base inst s = Abort reason u ==>
  ?v. step_inst_base inst t = Abort reason v
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) =
   IS_SOME (eval_operands inst.inst_operands t)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `t.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands t)`
  >- gvs[step_inst_base_opcode_eqs] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(), exec_create_abort_iff] >>
  Cases_on `eval_operand value t` >> Cases_on `eval_operand off t` >>
  gvs[exec_create_abort_iff, MEM] >> metis_tac[optionTheory.IS_SOME_DEF]
QED

Theorem ricf_create2_abort:
  inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value; off; sz; salt] /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  (!op. MEM op inst.inst_operands ==>
    (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))) /\
  eval_operand sz s = eval_operand sz t /\
  step_inst_base inst s = Abort reason u ==>
  ?v. step_inst_base inst t = Abort reason v
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) =
   IS_SOME (eval_operands inst.inst_operands t)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `t.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands t)`
  >- gvs[step_inst_base_opcode_eqs] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(), exec_create_abort_iff] >>
  Cases_on `eval_operand value t` >> Cases_on `eval_operand off t` >>
  Cases_on `eval_operand salt t` >> gvs[exec_create_abort_iff, MEM] >> metis_tac[optionTheory.IS_SOME_DEF]
QED
