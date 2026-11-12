Theory lowerDloadPtrJointClosureProbe
Ancestors
  lowerDloadPtrForward lowerDloadPtrAggregate ptrDiscipline
  venomExecSemantics venomState finite_map list

(* This tests a missing field of the proposed terminal formula, NOT the TASK
   antecedent or a fully reachable pair of executions. *)
Theorem terminal_variable_definedness_does_not_cover_labels:
  !base i fuel C.
    let s = base with vs_labels := FEMPTY;
        t = base with vs_labels := FEMPTY |+ ("probe",0w);
        a = i with <|inst_opcode := ASSIGN;
                     inst_operands := [Label "probe"]; inst_outputs := ["out"]|>
    in
      (!v. lookup_var v s = lookup_var v t) /\
      step_inst fuel C a s = Error "undefined operand" /\
      step_inst fuel C a t = OK (update_var "out" 0w t)
Proof
  simp[step_inst_non_invoke, step_inst_base_def, eval_operand_def,
       lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem forwarding_copy_success_reflect:
  i.inst_opcode = RETURNDATACOPY /\ i.inst_operands = [dst;off;sz] /\
  eval_operand dst s = SOME d /\
  eval_operand off s = eval_operand off t /\
  eval_operand sz s = eval_operand sz t /\
  LENGTH s.vs_returndata = LENGTH t.vs_returndata /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel C i s = OK s' /\
       s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
       s'.vs_vars = s.vs_vars /\ s'.vs_labels = s.vs_labels
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ t = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[step_inst_non_invoke, step_inst_base_def, write_memory_with_expansion_def]
QED

Theorem revert_no_reachable_successor_result:
  i.inst_opcode = REVERT ==>
  step_inst fuel C i s <> OK t /\ step_inst fuel C i s <> IntRet ret t
Proof
  strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  rename1 `i.inst_operands = a::ops` >> Cases_on `ops` >> simp[] >>
  rename1 `ops = b::rest` >> Cases_on `rest` >>
  simp[AllCaseEqs()]
QED

Theorem terminal_assign_success_reflect:
  i.inst_opcode = ASSIGN /\
  (!op. MEM op i.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  (!v. v IN U ==> op_taint tn (Var v) = op_taint un (Var v)) /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel C i s = OK s' /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next /\
    s'.vs_labels = s.vs_labels /\ t'.vs_labels = t.vs_labels /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    (!v. v IN U ==> op_taint (step_taint i s s' tn) (Var v) =
                   op_taint (step_taint i t t' un) (Var v))
Proof
  strip_tac >>
  `!s' t'. !v. v IN U ==>
    op_taint (step_taint i s s' tn) (Var v) =
    op_taint (step_taint i t t' un) (Var v)` by
      (ntac 2 gen_tac >> match_mp_tac forwarding_step_var_taint >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ t = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  rename1 `i.inst_operands = [op]` >>
  Cases_on `eval_operand op s`
  >- gvs[] >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> fs[lookup_var_def]
QED

Theorem assign_no_terminal_constructor:
  i.inst_opcode = ASSIGN ==>
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s <> IntRet ret t
Proof
  strip_tac >>
  simp[venomInstTheory.is_terminator_def, step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  rename1 `i.inst_operands = a::ops` >> Cases_on `ops` >> simp[] >>
  Cases_on `i.inst_outputs` >> simp[] >>
  rename1 `i.inst_outputs = b::outs` >> Cases_on `outs` >>
  simp[AllCaseEqs()]
QED
