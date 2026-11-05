(* Checked consumer side of the successful-return interface.
   This theory does not reconstruct a source callee execution. *)
Theory lowerDloadReturnInterfaceProbe
Ancestors
  lowerDloadSafetyRunInduction lowerDloadSafetyAmbient
  lowerDloadSafetyRelation venomExecSemantics venomState venomInst list

Theorem ld_invoke_from_return:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME fn /\
  eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
  run_blocks sf C fn cs = IntRet rs cs' /\
  rs.iret_values = rt.iret_values /\
  bind_outputs inst.inst_outputs rt.iret_values target = SOME target' ==>
  ?s'. bind_outputs inst.inst_outputs rs.iret_values
         (adopt_return_fmp rs (merge_callee_state s cs')) = SOME s' /\
       step_inst sf C inst s = OK s'
Proof
  strip_tac >>
  `LENGTH inst.inst_outputs = LENGTH rs.iret_values` by
    gvs[bind_outputs_def, AllCaseEqs()] >>
  `?s'. bind_outputs inst.inst_outputs rs.iret_values
         (adopt_return_fmp rs (merge_callee_state s cs')) = SOME s'` by
    simp[bind_outputs_def] >>
  qexists `s'` >> simp[] >> once_rewrite_tac[step_inst_def] >> simp[]
QED

val _ = if null (hyp ld_invoke_from_return) then ()
        else raise Fail "invoke consumer has hypotheses";
