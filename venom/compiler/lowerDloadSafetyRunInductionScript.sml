(* Relation-parametric successful semantic recursion interface. *)
Theory lowerDloadSafetyRunInduction
Ancestors
  venomExecSemantics venomExecProofs venomState venomInst list

Theorem ld_invoke_success:
  inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst s = OK t ==>
  ?nm ops callee args cs ret cs'.
    decode_invoke inst = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    run_blocks fuel ctx callee cs = IntRet ret cs' /\
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s cs')) = SOME t
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[step_inst_def] >> simp[AllCaseEqs()] >> metis_tac[]
QED

