(* Upstream #5254: an inlined return-PC binding must not evaluate the
   removed callee's label as a value. *)
Theory functionInlinerReturnPcWitness
Ancestors
  functionInlinerDefs venomExecSemantics venomState venomInst list

Theorem inlined_retpc_assigns_zero:
  !args callee outs ret_label inst out s.
    inst.inst_opcode = RETPC_PARAM /\ inst.inst_outputs = [out] ==>
    step_inst_base
      (HD (FST (rewrite_inline_inst
        (rotate_invoke_ops (Label callee::args)) outs ret_label inst
        (LENGTH args)))) s = OK (update_var out 0w s)
Proof
  rpt strip_tac >>
  simp[rotate_invoke_ops_def, rewrite_inline_inst_def,
       is_param_opcode_def, EL_APPEND_EQN, step_inst_base_def,
       eval_operand_def]
QED
