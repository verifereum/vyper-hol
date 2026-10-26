(* Restricted dispatcher selection: no ambient simplification of branch bodies. *)
Theory abiDecoderOpcodeSelect
Ancestors
  venomExecSemantics venomState venomInst

Theorem abi_decoder_step_ADD:
  inst.inst_opcode = ADD ==>
  step_inst_base inst s = exec_pure2 word_add inst s
Proof
  strip_tac >> pure_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >> rewrite_tac[]
QED

Theorem abi_decoder_step_JNZ:
  inst.inst_opcode = JNZ ==>
  step_inst_base inst s =
    (case inst.inst_operands of
       [cond_op; Label if_nonzero; Label if_zero] =>
         (case eval_operand cond_op s of
            SOME cond => if cond <> 0w then OK (jump_to if_nonzero s)
                         else OK (jump_to if_zero s)
          | NONE => Error "undefined condition")
     | _ => Error "jnz requires cond and 2 labels")
Proof
  strip_tac >> pure_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >> rewrite_tac[]
QED
