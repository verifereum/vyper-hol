Theory concretizePtrCopyContent
Ancestors copyFwdEquiv allocaRemapDefs ptrDiscipline codegenRel venomExecSemantics
  venomState words pred_set

(* Reuse copyFwdEquiv.mcopy_establishes_equiv, including overlapping copies.
   read_byte and mem_byte_at are the same zero-extending observation. *)
Theorem ptr_mcopy_masked_content:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop s = SOME d /\ eval_operand sop s = SOME r /\
  eval_operand nop s = SOME n /\
  eval_operand dop t = SOME dt /\ eval_operand sop t = SOME rt /\
  eval_operand nop t = SOME n /\
  (!i. i < w2n n /\ w2n r + i NOTIN tn.t_mem ==>
    read_byte (w2n r+i) s.vs_memory =
    read_byte (w2n rt+i) t.vs_memory) ==>
  ?s' t'. step_inst_base inst s = OK s' /\
    step_inst_base inst t = OK t' /\
    (!i. i < w2n n /\ w2n d+i NOTIN mem_taint tn inst s s' ==>
      read_byte (w2n d+i) s'.vs_memory =
      read_byte (w2n dt+i) t'.vs_memory)
Proof
  strip_tac >>
  simp[step_inst_base_def] >>
  rpt strip_tac >>
  `w2n r + i NOTIN tn.t_mem` by
    (gvs[mem_taint_def, written_taint_def] >> metis_tac[]) >>
  first_x_assum drule_all >>
  pure_rewrite_tac[read_byte_def, GSYM mem_byte_at_def] >>
  metis_tac[SIMP_RULE bool_ss [LET_THM] mcopy_establishes_equiv,
            arithmeticTheory.ADD_COMM]
QED
