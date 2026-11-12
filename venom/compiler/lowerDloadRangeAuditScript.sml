(* Checked zero-topic LOG descriptor/range agreement. *)
Theory lowerDloadRangeAudit
Ancestors contextCodegenRel codegenRel memLocDefs venomExecSemantics venomState venomInst words list

Theorem ld_log_zero_topics_range_audit:
  !inst s.
    inst.inst_opcode = LOG /\
    inst.inst_operands = [Lit 0w; Lit 1w; Lit 0w] ==>
    mem_read_ops inst = SOME <| iao_ofst := Lit 0w;
      iao_size := SOME (Lit 1w); iao_max_size := SOME (Lit 1w) |> /\
    source_memory_read_ranges inst s = [(0,1)]
Proof
  rpt strip_tac >>
  simp[mem_read_ops_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, eval_operands_def, eval_operand_def]
QED
