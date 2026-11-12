(* Local exclusion of literal-address loads at the counted lo=0 boundary.
   This does not establish reachability of a return instruction. *)
Theory bodyPtrStructLitCallExclusion
Ancestors
  ptrSafeRun ptrDiscipline contextCodegenRel venomExecSemantics
  venomInst venomState finite_map memLocDefs

Theorem literal_mload_not_access_ok:
  !G fn inst s a.
    inst.inst_opcode = MLOAD /\ inst.inst_operands = [Lit a] /\
    ~in_revert_forward fn s ==>
    ~access_ok 0 G fn inst s
Proof
  rpt strip_tac >>
  gvs[access_ok_def, source_memory_read_ranges_def,
      eval_operand_def, mem_read_ops_def]
QED

Theorem literal_mload_not_ptr_safe_step:
  !D fuel ctx fn PG G tn inst s a.
    inst.inst_opcode = MLOAD /\ inst.inst_operands = [Lit a] /\
    ~in_revert_forward fn s ==>
    ~ptr_safe_step D 0 fuel ctx fn PG G tn inst s
Proof
  rpt strip_tac >> drule ptr_safe_step_inst_ok >>
  pure_rewrite_tac[ptr_inst_ok_def] >> strip_tac >>
  metis_tac[literal_mload_not_access_ok]
QED
