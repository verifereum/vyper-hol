Theory bodyPtrIntCallRunCode
Ancestors bodyPtrIntCallRunFrame venomExecProps venomInst unitShapeDefs list

Theorem intcall_context_instruction_no_setfmp:
  lowering_context_ok ctx /\ MEM fn ctx.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  inst.inst_opcode <> SETFMP
Proof
  strip_tac >> irule intcall_checked_context_no_setfmp >>
  goal_assum (drule_at Any) >> simp[] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM inst bb.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  fs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED
