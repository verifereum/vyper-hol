Theory bodyPtrBopInLoopBoundary
Ancestors
  ptrDiscipline contextCodegenRel codegenRel memLocDefs list

(* These operations neither access source memory nor compare pointers.
   Loads may produce taint; this boundary checks their inputs only. *)
Theorem word_suffix_access:
  (inst.inst_opcode = AND \/ inst.inst_opcode = ISZERO \/
   inst.inst_opcode = SLOAD \/ inst.inst_opcode = TLOAD \/
   inst.inst_opcode = CALLDATALOAD \/ inst.inst_opcode = DLOAD) ==>
  access_ok lo G fn inst s
Proof
  strip_tac >>
  simp[access_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mem_read_ops_def, mem_write_ops_def]
QED

Theorem word_suffix_taint:
  (inst.inst_opcode = AND \/ inst.inst_opcode = ISZERO \/
   inst.inst_opcode = SLOAD \/ inst.inst_opcode = TLOAD \/
   inst.inst_opcode = CALLDATALOAD \/ inst.inst_opcode = DLOAD) /\
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) ==>
  taint_ok fn tn inst s
Proof
  strip_tac >>
  simp[taint_ok_def, source_memory_read_ranges_def, mem_read_ops_def] >>
  metis_tac[]
QED
