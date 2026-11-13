Theory lowerDloadPtrExpansion
Ancestors
  lowerDloadPtrAggregate lowerDloadPtrAlloc ptrDiscipline memLocDefs
  codegenRel contextCodegenRel venomExecSemantics venomState words

(* Generated copies address their destination through an original or scratch
   site.  The code source is not a memory read. *)
Theorem dload_codecopy_safe:
  inst.inst_opcode = CODECOPY /\
  inst.inst_operands = [Var dst; src; sz] /\
  FLOOKUP G dst = SOME (b,n) /\
  eval_operand (Var dst) s = SOME x /\
  eval_operand src s = SOME a /\ eval_operand sz s = SOME z /\
  b <= w2n x /\ w2n x + w2n z <= b+n /\
  op_taint tn (Var dst) = {} /\ op_taint tn src = {} /\
  op_taint tn sz = {} ==>
  access_ok lo G fn inst s /\ taint_ok fn tn inst s
Proof
  strip_tac >>
  simp[access_ok_def, taint_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, sized_source_write_range_def,
       mem_write_ops_def, mem_read_ops_def, op_prov_def] >>
  metis_tac[]
QED

Theorem dload_mload_safe:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [Var dst] /\
  FLOOKUP G dst = SOME (b,n) /\ eval_operand (Var dst) s = SOME x /\
  b <= w2n x /\ w2n x + 32 <= b+n /\
  op_taint tn (Var dst) = {} ==>
  access_ok lo G fn inst s /\ taint_ok fn tn inst s
Proof
  strip_tac >>
  simp[access_ok_def, taint_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, mem_write_ops_def, mem_read_ops_def,
       op_prov_def] >>
  metis_tac[]
QED

Theorem dload_nonmemory_safe:
  (inst.inst_opcode = ALLOCA \/ inst.inst_opcode = ADD) /\
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) ==>
  access_ok lo G fn inst s /\ taint_ok fn tn inst s
Proof
  strip_tac >>
  simp[access_ok_def, taint_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  metis_tac[]
QED
