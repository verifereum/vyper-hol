Theory frameRelocationMemoryOpaque
Ancestors frameRelocationOpaque memLocDefs o1PassContract ptrDiscipline
  unitShapeDefs venomInst list

Theorem disciplined_memory_offset_not_retpc:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
  ops.iao_ofst = Var v ==>
  ~retpc_var fn v
Proof
  strip_tac >> (
  `MEM (Var v) inst.inst_operands` by
    (qpat_x_assum `_ = SOME ops` mp_tac >>
     simp[mem_write_ops_def, mem_read_ops_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> metis_tac[MEM_REVERSE, MEM]) >>
  strip_tac >> drule_all disciplined_retpc_operand_use >>
  strip_tac >> gvs[mem_write_ops_def, mem_read_ops_def])
QED
