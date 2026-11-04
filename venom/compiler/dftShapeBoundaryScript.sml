Theory dftShapeBoundary
Ancestors
  o1PassContract unitShapeDefs sorting list

Theorem dft_ctx_instruction_shape:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ MEM i (fn_insts fn) ==>
  inst_shape_ok i
Proof
  simp[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, fn_shape_ok_def] >>
  metis_tac[]
QED

Theorem dft_ctx_instruction_excluded:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ MEM i (fn_insts fn) ==>
  ~MEM i.inst_opcode [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT; DJMP; OFFSET]
Proof
  strip_tac >> drule_all dft_ctx_instruction_shape >>
  simp[inst_shape_ok_def]
QED

Theorem dft_instruction_shape_perm:
  EVERY inst_shape_ok orig /\ PERM orig current ==>
  EVERY inst_shape_ok current
Proof
  metis_tac[sortingTheory.PERM_MEM_EQ, EVERY_MEM]
QED
