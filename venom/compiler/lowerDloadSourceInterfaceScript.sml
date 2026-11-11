Theory lowerDloadSourceInterface
Ancestors
  ptrDiscipline list pred_set fmpStepSupply dftCorrectness
  lowerDloadOpaqueExecution venomInst irSupply unitShapeDefs

Theorem ld_fn_ptr_excluded_opcodes:
  fn_ptr_ok P fn /\ MEM i (fn_insts fn) ==>
  ~MEM i.inst_opcode [MEMTOP; DRET; GETFMP; SETFMP; RETFMP; FMP_PARAM]
Proof
  simp[fn_ptr_ok_def] >> metis_tac[]
QED

Theorem ld_ctx_ptr_excluded_opcodes:
  ptr_discipline lo C vs0 /\ MEM fn C.ctx_functions /\
  MEM i (fn_insts fn) ==>
  ~MEM i.inst_opcode [MEMTOP; DRET; GETFMP; SETFMP; RETFMP; FMP_PARAM]
Proof
  strip_tac >> irule ld_fn_ptr_excluded_opcodes >>
  fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ld_original_operand_support:
  MEM i (fn_insts fn) /\ MEM (Var v) i.inst_operands ==>
  MEM v (fn_ir_vars fn)
Proof
  simp[fn_insts_def, MEM_fn_insts_blocks_iff, PULL_EXISTS,
       fn_ir_vars_member, inst_uses_def, MEM_operand_vars_iff] >>
  metis_tac[]
QED

Theorem ld_original_output_support:
  MEM i (fn_insts fn) /\ MEM v i.inst_outputs ==>
  MEM v (fn_ir_vars fn)
Proof
  simp[fn_insts_def, MEM_fn_insts_blocks_iff, PULL_EXISTS, fn_ir_vars_member] >>
  metis_tac[]
QED

Theorem ld_original_nonopaque_operand_support:
  opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  i.inst_opcode <> ASSIGN /\ i.inst_opcode <> PHI /\
  ~MEM i.inst_opcode [RET; RETFMP; DRET] /\ MEM (Var v) i.inst_operands ==>
  v IN {v | MEM v (fn_ir_vars fn) /\ ~retpc_var fn v}
Proof
  strip_tac >>
  drule_all ld_retpc_observable_operand >> strip_tac >>
  simp[] >> irule ld_original_operand_support >> metis_tac[]
QED
