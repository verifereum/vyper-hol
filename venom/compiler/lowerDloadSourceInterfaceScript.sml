Theory lowerDloadSourceInterface
Ancestors
  ptrDiscipline list pred_set

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
