Theory ptrDisciplineTaintProps
Ancestors ptrDiscipline venomInst list pred_set

Theorem taint_ok_clean_step:
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN tn.t_mem) ==>
  taint_ok fn tn inst s
Proof
  simp[taint_ok_def, EVERY_MEM] >> metis_tac[]
QED
