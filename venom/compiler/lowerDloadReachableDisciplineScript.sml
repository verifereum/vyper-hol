Theory lowerDloadReachableDiscipline
Ancestors
  lowerDloadOwnership ptrDiscipline venomInst list pred_set

Theorem ld_annotated_taint_ok:
  ptr_discipline lo ctx vs0 /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s ==>
  taint_ok fn tn i s
Proof
  strip_tac >> drule ld_annotated_erasure >>
  fs[ptr_discipline_def] >> metis_tac[]
QED

Theorem ld_annotated_access_ok:
  ptr_discipline lo ctx vs0 /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s ==>
  access_ok lo (ld_erase AG) fn i s
Proof
  strip_tac >> drule ld_annotated_erasure >>
  fs[ptr_discipline_def] >> metis_tac[]
QED

Theorem ld_taint_operand_clean:
  taint_ok fn tn i s /\ MEM op i.inst_operands /\
  i.inst_opcode <> ASSIGN /\
  ~MEM i.inst_opcode [SHL;SHR;SAR;MSTORE;SSTORE;TSTORE;ISTORE] ==>
  op_taint tn op = {}
Proof
  simp[taint_ok_def, MEM] >> metis_tac[]
QED

Theorem ld_taint_store_address_clean:
  taint_ok fn tn i s /\
  MEM i.inst_opcode [MSTORE;SSTORE;TSTORE;ISTORE] /\
  i.inst_operands = [a;v] ==>
  op_taint tn a = {}
Proof
  simp[taint_ok_def, MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `a` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ld_taint_shift_amount_clean:
  taint_ok fn tn i s /\ MEM i.inst_opcode [SHL;SHR;SAR] /\
  i.inst_operands = [n;v] ==>
  op_taint tn n = {}
Proof
  simp[taint_ok_def, MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> metis_tac[]
QED
