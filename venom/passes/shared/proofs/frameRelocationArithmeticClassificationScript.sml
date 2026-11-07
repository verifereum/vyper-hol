Theory frameRelocationArithmeticClassification
Ancestors ptrDiscipline pointerConfinedDefs removeUnusedSsaProofs
  venomInst finite_map list pred_set

Theorem resolved_sub_right_absent:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  inst.inst_opcode = SUB /\ inst.inst_operands = [a;Var w] ==>
  FLOOKUP rv w = NONE
Proof
  rw[fn_ptr_ok_def, affine_pointer_ops_def, fn_pv_def] >>
  gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem resolved_add_right_absent:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  inst.inst_opcode = ADD /\ inst.inst_operands = [Var u;Var w] /\
  FLOOKUP rv u <> NONE ==>
  FLOOKUP rv w = NONE
Proof
  rw[fn_ptr_ok_def, affine_pointer_ops_def, fn_pv_def] >>
  gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED
