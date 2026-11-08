Theory concretizeAnalysisAffine
Ancestors venomWfProps concretizeAnalysisSupport concretizeAnalysisBoundary ptrDiscipline
  pointerConfinedDefs removeUnusedSsaProofs basePtrDefs basePtrProofs
  list pred_set venomInst combin

Theorem fn_ptr_ok_add_exclusion:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ADD /\ inst.inst_operands = [Var x; Var y] ==>
  ~(x IN fn_pv P fn /\ y IN fn_pv P fn)
Proof
  rw[fn_ptr_ok_def, affine_pointer_ops_def, fn_pv_def] >>
  gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem fn_ptr_ok_sub_exclusion:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = SUB /\ inst.inst_operands = [Var x; Var y] ==>
  y NOTIN fn_pv P fn
Proof
  rw[fn_ptr_ok_def, affine_pointer_ops_def, fn_pv_def] >>
  gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem bp_supported_add_right_empty:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  bp_supported (fn_pv P fn) r /\ inst.inst_opcode = ADD /\
  inst.inst_operands = [Var x; Var y] /\ x IN fn_pv P fn ==>
  bp_get_ptrs r y = []
Proof
  metis_tac[fn_ptr_ok_add_exclusion, bp_supported_outside]
QED

Theorem bp_supported_add_left_empty:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  bp_supported (fn_pv P fn) r /\ inst.inst_opcode = ADD /\
  inst.inst_operands = [Var x; Var y] /\ y IN fn_pv P fn ==>
  bp_get_ptrs r x = []
Proof
  metis_tac[fn_ptr_ok_add_exclusion, bp_supported_outside]
QED

Theorem bp_supported_sub_right_empty:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  bp_supported (fn_pv P fn) r /\ inst.inst_opcode = SUB /\
  inst.inst_operands = [Var x; Var y] ==>
  bp_get_ptrs r y = []
Proof
  metis_tac[fn_ptr_ok_sub_exclusion, bp_supported_outside]
QED

Theorem bp_add_right_base_transfer:
  inst_output inst = SOME out /\ inst.inst_opcode = ADD /\
  inst.inst_operands = [Var x; Var y] /\
  bp_get_ptrs r x = [] /\ bp_get_ptrs r y <> [] ==>
  bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r y
Proof
  rpt strip_tac >>
  simp[bp_bases_def, bp_handle_inst_def, bp_get_ptrs_update,
       MAP_MAP_o, o_DEF] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[] >> Cases >>
  rename1 `Ptr a off` >> Cases_on `off` >>
  simp[offset_by_def, ptr_base_def]
QED

Theorem bp_affine_add_base_transfer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  bp_supported (fn_pv P fn) r /\ inst_output inst = SOME out /\
  inst.inst_opcode = ADD /\ inst.inst_operands = [Var x; Var y] /\
  bp_get_ptrs r x <> [] ==>
  bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r x
Proof
  rpt strip_tac >> irule bp_add_base_transfer >> simp[] >>
  metis_tac[bp_supported_add_right_empty, bp_supported_def]
QED

Theorem bp_affine_add_right_base_transfer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  bp_supported (fn_pv P fn) r /\ inst_output inst = SOME out /\
  inst.inst_opcode = ADD /\ inst.inst_operands = [Var x; Var y] /\
  bp_get_ptrs r y <> [] ==>
  bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r y
Proof
  rpt strip_tac >> irule bp_add_right_base_transfer >> simp[] >>
  metis_tac[bp_supported_add_left_empty, bp_supported_def]
QED

Theorem bp_affine_sub_base_transfer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  bp_supported (fn_pv P fn) r /\ inst_output inst = SOME out /\
  inst.inst_opcode = SUB /\ inst.inst_operands = [Var x; Var y] /\
  bp_get_ptrs r x <> [] ==>
  bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r x
Proof
  rpt strip_tac >> irule bp_sub_base_transfer >> simp[] >>
  metis_tac[bp_supported_sub_right_empty]
QED
