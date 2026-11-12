Theory o1SimpleStructuralOpcodes
Ancestors
  o1MakeSsaFormats simplifyCfgInvariant singleUseExpansionSupplySim
  venomInst ctxLookupAgreeHelpers list

Theorem make_ssa_current_fn_no_returndatacopy:
  make_ssa_current_fn s fn = (fn',s') /\
  (!i. MEM i (fn_insts fn) ==> i.inst_opcode <> RETURNDATACOPY) ==>
  !i. MEM i (fn_insts fn') ==> i.inst_opcode <> RETURNDATACOPY
Proof
  simp[GSYM EVERY_MEM, fn_insts_def, fn_insts_EVERY_block] >>
  strip_tac >> ho_match_mp_tac make_ssa_current_fn_opcodes >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem simplify_cfg_fn_with_labels_opcode_absence:
  (op = RETURNDATACOPY \/ op = INVOKE) /\
  (!i. MEM i (fn_insts fn) ==> i.inst_opcode <> op) ==>
  !i. MEM i (fn_insts (FST (simplify_cfg_fn_with_labels fn))) ==>
      i.inst_opcode <> op
Proof
  simp[GSYM EVERY_MEM] >> strip_tac >>
  ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >> gvs[]
QED

Theorem sue_expand_function_supply_no_returndatacopy:
  sue_expand_function_supply s fn = (fn',s') /\
  (!i. MEM i (fn_insts fn) ==> i.inst_opcode <> RETURNDATACOPY) ==>
  !i. MEM i (fn_insts fn') ==> i.inst_opcode <> RETURNDATACOPY
Proof
  simp[GSYM EVERY_MEM] >> strip_tac >>
  ho_match_mp_tac sue_expand_function_supply_opcodes >> simp[] >>
  goal_assum (drule_at Any)
QED
