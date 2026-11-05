Theory loadElimNoAlloca
Ancestors
  loadElimDefs loadElimBPEmpty passSharedDefs passSharedProps
  analysisSimDefs passSimulationDefs indexedLists list pred_set

Theorem le_inst_no_alloca:
  inst.inst_opcode <> ALLOCA ==>
  (load_elim_inst ctx actions ll inst).inst_opcode <> ALLOCA
Proof
  strip_tac >> simp[load_elim_inst_def]
  >> rpt (BasicProvers.TOP_CASE_TAC >> simp[mk_assign_inst_def, mk_nop_inst_def])
QED

Theorem le_phi_no_alloca:
  MEM inst (load_phi_prepend actions lbl) ==> inst.inst_opcode <> ALLOCA
Proof
  simp[load_phi_prepend_def, phis_for_block_def, MEM_MAP] >> rpt strip_tac
  >> gvs[]
QED

Theorem le_block_no_alloca:
  (!inst. MEM inst bb.bb_instructions ==> inst.inst_opcode <> ALLOCA) ==>
  !inst. MEM inst
    (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll i. [load_elim_inst ctx actions ll i]) bb).bb_instructions ==>
    inst.inst_opcode <> ALLOCA
Proof
  strip_tac >> simp[analysis_block_transform_prepend_def, MEM_APPEND]
  >> rpt strip_tac
  >> `MEM inst (load_phi_prepend actions bb.bb_label) \/
      MEM inst (FLAT (MAPi (\idx i.
        [load_elim_inst ctx actions (df_at NONE result bb.bb_label idx) i])
        bb.bb_instructions))` by metis_tac[MEM_APPEND, TAKE_DROP]
  >> gvs[MEM_FLAT, MEM_MAPi]
  >> metis_tac[MEM_EL, le_inst_no_alloca, le_phi_no_alloca]
QED

Theorem le_one_no_alloca:
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
     inst.inst_opcode <> ALLOCA) ==>
  !bb inst. MEM bb (load_elim_one ctx cfg fn).fn_blocks /\
     MEM inst bb.bb_instructions ==> inst.inst_opcode <> ALLOCA
Proof
  strip_tac
  >> simp[load_elim_one_def, analysis_function_transform_prepend_def,
          function_map_transform_def, MEM_MAP]
  >> rpt gen_tac >> strip_tac >> gvs[]
  >> irule le_block_no_alloca >> metis_tac[]
QED

Theorem le_clear_nops_no_alloca:
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
     inst.inst_opcode <> ALLOCA) ==>
  !bb inst. MEM bb (clear_nops_function fn).fn_blocks /\
     MEM inst bb.bb_instructions ==> inst.inst_opcode <> ALLOCA
Proof
  simp[clear_nops_function_def, MEM_MAP]
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >> gvs[clear_nops_block_def, MEM_FILTER] >> metis_tac[]
QED

Theorem le_function_no_alloca:
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
     inst.inst_opcode <> ALLOCA) ==>
  !bb inst. MEM bb (load_elim_function fn).fn_blocks /\
     MEM inst bb.bb_instructions ==> inst.inst_opcode <> ALLOCA
Proof
  strip_tac >> simp[load_elim_function_def]
  >> match_mp_tac le_clear_nops_no_alloca
  >> rpt (match_mp_tac le_one_no_alloca) >> asm_rewrite_tac[]
QED

Theorem le_one_bp_empty:
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
     inst.inst_opcode <> ALLOCA) ==>
  !v. bp_get_ptrs (bp_analyze cfg' (load_elim_one ctx cfg fn)) v = []
Proof
  strip_tac >> match_mp_tac le_bp_analyze_empty
  >> match_mp_tac le_one_no_alloca >> asm_rewrite_tac[]
QED

Theorem le_function_bp_empty:
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
     inst.inst_opcode <> ALLOCA) ==>
  !v. bp_get_ptrs (bp_analyze cfg (load_elim_function fn)) v = []
Proof
  strip_tac >> match_mp_tac le_bp_analyze_empty
  >> match_mp_tac le_function_no_alloca >> asm_rewrite_tac[]
QED
