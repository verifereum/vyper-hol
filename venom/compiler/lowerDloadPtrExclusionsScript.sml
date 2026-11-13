Theory lowerDloadPtrExclusions
Ancestors o1PassContract o1SafeUpto ptrDiscipline venomInst dretDesugarDefs list venomExecSemantics

Theorem dload_source_instruction_exclusions:
  !D lo cut C vs f i.
    o1_ptr_safe_upto D lo cut C vs /\ o1_ctx_shape C /\
    MEM f C.ctx_functions /\ MEM i (fn_insts f) ==>
    i.inst_opcode <> DALLOCA /\ i.inst_opcode <> DRET /\
    ~is_raw_fmp_opcode i.inst_opcode
Proof
  simp[o1_ptr_safe_upto_def, o1_ctx_shape_def, fmp_free_ctx_def,
    ctx_has_dalloca_def, EXISTS_MEM, EVERY_MEM] >> rpt strip_tac
  >- metis_tac[]
  >- metis_tac[o1_fn_shape_def, no_dret_def]
  >> metis_tac[no_raw_fmp_ops_def]
QED

Theorem dload_ptr_instruction_exclusions:
  !P f i. fn_ptr_ok P f /\ MEM i (fn_insts f) ==>
    ~MEM i.inst_opcode [MEMTOP;FMP_PARAM]
Proof
  simp[fn_ptr_ok_def, MEM] >> metis_tac[]
QED

Theorem dload_non_success_instruction_exclusions:
  !i s t. MEM i.inst_opcode [PHI;INVALID;SELFDESTRUCT] ==>
    step_inst_base i s <> OK t
Proof
  rpt strip_tac >> gvs[MEM, step_inst_base_opcode_eqs, AllCaseEqs()]
QED
