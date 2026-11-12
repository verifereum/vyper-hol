Theory lowerDloadPtrExclusions
Ancestors o1PassContract ptrDiscipline venomInst dretDesugarDefs list venomExecSemantics

Theorem dload_source_instruction_exclusions:
  !D C vs f i.
    o1_src_inv D C vs /\ o1_ctx_shape C /\
    MEM f C.ctx_functions /\ MEM i (fn_insts f) ==>
    i.inst_opcode <> DRET /\
    (i.inst_opcode <> DALLOCA ==> ~is_raw_fmp_opcode i.inst_opcode)
Proof
  simp[o1_src_inv_def, o1_ctx_shape_def, fmp_free_ctx_def,
    EXISTS_MEM, EVERY_MEM] >> rpt strip_tac
  >- metis_tac[o1_fn_shape_def, no_dret_def] >>
  `o1PassContract$pre_fmp_opcode i.inst_opcode` by
    (fs[o1PassContractTheory.pre_fmp_ops_def, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `i.inst_opcode` >>
  gvs[is_raw_fmp_opcode_def, o1PassContractTheory.pre_fmp_opcode_def]
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
