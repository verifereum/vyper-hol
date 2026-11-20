Theory requestCutLabels
Ancestors
  codegenAsmStaticWf asmSymBridge asmToBytecodeProofs symBlockBody
  codegen symbolResolve asmIR stackPlanGen unitShapeDefs finite_map list
  symBodyStaticFacts

Theorem request_cut_compute_header:
  codegen_assembly rp unit = SOME prog /\ unit_shape_ok unit /\
  ((?fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
               MEM (Label "runtime_begin") inst.inst_operands) ==>
    EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) ==>
  !fn inst l.
    MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
    MEM (AsmDataHeader l) prog
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt strip_tac >>
  `inst_shape_ok inst` by
    (fs[unit_shape_ok_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `l = "code_end"`
     >- gvs[codegen_assembly_def, AllCaseEqs(), MEM_APPEND] >>
     drule_all shaped_compute_operands_refs >> simp[] >> strip_tac >>
     qpat_x_assum `l = "runtime_begin"` SUBST_ALL_TAC >>
     `EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment` by
       (qpat_assum `_ ==> EXISTS _ unit.cu_data_segment` irule >>
        qexistsl_tac [`fn`, `inst`] >> simp[]) >>
     fs[EXISTS_MEM] >> drule symBodyStaticFactsTheory.data_segment_asm_header >> strip_tac >>
     gvs[codegen_assembly_def, AllCaseEqs(), MEM_APPEND]
QED

Theorem request_cut_compute_labels_bound:
  codegen_assembly rp unit = SOME prog /\ unit_shape_ok unit /\
  ((?fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
               MEM (Label "runtime_begin") inst.inst_operands) ==>
    EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) ==>
  !fn inst l.
    MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt strip_tac >>
  `MEM (AsmDataHeader l) prog` by
    (mp_tac (Q.INST [`rp` |-> `rp`, `unit` |-> `unit`, `prog` |-> `prog`]
      request_cut_compute_header) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (qspecl_then [`fn`,`inst`,`l`] mp_tac) >> simp[]) >>
  `l IN FDOM (SND (compute_label_offsets prog))` by
    (simp[compute_label_offsets_def, clo_step_eq] >> irule clo_FDOM >> simp[]) >>
  simp[FLOOKUP_DEF]
QED
