(* The symbolic optimizer walk interprets code reads using the installed bytes. *)
Theory gasFocusOwnSetup
Ancestors
  gasFocusOptLabelFlow gasFocusOptStaticAssembly
  asmFinalizerPrefixStatic
  asmRelocDataEnv asmDataEnv asmSymBridge asmOptimizer
  fnFrameSymbolicPrefix fnPlanPlaceRevertPostamble codegenLabelDisciplined
  codegenEntrySim[qualified] codegenEntryRel
  o1PipelineCorrect venomFnInstsProofs venomState unitShapeDefs
  venomCompilerTypes asmIR finite_map list words

Theorem focus_own_finalizer_setup:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  unit_shape_ok out.po_unit /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  (fin = asm_opt_finalizer ==>
     label_flow_own_ok unit.cu_context /\
     (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
        ~MEM (Label "code_end") inst.inst_operands) /\
     EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                       ds.ds_items) unit.cu_data_segment /\
     ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                 MEM inst (fn_insts fn) /\
                 MEM (Label "runtime_begin") inst.inst_operands) ==>
      EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment)) /\
  vs0.vs_code = assemble prog' ++ vs0.vs_data_section /\
  codegen_asm_entry_rel_reloc (lo_reloc prog prog') cpl prog vs0
    (entry_asm_state vs0 es0) ==>
  (fin = K SOME ==> prog' = prog /\
    codegenEntrySim$codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0)) /\
  (fin = asm_opt_finalizer ==>
    focus_s7_symbolic_context_own T out.po_unit prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM (asm_data_env prog' vs0.vs_code)) /\
    asm_data_env_lo_ok (lo_reloc prog prog') prog (asm_data_env prog' vs0.vs_code)
      vs0.vs_code)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (disch_tac >> gvs[combinTheory.K_THM, lo_reloc_refl,
      codegen_asm_entry_rel_reloc_def, codegenEntrySimTheory.codegen_asm_entry_rel_def]) >>
  disch_tac >>
  qpat_assum `fin = asm_opt_finalizer ==> label_flow_own_ok _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_all_then assume_tac focus_opt_label_flow_own >>
  drule_all_then strip_assume_tac focus_opt_static_assembly >>
  drule_all finalizer_prefix_static >>
  disch_then (qspec_then `vs0.vs_data_section` strip_assume_tac) >>
  mp_tac (Q.INST [`p` |-> `prog`, `q` |-> `prog'`, `code` |-> `vs0.vs_code`]
    lo_reloc_data_env) >>
  (impl_tac >- simp[]) >>
  strip_tac >> rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE simp[focus_s7_symbolic_context_own_def])
QED
