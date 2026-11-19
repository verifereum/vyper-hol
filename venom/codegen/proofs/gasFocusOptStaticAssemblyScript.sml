(* Static inputs to the optimizer's symbolic frame route. *)
Theory gasFocusOptStaticAssembly
Ancestors
  o1SymStaticPipeline o1SymStaticData venomPipelineDriverProps
  codegenAsmStaticWf codegenSymRel venomCompilerWf venomWf

Theorem focus_opt_static_assembly:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  unit_shape_ok out.po_unit /\ codegen_assembly rp out.po_unit = SOME prog /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                    ds.ds_items) unit.cu_data_segment /\
  ((?fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands) ==>
   EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) ==>
  sym_unit_static_ok out.po_unit /\ asm_static_wf prog
Proof
  strip_tac >>
  drule o1_pipeline_runtime_reference_reflects >> simp[] >> disch_tac >>
  qpat_assum `o1PipelineCorrect$o1_pipeline _ _ = _`
    (assume_tac o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
  drule_all run_venom_pipeline_bytes_only >> strip_tac >>
  drule run_venom_pipeline_success_boundary >> strip_tac >>
  conj_asm1_tac
  >- (simp[sym_unit_static_ok_def] >>
      fs[unit_wf_def, venom_wf_def] >> metis_tac[]) >>
  irule codegen_asm_static_wf >> qexistsl [`rp`, `out.po_unit`] >> simp[]
QED
