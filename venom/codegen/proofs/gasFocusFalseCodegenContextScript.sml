Theory gasFocusFalseCodegenContext
Ancestors
  o1PipelineCorrect venomPipelineDriverProps contextPlanLayoutProps
  contextCodegenRel venomCompilerWf venomWf unitShapeDefs

(* The frame-prefix planner needs the static codegen obligations only. *)
Theorem focus_false_codegen_context:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  unit_shape_ok out.po_unit ==>
  codegen_context_obligations (\_ _ _ _. F) out.po_unit.cu_context cpl
Proof
  simp[o1PipelineCorrectTheory.o1_pipeline_def] >> strip_tac >>
  drule_then strip_assume_tac run_venom_pipeline_success_boundary >>
  drule_then assume_tac generate_context_plan_layout_wf >>
  gvs[codegen_context_obligations_def, codegen_memory_obligations_def,
      unit_wf_def, venom_wf_def, reachable_call_graph_acyclic_def,
      unit_shape_ok_def] >>
  rpt strip_tac >> drule_all entry_fn_first_lookup >> simp[]
QED
