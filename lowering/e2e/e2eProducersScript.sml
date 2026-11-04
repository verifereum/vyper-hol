(* Structural producers for PLAN 8.3.
 * TOP-LEVEL: compile_vyper_runtime_phases (L1),
 * type_env_all_modules_single (L12), o1_pipeline_codegen_obligations (L5),
 * entry_venom_state_initial_venom_state_rel (L6),
 * entry_venom_state_o1_initial_state_ok (L7),
 * entry_venom_state_initial_ctx_rel (L8).
 * Helper: codegen_assembly_success_shape (V8).
 * Only definitions and proved phase/finalizer facts are used: no S1-S7
 * correctness theorem is a logical dependency. In particular, the O1 owner
 * is imported for its pipeline definition, not its planned admissions.
 * Direction: compilePhasesProps + clean e2eDefs -> e2eProducers;
 * there is no dependency on configuredE2ECorrectness/e2eCorrectness.
 *)
Theory e2eProducers
Ancestors
  compilePhasesProps e2eDefs o1PipelineCorrect
  compileVyper codegen vyperContext finite_map
  e2eEntry vyperLoweringCorrect codegenCorrectness
  unitShapeDefs unitTransformDefs contextCodegenRel contextPlanLayoutProps
  venomPipelineDriverProps venomCompilerWf venomWf

(* Helper: successful code generation exposes the actual generated plan and
   checked assembly, including the data segment and code-end header. *)
Theorem codegen_assembly_success_shape:
  codegen_assembly rpolicy unit = SOME prog ==>
  ?cp. generate_context_plan unit.cu_context = SOME cp /\
       assembly_target_safe rpolicy.rpol_target prog /\
       prog = execute_plan cp.cp_initial_fmp (context_plan_ops cp) ++
              data_segment_asm unit.cu_data_segment ++
              [AsmDataHeader "code_end"]
Proof
  simp[codegen_assembly_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> goal_assum $ drule_at Any >> simp[]
QED

(* L1: witnesses are tied to the successful compiler's policy, raw runtime
   unit, exact O1 output and generated plan, not just an existential bytecode
   equality. The finalizer is the identity profile K SOME. *)
Theorem compile_vyper_runtime_phases:
  compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) ==>
  ?rpolicy unit out prog cp.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    assembly_target_safe rpolicy.rpol_target prog /\
    prog = execute_plan cp.cp_initial_fmp (context_plan_ops cp) ++
           data_segment_asm out.po_unit.cu_data_segment ++
           [AsmDataHeader "code_end"] /\
    runtime_bc = assemble prog
Proof
  simp[compile_vyper_def] >> strip_tac >>
  drule compile_vyper_with_success_phases >> strip_tac >>
  gvs[finalize_codegen_identity, o1PipelineCorrectTheory.o1_pipeline_def,
      AllCaseEqs()] >>
  rename1 `lower_vyper_runtime_unit tops rpolicy = SOME unit` >>
  rename1 `run_venom_pipeline (K T) (K T) (K T)
             rpolicy o1_pipeline_spec unit = SOME out` >>
  qpat_x_assum `codegen_assembly rpolicy out.po_unit = SOME _`
    (strip_assume_tac o MATCH_MP codegen_assembly_success_shape) >>
  goal_assum $ drule_at Any >> gvs[]
QED

(* L5: successful syntax/structural checks supply only structural facts.
   The semantic memory obligation remains supplied by S5's caller. *)
Theorem o1_pipeline_codegen_obligations:
  !rpolicy unit out cp Inv.
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  generate_context_plan out.po_unit.cu_context = SOME cp /\
  unit_shape_ok out.po_unit /\
  codegen_memory_obligations Inv out.po_unit.cu_context cp ==>
  codegen_context_obligations Inv out.po_unit.cu_context cp
Proof
  simp[o1PipelineCorrectTheory.o1_pipeline_def] >> rpt strip_tac >>
  drule run_venom_pipeline_success_boundary >> strip_tac >>
  drule generate_context_plan_layout_wf >> strip_tac >>
  gvs[codegen_context_obligations_def, unit_wf_def, venom_wf_def,
      reachable_call_graph_acyclic_def, unit_shape_ok_def] >>
  rpt strip_tac >> drule_all entry_fn_first_lookup >> simp[]
QED

(* L6: exact source-to-Venom entry boundary, including LIVE transferred state. *)
Theorem entry_venom_state_initial_venom_state_rel:
  !tops prog am tx es cp.
  call_state_rel tops (assemble prog) am tx es ==>
  initial_venom_state_rel tops am tx (entry_venom_state prog cp es)
Proof
  rpt strip_tac >> drule entry_venom_state_source_environment >> strip_tac >>
  drule entry_venom_state_installed_section >> strip_tac >>
  gvs[call_state_rel_def, tx_block_fields_rel_def,
      initial_venom_state_rel_def, entry_venom_state_frame_fields,
      entry_venom_state_fresh]
QED

(* L7 has NO premises. *)
Theorem entry_venom_state_o1_initial_state_ok:
  !prog cp es.
  o1_initial_state_ok (entry_venom_state prog cp es)
Proof
  simp[entry_venom_state_fresh]
QED

(* L8: final fresh-frame and unit-shape boundary; the entry function is the
   first function, with no stack parameters. Labels are concrete offsets. *)
Theorem entry_venom_state_initial_ctx_rel:
  !tops prog am tx es u cp.
  call_state_rel tops (assemble prog) am tx es /\ unit_shape_ok u ==>
  initial_ctx_rel cp prog u.cu_context (entry_venom_state prog cp es) es
Proof
  rpt strip_tac >> rename1 `entry_venom_state prog cplan es` >>
  drule entry_venom_state_installed_section >> strip_tac >>
  `initial_state_rel cplan prog 0 (HD u.cu_context.ctx_functions)
     (entry_venom_state prog cplan es) es` by
    (drule entry_venom_state_first_frame >> disch_then irule >>
     gvs[unit_shape_ok_def]) >>
  gvs[unit_shape_ok_def, entry_fn_first_def, call_state_rel_def,
      initial_ctx_rel_def, entry_venom_state_fresh,
      entry_venom_state_frame_fields]
QED

(* L12: the main module's singleton type environment is exactly type_env. *)
Theorem type_env_all_modules_single:
  type_env_all_modules [(NONE, tops)] = type_env tops
Proof
  simp[type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED
