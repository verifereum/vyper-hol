(* Structural producers for PLAN 8.3.
 * TOP-LEVEL: compile_vyper_runtime_phases (L1),
 * type_env_all_modules_single (L12).
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

(* L12: the main module's singleton type environment is exactly type_env. *)
Theorem type_env_all_modules_single:
  type_env_all_modules [(NONE, tops)] = type_env tops
Proof
  simp[type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED
