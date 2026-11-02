(*
 * The three planned O1 producers, PLAN §5.8 S4-S6.
 * S4 and S6 follow from the per-pass contracts (o1ContractTheorems) by the
 * composition in o1PipelineCompose; the only admissions on their path are
 * the nine contract theorems, one per pass tag.  S5 stays an authorized
 * planned admission.
 * No compiler hook or final-unit check is changed to obtain output shape.
 * run_venom_pipeline_mem_inv is the output's memory invariant in lowered
 * form, which codegen consumes.
 *)
Theory o1PipelineCorrect
Ancestors
  unitTransformDefs unitShapeDefs unitMemInv venomPipelineDriver
  venomPassSchedule o1PassContract o1PipelineCompose ctxLookupAgree
  contextCodegenRel stackPlanGen venomCompilerTypes venomState words

(* This is the compiler's existing O1 hook, with all three checks K T.
 * Naming it does not change compile_vyper or its literal pipeline hooks. *)
Definition o1_pipeline_def:
  o1_pipeline rpolicy unit =
    run_venom_pipeline (K T) (K T) (K T) rpolicy o1_pipeline_spec unit
End

(* ===== S4: semantic forward simulation ===== *)

(* S4 -- Milestone 3, from the per-pass contracts.
 * Premise added to the original admission: the initial state's
 * dynamic-memory pointer is its initial free-memory pointer
 * (o1_run_state_ok), as the entry state has it. *)
Theorem run_venom_pipeline_correct:
  !rpolicy unit out vs.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\
    o1_run_state_ok vs /\
    raw_unit_memory_ok unit.cu_context vs
    ==>
    checked_unit_transform_correct o1_pipeline rpolicy unit vs
Proof
  rpt strip_tac >>
  simp[checked_unit_transform_correct_def, ctx_transform_correct_ctx_sim] >>
  fs[o1_pipeline_def, raw_unit_memory_ok_mem_inv, GSYM o1_src_inv_def] >>
  drule_all o1_pipeline_stage_facts >> strip_tac >> metis_tac[]
QED

(* The output's memory invariant: every access is static (below some
 * layout end) or dynamic (at or above the initial frame pointer). *)
Theorem run_venom_pipeline_mem_inv:
  !rpolicy unit out vs.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\
    o1_run_state_ok vs /\
    raw_unit_memory_ok unit.cu_context vs
    ==>
    ?eom. mem_inv (lowered_mem_ok eom (w2n vs.vs_initial_fmp))
            out.po_unit.cu_context vs
Proof
  rpt strip_tac >>
  fs[o1_pipeline_def, raw_unit_memory_ok_mem_inv, GSYM o1_src_inv_def] >>
  drule_all o1_pipeline_stage_facts >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  fs[o1_lowered_inv_def] >>
  qexists_tac `eom` >> fs[mem_inv_raw_reachable] >>
  rpt strip_tac >> first_x_assum drule >>
  drule raw_reachable_initial_fmp >> simp[lowered_mem_fact_def]
QED

(* ===== S5: output codegen memory obligations ===== *)

(* PLANNED ADMISSION S5 -- Milestone 5.
 * Proof idea: transport below-frontier raw memory safety through O1 allocation
 * and concretization, then use the generated context-plan spill intervals.
 * Construct an invariant at actual post-PHI instruction sites, including
 * incremented ordinary continuations, terminator entries, INVOKE callee
 * entries and aggregate returns; prove reads/writes avoid every live spill
 * region and each successful step preserves its bytes. *)
Theorem o1_pipeline_memory_obligations:
  !rpolicy unit out cp vs.
    o1_pipeline rpolicy unit = SOME out /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    o1_source_unit_ok unit /\ o1_initial_state_ok vs /\
    raw_unit_memory_ok unit.cu_context vs /\
    vs.vs_initial_fmp = n2w cp.cp_initial_fmp
    ==>
    ?Inv. codegen_memory_obligations Inv out.po_unit.cu_context cp /\
          codegen_reachability_package Inv out.po_unit.cu_context vs
Proof
  cheat
QED

(* ===== S6: output shape without new compiler checks ===== *)

(* S6 -- Milestone 3, from the per-pass contracts. *)
Theorem run_venom_pipeline_output_shape:
  !rpolicy unit out.
    o1_pipeline rpolicy unit = SOME out /\ o1_source_unit_ok unit
    ==> unit_shape_ok out.po_unit
Proof
  rpt strip_tac >> fs[o1_pipeline_def] >>
  drule_all o1_pipeline_stage_facts >> strip_tac >>
  irule o1_ctx_shape_unit_shape_ok >> simp[]
QED
