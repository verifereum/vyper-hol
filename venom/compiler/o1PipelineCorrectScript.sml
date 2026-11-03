(*
 * The three planned O1 producers, PLAN §5.8 S4-S6.
 * S4 and S6 follow from the per-pass contracts (o1ContractTheorems) by the
 * composition in o1PipelineCompose; the only admissions on their path are
 * the eleven contract theorems, one per pass run.  S5 stays an authorized
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
 * Premises added to the original admission: the source's non-INVOKE label
 * operands are local (unit_label_refs_ok), which unit_wf does not give for
 * PHI; its entry function has no PARAM (unit_entry_no_params); no
 * function has a PHI in its first block (unit_first_block_no_phi); and
 * the initial state's dynamic-memory pointer is its initial free-memory
 * pointer (o1_run_state_ok), as the entry state has it; and the
 * context's global reservations are well-formed, which the stage
 * invariants from ConcretizeMemLoc on need for max_live_eom; and every
 * DLOAD/DLOADBYTES offset stays below 2^256 once added to the code
 * prefix's length (mem_inv dload_offset_ok), so LowerDload's code_end
 * offset does not wrap; and the alloca frontier stays below 2^256 with
 * 32 bytes to spare per DLOAD (mem_inv dload_headroom_ok), so LowerDload's
 * new scratch sites do not wrap either.
 * The runs match up to any well-formed set D of dead bytes (dead_wf):
 * ConcretizeMemLoc moves buffers, so bytes nothing reads may differ. *)
Theorem run_venom_pipeline_correct:
  !D rpolicy unit out vs.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_label_refs_ok unit /\
    unit_entry_no_params unit /\ unit_first_block_no_phi unit /\
    o1_run_state_ok vs /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    raw_unit_memory_ok unit.cu_context vs /\
    mem_inv dload_offset_ok unit.cu_context vs /\
    mem_inv dload_headroom_ok unit.cu_context vs /\ dead_wf D
    ==>
    ctx_sim D unit.cu_context out.po_unit.cu_context vs vs
Proof
  rpt strip_tac >>
  fs[o1_pipeline_def] >>
  `o1_src_inv unit.cu_context vs` by
    fs[o1_src_inv_def, raw_unit_memory_ok_mem_inv] >>
  drule_all o1_pipeline_stage_facts >> strip_tac >> metis_tac[]
QED

(* The output's memory invariant: every access is static (below some
 * layout end) or dynamic (at or above the initial frame pointer). *)
Theorem run_venom_pipeline_mem_inv:
  !rpolicy unit out vs.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_label_refs_ok unit /\
    unit_entry_no_params unit /\ unit_first_block_no_phi unit /\
    o1_run_state_ok vs /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    raw_unit_memory_ok unit.cu_context vs /\
    mem_inv dload_offset_ok unit.cu_context vs /\
    mem_inv dload_headroom_ok unit.cu_context vs
    ==>
    ?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
          mem_inv (lowered_mem_ok eom (w2n vs.vs_initial_fmp))
            out.po_unit.cu_context vs
Proof
  rpt strip_tac >>
  fs[o1_pipeline_def] >>
  `o1_src_inv unit.cu_context vs` by
    fs[o1_src_inv_def, raw_unit_memory_ok_mem_inv] >>
  drule_all o1_pipeline_stage_facts >> strip_tac >>
  (* Any well-formed dead-byte set will do; take none. *)
  first_x_assum (qspecl_then [`<| d_stor := K (K {}); d_trans := K (K {});
                                  d_imm := K {}; d_ret := K {} |>`, `vs`]
                   mp_tac) >>
  simp[dead_wf_def] >> strip_tac >>
  fs[o1_lowered_inv_def, mem_inv_raw_reachable] >>
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

(* S6 -- Milestone 3, from the per-pass contracts.
 * Premises added from the original admission: unit_label_refs_ok,
 * unit_entry_no_params and unit_first_block_no_phi, as S4. *)
Theorem run_venom_pipeline_output_shape:
  !rpolicy unit out.
    o1_pipeline rpolicy unit = SOME out /\ o1_source_unit_ok unit /\
    unit_label_refs_ok unit /\ unit_entry_no_params unit /\
    unit_first_block_no_phi unit
    ==> unit_shape_ok out.po_unit
Proof
  rpt strip_tac >> fs[o1_pipeline_def] >>
  drule_all o1_pipeline_stage_facts >> strip_tac >>
  irule o1_ctx_shape_unit_shape_ok >> simp[]
QED
