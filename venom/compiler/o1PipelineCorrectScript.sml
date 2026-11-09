(*
 * The three planned O1 producers, PLAN §5.8 S4-S6.
 * S4 and S6 follow from the per-pass contracts (o1ContractTheorems) by the
 * composition in o1PipelineCompose; the only admissions on their path are
 * the eleven contract theorems, one per pass run.  S5 follows from the
 * output's memory invariant and the generated plan's spill layout.
 * No compiler hook or final-unit check is changed to obtain output shape.
 * S4 supplies the lowered output invariant at its chosen input oracle;
 * S5 consumes that same output invariant for codegen.
 *)
Theory o1PipelineCorrect
Ancestors
  unitTransformDefs unitShapeDefs unitMemInv venomPipelineDriver
  venomPassSchedule o1PassContract o1PipelineCompose ctxLookupAgree
  ptrDiscipline contextPlanLayoutProps stepWriteFootprint
  contextCodegenRel stackPlanGen venomCompilerTypes venomState words

(* This is the compiler's existing O1 hook, with all three checks K T.
 * Naming it does not change compile_vyper or its literal pipeline hooks. *)
Definition o1_pipeline_def:
  o1_pipeline rpolicy unit =
    run_venom_pipeline (K T) (K T) (K T) rpolicy o1_pipeline_spec unit
End

(* ===== S4: semantic forward simulation ===== *)

(* The O1 source shape excludes DALLOCA. *)
Theorem o1_source_unit_ok_no_dalloca:
  o1_source_unit_ok unit ==> ~ctx_has_dalloca unit.cu_context
Proof
  rw[o1_source_unit_ok_def, ctx_has_dalloca_def, listTheory.EVERY_MEM,
     listTheory.EXISTS_MEM] >>
  CCONTR_TAC >> gvs[] >>
  rename1 `MEM i (fn_insts f)` >>
  `raw_opcode_ok i.inst_opcode` by metis_tac[] >>
  gvs[raw_opcode_ok_def]
QED

(* S4 -- Milestone 3, from the per-pass contracts.
 * Premises added to the original admission: the source's entry function
 * has no PARAM (unit_entry_no_params); every variable a use reads is
 * written on every path to it (unit_defs_reach_uses), which SimplifyCFG's
 * pre-walk needs; no function has its FMP convention set yet
 * (unit_fmp_unsealed); the initial state's dynamic-memory pointer is its
 * initial free-memory pointer (o1_run_state_ok), as the entry state has
 * it; and the
 * context's global reservations are well-formed, which the stage
 * invariants from ConcretizeMemLoc on need for max_live_eom; and every
 * DLOAD/DLOADBYTES offset stays below 2^256 once added to the code
 * prefix's length (mem_inv dload_offset_ok), so LowerDload's code_end
 * offset does not wrap; and the alloca frontier stays below 2^256 with
 * 32 bytes to spare per DLOAD (mem_inv dload_headroom_ok), so LowerDload's
 * new scratch sites do not wrap either.
 * The runs match up to any well-formed set D of dead bytes (dead_wf):
 * ConcretizeMemLoc moves buffers, so bytes nothing reads may differ.
 * The source's static invariant rows remain premises: no function has
 * an eom, and the fixed region is reserved. Raw memory safety, pointer
 * discipline, taint bounds and DLOAD bounds guard the reconstructed
 * input oracle together. No DALLOCA follows from o1_source_unit_ok. *)
Theorem run_venom_pipeline_correct:
  !D lo rpolicy unit out vs_out.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\ o1_run_state_ok vs_out /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\ dead_wf D
    ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (raw_unit_memory_ok unit.cu_context vs_in /\
       ptr_discipline lo unit.cu_context vs_in /\
       taint_within D unit.cu_context vs_in /\
       mem_inv dload_offset_ok unit.cu_context vs_in /\
       mem_inv dload_headroom_ok unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out)
Proof
  rpt strip_tac >>
  `fmp_free_ctx unit.cu_context` by (irule source_fmp_free >> fs[]) >>
  `!vi. raw_unit_memory_ok unit.cu_context vi /\
        ptr_discipline lo unit.cu_context vi /\
        taint_within D unit.cu_context vi /\
        mem_inv dload_offset_ok unit.cu_context vi /\
        mem_inv dload_headroom_ok unit.cu_context vi ==>
        o1_pre_walk_inv D unit.cu_context vi` by
    (rpt strip_tac >>
     `o1_src_inv D unit.cu_context vi` by
       (fs[o1_src_inv_def, raw_unit_memory_ok_mem_inv,
           o1_source_unit_ok_no_dalloca] >> metis_tac[]) >>
     irule o1_source_pre_walk_inv >> simp[]) >>
  fs[o1_pipeline_def] >>
  drule_all o1_pipeline_stage_facts >> strip_tac >> metis_tac[]
QED

Theorem o1_lowered_inv_fixed_pointer[local]:
  o1_lowered_inv C vs ==>
  ?eom. max_live_eom C = SOME eom /\
        mem_inv (lowered_mem_ok eom (w2n vs.vs_initial_fmp)) C vs
Proof
  strip_tac >> fs[o1_lowered_inv_def] >>
  fs[mem_inv_raw_reachable] >>
  rpt strip_tac >> first_x_assum drule >>
  drule raw_reachable_initial_fmp >> simp[lowered_mem_fact_def]
QED

(* The output's memory invariant: every access is static (below some
 * layout end) or dynamic (at or above the initial frame pointer). *)
Theorem run_venom_pipeline_mem_inv:
  !lo rpolicy unit out vs_out.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\ o1_run_state_ok vs_out /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context
    ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (raw_unit_memory_ok unit.cu_context vs_in /\
       ptr_discipline lo unit.cu_context vs_in /\
       mem_inv dload_offset_ok unit.cu_context vs_in /\
       mem_inv dload_headroom_ok unit.cu_context vs_in ==>
       ?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
             mem_inv (lowered_mem_ok eom (w2n vs_out.vs_initial_fmp))
               out.po_unit.cu_context vs_out)
Proof
  rpt strip_tac >>
  qabbrev_tac `D = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                      d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf D` by simp[Abbr `D`, dead_wf_def] >>
  drule_all run_venom_pipeline_correct >> strip_tac >>
  qexists_tac `vs_in` >> simp[] >> strip_tac >>
  `taint_within D unit.cu_context vs_in` by
    simp[Abbr `D`, taint_within_def] >>
  irule o1_lowered_inv_fixed_pointer >> metis_tac[]
QED

(* ===== S5: output codegen memory obligations ===== *)

(* S5 -- Milestone 5. The output row supplied by S4, the plan's spill
 * regions inside [max_live_eom, cp_initial_fmp), and the step write
 * footprint give codegen its memory obligations with raw_reachable vs
 * as the invariant. This consumes S4's output row without choosing
 * another input oracle. *)
Theorem o1_pipeline_memory_obligations:
  !out cp vs.
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    o1_lowered_inv out.po_unit.cu_context vs /\
    vs.vs_initial_fmp = n2w cp.cp_initial_fmp
    ==>
    ?Inv. codegen_memory_obligations Inv out.po_unit.cu_context cp /\
          codegen_reachability_package Inv out.po_unit.cu_context vs
Proof
  rpt strip_tac >>
  drule generate_context_plan_spill_gap >> strip_tac >>
  drule o1_lowered_inv_fixed_pointer >> strip_tac >>
  gvs[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  qexists_tac `raw_reachable vs` >>
  metis_tac[mem_inv_codegen_obligations, step_write_footprint_holds]
QED

(* ===== S6: output shape without new compiler checks ===== *)

(* S6 -- Milestone 3, from the per-pass contracts.
 * Premises added from the original admission: unit_entry_no_params,
 * unit_defs_reach_uses and unit_fmp_unsealed, as S4: the walk's runs
 * read their function rows (o1_fn_row), which start from these. *)
Theorem run_venom_pipeline_output_shape:
  !rpolicy unit out.
    o1_pipeline rpolicy unit = SOME out /\ o1_source_unit_ok unit /\
    unit_entry_no_params unit /\ unit_defs_reach_uses unit /\
    unit_fmp_unsealed unit
    ==> unit_shape_ok out.po_unit
Proof
  rpt strip_tac >> fs[o1_pipeline_def] >>
  drule_all o1_pipeline_stage_facts >> strip_tac >>
  irule o1_ctx_shape_unit_shape_ok >> simp[]
QED
