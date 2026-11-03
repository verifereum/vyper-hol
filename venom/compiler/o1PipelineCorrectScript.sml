(*
 * The three planned O1 producers, PLAN §5.8 S4-S6.
 * S4 and S6 follow from the per-pass contracts (o1ContractTheorems) by the
 * composition in o1PipelineCompose; the only admissions on their path are
 * the eleven contract theorems, one per pass run.  S5 follows from the
 * output's memory invariant and the generated plan's spill layout.
 * No compiler hook or final-unit check is changed to obtain output shape.
 * run_venom_pipeline_mem_inv is the output's memory invariant in lowered
 * form, which codegen consumes.
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
 * Premises added to the original admission: the source's non-INVOKE label
 * operands are local (unit_label_refs_ok), which unit_wf does not give for
 * PHI; its entry function has no PARAM (unit_entry_no_params); no
 * function has a PHI in its first block (unit_first_block_no_phi); and
 * the initial state's dynamic-memory pointer is its initial free-memory
 * pointer (o1_run_state_ok), as the entry state has it; and the
 * context's global reservations are well-formed, which the stage
 * invariants from ConcretizeMemLoc on need for max_live_eom.
 * The runs match up to any well-formed set D of dead bytes (dead_wf):
 * ConcretizeMemLoc moves buffers, so bytes nothing reads may differ.
 * The source's other invariant rows (o1_src_inv) are premises too: no
 * function has an eom, its pointers follow the discipline above a
 * reserved fixed region, and what it writes out or returns reads only
 * bytes in D (taint_within).  No DALLOCA follows from o1_source_unit_ok. *)
Theorem run_venom_pipeline_correct:
  !D lo rpolicy unit out vs.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_label_refs_ok unit /\
    unit_entry_no_params unit /\ unit_first_block_no_phi unit /\
    o1_run_state_ok vs /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    raw_unit_memory_ok unit.cu_context vs /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\
    ptr_discipline lo unit.cu_context vs /\
    taint_within D unit.cu_context vs /\ dead_wf D
    ==>
    ctx_sim D unit.cu_context out.po_unit.cu_context vs vs
Proof
  rpt strip_tac >>
  `o1_src_inv D unit.cu_context vs` by
    (fs[o1_src_inv_def, raw_unit_memory_ok_mem_inv,
        o1_source_unit_ok_no_dalloca] >> metis_tac[]) >>
  fs[o1_pipeline_def] >>
  drule_all o1_pipeline_stage_facts >> strip_tac >> metis_tac[]
QED

(* The output's memory invariant: every access is static (below some
 * layout end) or dynamic (at or above the initial frame pointer). *)
Theorem run_venom_pipeline_mem_inv:
  !lo rpolicy unit out vs.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_label_refs_ok unit /\
    unit_entry_no_params unit /\ unit_first_block_no_phi unit /\
    o1_run_state_ok vs /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    raw_unit_memory_ok unit.cu_context vs /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\
    ptr_discipline lo unit.cu_context vs
    ==>
    ?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
          mem_inv (lowered_mem_ok eom (w2n vs.vs_initial_fmp))
            out.po_unit.cu_context vs
Proof
  rpt strip_tac >>
  (* Any well-formed dead-byte set will do; take every byte, which bounds
     any taint. *)
  qabbrev_tac `D = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                      d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf D /\ taint_within D unit.cu_context vs` by
    simp[Abbr `D`, dead_wf_def, taint_within_def] >>
  `o1_src_inv D unit.cu_context vs` by
    (fs[o1_src_inv_def, raw_unit_memory_ok_mem_inv,
        o1_source_unit_ok_no_dalloca] >> metis_tac[]) >>
  fs[o1_pipeline_def] >>
  drule_all o1_pipeline_stage_facts >> strip_tac >>
  first_x_assum (qspecl_then [`D`, `vs`] mp_tac) >> simp[] >> strip_tac >>
  fs[o1_lowered_inv_def, mem_inv_raw_reachable] >>
  rpt strip_tac >> first_x_assum drule >>
  drule raw_reachable_initial_fmp >> simp[lowered_mem_fact_def]
QED

(* ===== S5: output codegen memory obligations ===== *)

(* S5 -- Milestone 5.  The output's memory invariant
 * (run_venom_pipeline_mem_inv, so it takes that theorem's premises), the
 * plan's spill regions inside [max_live_eom, cp_initial_fmp)
 * (generate_context_plan_spill_gap) and the step write footprint, which
 * holds for every context (step_write_footprint_holds), give codegen its
 * memory obligations with raw_reachable vs as the invariant
 * (mem_inv_codegen_obligations). *)
Theorem o1_pipeline_memory_obligations:
  !lo rpolicy unit out cp vs.
    o1_pipeline rpolicy unit = SOME out /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    o1_source_unit_ok unit /\ unit_label_refs_ok unit /\
    unit_entry_no_params unit /\ unit_first_block_no_phi unit /\
    o1_run_state_ok vs /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    raw_unit_memory_ok unit.cu_context vs /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\
    ptr_discipline lo unit.cu_context vs /\
    vs.vs_initial_fmp = n2w cp.cp_initial_fmp
    ==>
    ?Inv. codegen_memory_obligations Inv out.po_unit.cu_context cp /\
          codegen_reachability_package Inv out.po_unit.cu_context vs
Proof
  rpt strip_tac >>
  drule generate_context_plan_spill_gap >> strip_tac >>
  drule_all run_venom_pipeline_mem_inv >> strip_tac >>
  gvs[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  qexists_tac `raw_reachable vs` >>
  metis_tac[mem_inv_codegen_obligations, step_write_footprint_holds]
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
