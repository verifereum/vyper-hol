(*
 * S3, Milestone 5: the lowered unit's memory obligations, as bridges from
 * the memory-safe and pointer-safe runs from the unit's entry
 *
 * The runs themselves are the exit arm of loweringRuntimeCorrect's
 * lower_vyper_runtime_unit_body_joint; these theorems take them as
 * premises and carry no source premise.
 *
 * TOP-LEVEL:
 *   lower_vyper_runtime_unit_memory_ok -- S3, from the memory-safe run
 *     through mem_safe_raw_unit_memory_ok, and from the pointer-safe run
 *     through loweringPtrCorrect's lower_vyper_runtime_unit_ptr_taint
 *   lower_vyper_runtime_unit_dload_offset_ok -- S3's no-wrap bound on
 *     DLOAD/DLOADBYTES offsets, from the memory-safe run's DLOAD check
 *   lower_vyper_runtime_unit_dload_headroom_ok -- LowerDload's scratch
 *     headroom, from alloca_frontier_inv and lowering_context_ok
 *)
Theory loweringMemCorrect
Ancestors
  stmtSimDefs
  loweringPosts
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps valueEncodingProofs vyperInterpreter vyperContext
  venomExecSemantics venomState compileEnv e2eDefs supportedProgram
  compileVyper unitTransformDefs fragExec loweringHalt venomInst venomWf
  contextCodegenRel memSafeRun allocaFrontierBound o1PassContract ptrDiscipline
  vyperLoweringCorrect loweringRuntimeCorrect fragExecMem bodyMemoryDefs
  entryHaltMem loweringPtrCorrect bodySim bodySimMain moduleLowering
  stmtLowering vyperTypeSystem vyperState lowerDloadDefs
  gasSummary

val _ = Parse.hide "body";

(* ===== S3 ===== *)

(* S3, Milestone 5: the memory-safe run through the bridge
   mem_safe_raw_unit_memory_ok, with alloca_frontier_inv as the frontier
   bound, and the pointer-safe run through loweringPtrCorrect's
   lower_vyper_runtime_unit_ptr_taint, with the empty reserved region.  The
   bridge's structural premises (an entry function with an entry block,
   distinct labels, an acyclic reachable call graph, the allocation budget
   below the word size) are lowering_context_ok, which run_lowering checks.
   The other conjuncts come from run_lowering: no eom, and no reserved
   global region.  No DALLOCA is the O1 source shape's
   (o1_source_unit_ok_no_dalloca), which S4 has. *)
Theorem lower_vyper_runtime_unit_memory_ok:
  !tops rpolicy unit am tx vs fn lbl D.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    initial_venom_state_rel tops am tx vs /\
    ~ctx_has_dalloca unit.cu_context /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>)) /\
    (!fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        taint_within D unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  drule lowering_context_ok_integrity >> strip_tac >>
  drule lowering_context_ok_static_integrity >> strip_tac >>
  drule lowering_context_ok_alloca_budget >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions /\ fn.fn_name = "__entry"` by
    (imp_res_tac lookup_function_MEM >>
     imp_res_tac lookup_function_result_name >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[listTheory.EVERY_MEM] >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) unit.cu_context.ctx_functions` by
    fs[listTheory.EVERY_MEM] >>
  `reachability_closed alloca_frontier_inv unit.cu_context` by
    (irule alloca_frontier_inv_closed >> simp[]) >>
  `fn_entry_inv alloca_frontier_inv unit.cu_context fn
     (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0 |>)` by
    (irule alloca_frontier_inv_entry >>
     simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def, listTheory.MEM_MAP,
          reachable_call_graph_acyclic_def] >>
     fs[initial_venom_state_rel_def] >> metis_tac[]) >>
  `!f inst s. alloca_frontier_inv unit.cu_context f inst s ==>
              s.vs_alloca_next < dimword (:256)` by
    (rpt strip_tac >> drule alloca_frontier_inv_bound >> simp[]) >>
  drule_all mem_safe_raw_unit_memory_ok >> strip_tac >>
  drule lower_vyper_runtime_unit_raw_defaults >> strip_tac >>
  drule_all loweringPtrCorrectTheory.lower_vyper_runtime_unit_ptr_taint >> strip_tac >>
  simp[fixed_region_reserved_def]
QED

(* S3's twin for LowerDload: every reachable DLOAD/DLOADBYTES offset,
   added to the length of the code before the data section, stays below
   2^256, so LowerDload's code_end-relative CODECOPY offset does not wrap.
   The memory-safe run checks that each offset is at most the data
   section's length (inst_dload_in_section); the code and the data section
   never change, and code_layout_valid keeps the code within 2^255
   bytes. *)
Theorem lower_vyper_runtime_unit_dload_offset_ok:
  !tops rpolicy unit vs fn lbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    code_layout_valid vs /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> mem_inv dload_offset_ok unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions /\ fn.fn_name = "__entry"` by
    (imp_res_tac lookup_function_MEM >>
     imp_res_tac lookup_function_result_name >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[listTheory.EVERY_MEM] >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) unit.cu_context.ctx_functions` by
    fs[listTheory.EVERY_MEM] >>
  rewrite_tac[unitMemInvTheory.mem_inv_def, codegen_reachability_package_def] >>
  qexists_tac `\c f i s. mem_safe_point c f i s /\
                         s.vs_code = vs.vs_code /\
                         s.vs_data_section = vs.vs_data_section` >>
  rpt conj_tac
  >- (qspecl_then [`mem_safe_point`,
        `\c f i s. s.vs_code = vs.vs_code /\
                   s.vs_data_section = vs.vs_data_section`,
        `unit.cu_context`] mp_tac
        contextCodegenRelPropsTheory.reachability_closed_conj >>
      simp[mem_safe_point_closed, code_data_closed])
  >- (qexistsl_tac [`"__entry"`, `fn`, `lbl`] >> simp[] >>
      qspecl_then [`mem_safe_point`,
        `\c f i s. s.vs_code = vs.vs_code /\
                   s.vs_data_section = vs.vs_data_section`,
        `unit.cu_context`, `fn`,
        `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>`] mp_tac
        contextCodegenRelPropsTheory.fn_entry_inv_conj >>
      impl_tac >- (
        conj_tac >- (irule mem_safe_point_entry >> simp[]) >>
        qspecl_then [`unit.cu_context`, `fn`,
          `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                      vs_inst_idx := 0 |>`] mp_tac code_data_entry >>
        simp[]) >>
      simp[]) >>
  rw[dload_offset_ok_def] >>
  `inst_dload_in_section inst s` by metis_tac[mem_safe_point_dload] >>
  `w2n off <= LENGTH s.vs_data_section` by
    (fs[inst_dload_in_section_def] >> metis_tac[]) >>
  gvs[code_layout_valid_def, wordsTheory.dimword_def]
QED

(* Every reachable alloca frontier, plus 32 bytes per DLOAD in the unit,
   stays below 2^256, so LowerDload's scratch sites do not wrap:
   alloca_frontier_inv bounds the frontier by unit_alloca_budget, and
   lowering_context_ok, which run_lowering checks, leaves 32 bytes per
   DLOAD above that budget. *)
Theorem lower_vyper_runtime_unit_dload_headroom_ok:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    initial_venom_state_rel tops am tx vs
    ==> mem_inv dload_headroom_ok unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  drule lowering_context_ok_integrity >> strip_tac >>
  drule lowering_context_ok_static_integrity >> strip_tac >>
  drule lowering_context_ok_dload_budget >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions /\ fn.fn_name = "__entry"` by
    (imp_res_tac lookup_function_MEM >>
     imp_res_tac lookup_function_result_name >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[listTheory.EVERY_MEM] >>
  `?lbl. fn_entry_label fn = SOME lbl` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
  simp[unitMemInvTheory.mem_inv_def, codegen_reachability_package_def] >>
  qexists_tac `alloca_frontier_inv` >> rpt conj_tac
  >- (irule alloca_frontier_inv_closed >> simp[])
  >- (irule alloca_frontier_inv_entry >>
      simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def, listTheory.MEM_MAP,
           reachable_call_graph_acyclic_def] >>
      fs[initial_venom_state_rel_def] >> metis_tac[]) >>
  rw[dload_headroom_ok_def, alloca_frontier_inv_def, ctx_dload_count_def] >>
  fs[rich_listTheory.FILTER_FLAT, rich_listTheory.LENGTH_FLAT, listTheory.MAP_MAP_o,
     combinTheory.o_DEF] >>
  decide_tac
QED
