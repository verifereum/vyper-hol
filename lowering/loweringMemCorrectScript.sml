(*
 * S3, Milestone 5: the lowered unit's raw run is memory-safe
 *
 * lower_vyper_runtime_unit_run_mem_safe is composed like S1
 * (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct): the entry
 * reaches the selected function's body or reverts on the call value, the
 * body runs, and it returns or falls off its end.  Each piece is the
 * memory-safe twin of S1's: the body by bodyMemoryDefs's judgments at
 * d = NONE (an external frame has no caller return buffer), the end by
 * entryHaltMem's leaves.
 *
 * TOP-LEVEL:
 *   lower_vyper_runtime_unit_memory_ok -- S3, from the run through
 *     mem_safe_raw_unit_memory_ok, and from the pointer discipline and
 *     taint bound
 *   lower_vyper_runtime_unit_run_mem_safe -- the memory-safe run
 *   lower_vyper_runtime_unit_dload_offset_ok -- S3's no-wrap bound on
 *     DLOAD/DLOADBYTES offsets, from the memory-safe run's DLOAD check
 *   lower_vyper_runtime_unit_ptr_taint -- S3's pointer discipline and
 *     taint bound, from loweringPtrCorrect's pointer-safe run, which rests
 *     on that theory's admissions
 *
 * Pieces, each in its own theory, all memory twins of pieces S1 rests on:
 *   lower_vyper_runtime_unit_body_mem (loweringMemBodyRun) -- the run
 *     after the call value is accepted, composed from the entry bridge,
 *     the body and the frame's returns below
 *   body_stmts_sim_mem (bodyMemory) -- body_stmts_sim with memory (#641's
 *     body footprint)
 *   external_entry_value_revert_mem (loweringMemEntryRevert),
 *   external_entry_reaches_body_mem (loweringMemEntryReach) -- S1's entry
 *     bridge with memory (#639, #867)
 *   external_frame_ret_ok_mem (loweringMemFrameRet) -- the frame's returns
 *     with memory (#640),
 *     from entryHaltMem's return leaves
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
  gasSummary loweringMemEntryRevert loweringMemBodyRun

val _ = Parse.hide "body";

(* ===== S3 ===== *)

(* The run from the unit's entry is memory-safe: every instruction it
   executes, callee frames included, reads and writes memory below the
   allocation frontier (or is a revert forwarding).  Excluding
   source_exempt is essential: dynamic decoding can read unchecked
   offsets. *)
Theorem lower_vyper_runtime_unit_run_mem_safe:
  !tops rpolicy unit am tx ret vs fn lbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. mem_safe_blocks fuel unit.cu_context fn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  rpt gen_tac >> strip_tac >>
  `~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx)` by
    first_assum (ACCEPT_TAC o REWRITE_RULE [gasSummaryTheory.gas_explicit_nil] o Q.SPEC `[]`) >>
  `?mut args fbody.
     lookup_function NONE tx.function_name External tops =
       SOME (mut, F, args, [], ret, fbody) /\
     LENGTH tx.args = LENGTH args /\
     IS_SOME (bind_arguments (type_env tops) args tx.args)` by
    (fs[valid_vyper_call_def] >> metis_tac[]) >>
  `?env. bind_arguments (type_env tops) args tx.args = SOME env` by
    (Cases_on `bind_arguments (type_env tops) args tx.args` >> fs[]) >>
  Cases_on `send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <| outcomes := SOME vs.vs_outcomes; requests := [] |>)` >>
  rename1 `_ = (sres, es0)` >> Cases_on `sres`
  >- (rename1 `INL u` >> Cases_on `u` >>
      drule_all lower_vyper_runtime_unit_body_mem >> simp[]) >>
  drule_all external_entry_value_revert_mem >> simp[]
QED

(* S3's pointer discipline and taint bound: the rest of o1PassContract's
   source invariant (o1_src_inv), which the O1 pipeline's simulation (S4)
   takes beside raw_unit_memory_ok.  From the pointer-safe run
   (lower_vyper_runtime_unit_run_ptr_safe_composed) through the bridge
   ptr_safe_ptr_discipline; its distinct labels are
   lowering_context_ok's.  No DALLOCA is the O1 source shape's
   (o1_source_unit_ok_no_dalloca), which S4 has. *)
Theorem lower_vyper_runtime_unit_ptr_taint:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    ~ctx_has_dalloca unit.cu_context
    ==> ptr_discipline 0 unit.cu_context vs /\
        taint_within
          (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
          unit.cu_context vs
Proof
  rpt strip_tac >>
  `~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx)` by
    first_assum (ACCEPT_TAC o REWRITE_RULE [gasSummaryTheory.gas_explicit_nil] o Q.SPEC `[]`) >>
  drule lower_vyper_runtime_unit_run_lowering >> strip_tac >>
  drule run_lowering_context_ok >> strip_tac >>
  drule run_lowering_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions /\ fn.fn_name = "__entry"` by
    (imp_res_tac lookup_function_MEM >>
     imp_res_tac lookup_function_result_name >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[listTheory.EVERY_MEM] >>
  `?lbl. fn_entry_label fn = SOME lbl` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) unit.cu_context.ctx_functions` by
    fs[listTheory.EVERY_MEM] >>
  drule_all lower_vyper_runtime_unit_fn_ptr_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_run_ptr_safe_composed >> strip_tac >>
  `0 <= vs.vs_alloca_next` by simp[] >>
  drule_all ptrSafeRunTheory.ptr_safe_ptr_discipline >> simp[]
QED

(* S3, Milestone 5: the memory-safe run (above) through the bridge
   mem_safe_raw_unit_memory_ok, with alloca_frontier_inv as the frontier
   bound, and the pointer discipline and taint bound (above), with the
   empty reserved region.  The bridge's structural premises (an entry
   function with an entry block, distinct labels, an acyclic reachable call
   graph, the allocation budget below the word size) are
   lowering_context_ok, which run_lowering checks.  The other conjuncts
   come from run_lowering: no eom, and no reserved global region.  No
   DALLOCA is the O1 source shape's, as for the pointer discipline. *)
Theorem lower_vyper_runtime_unit_memory_ok:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    ~ctx_has_dalloca unit.cu_context
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        taint_within
          (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
          unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_run_lowering >> strip_tac >>
  drule run_lowering_context_ok >> strip_tac >>
  drule run_lowering_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  drule lowering_context_ok_integrity >> strip_tac >>
  drule lowering_context_ok_static_integrity >> strip_tac >>
  drule lowering_context_ok_alloca_budget >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions /\ fn.fn_name = "__entry"` by
    (imp_res_tac lookup_function_MEM >>
     imp_res_tac lookup_function_result_name >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[listTheory.EVERY_MEM] >>
  `?lbl. fn_entry_label fn = SOME lbl` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
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
  `!fuel. mem_safe_blocks fuel unit.cu_context fn
            (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                        vs_inst_idx := 0 |>)` by
    (drule_all lower_vyper_runtime_unit_run_mem_safe >> simp[]) >>
  drule_all mem_safe_raw_unit_memory_ok >> strip_tac >>
  drule run_lowering_eom_none >> strip_tac >>
  drule_all lower_vyper_runtime_unit_ptr_taint >> strip_tac >>
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
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    code_layout_valid vs /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx))
    ==> mem_inv dload_offset_ok unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_run_lowering >> strip_tac >>
  drule run_lowering_context_ok >> strip_tac >>
  drule run_lowering_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions /\ fn.fn_name = "__entry"` by
    (imp_res_tac lookup_function_MEM >>
     imp_res_tac lookup_function_result_name >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[listTheory.EVERY_MEM] >>
  `?lbl. fn_entry_label fn = SOME lbl` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) unit.cu_context.ctx_functions` by
    fs[listTheory.EVERY_MEM] >>
  `!fuel. mem_safe_blocks fuel unit.cu_context fn
            (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                        vs_inst_idx := 0 |>)` by
    (drule_all lower_vyper_runtime_unit_run_mem_safe >> simp[]) >>
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
  drule lower_vyper_runtime_unit_run_lowering >> strip_tac >>
  drule run_lowering_context_ok >> strip_tac >>
  drule run_lowering_entry >> strip_tac >>
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
