(* The raw unit's DLOAD scratch bound, independent of its source run. *)
Theory loweringDloadHeadroom
Ancestors
  vyperCompiler vyperLoweringCorrect allocaFrontierBound lowerDloadDefs
  contextCodegenRel unitMemInv unitShapeDefs venomWf venomInst fcgDefs

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
