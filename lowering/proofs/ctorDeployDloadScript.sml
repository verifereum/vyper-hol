(* DLOAD offset and headroom invariants of the raw deployment unit (the deploy
 * counterparts of lower_vyper_runtime_unit_dload_offset_ok/_headroom_ok);
 * the constructor arguments are the data section.
 * TOP-LEVEL: deploy_unit_dload_ok (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployDload
Ancestors
  ctorDeployDefs o1PassContract unitMemInv lowerDloadDefs
  deployUnitProducers allocaFrontierBound contextCodegenRel venomWf
  vyperCompiler venomInst

(* Every reachable alloca frontier, plus 32 bytes per DLOAD in the unit,
   stays below 2^256 (the deploy twin of
   lower_vyper_runtime_unit_dload_headroom_ok): alloca_frontier_inv bounds
   the frontier by unit_alloca_budget from frontier 0 at the entry, and
   lowering_context_ok, which run_deploy_lowering checks, leaves 32 bytes
   per DLOAD above that budget. *)
Theorem deploy_unit_dload_headroom_ok:
  !tops rpolicy runtime_bc dunit vs.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    vs.vs_alloca_next = 0
    ==> mem_inv dload_headroom_ok dunit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  drule lower_vyper_deploy_unit_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  drule lowering_context_ok_integrity >> strip_tac >>
  drule lowering_context_ok_static_integrity >> strip_tac >>
  drule lowering_context_ok_dload_budget >> strip_tac >>
  `MEM func dunit.cu_context.ctx_functions /\ func.fn_name = "__deploy"` by
    metis_tac[lookup_function_MEM, lookup_function_result_name] >>
  `ALL_DISTINCT (fn_labels func) /\ fn_has_entry func` by
    fs[listTheory.EVERY_MEM] >>
  `?lbl. fn_entry_label func = SOME lbl` by
    (Cases_on `func.fn_blocks` >>
     gvs[fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
  simp[mem_inv_def, codegen_reachability_package_def] >>
  qexists_tac `alloca_frontier_inv` >> rpt conj_tac
  >- (irule alloca_frontier_inv_closed >> simp[])
  >- (irule alloca_frontier_inv_entry >>
      simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def,
           listTheory.MEM_MAP, reachable_call_graph_acyclic_def] >>
      metis_tac[]) >>
  rw[dload_headroom_ok_def, alloca_frontier_inv_def, ctx_dload_count_def] >>
  fs[rich_listTheory.FILTER_FLAT, rich_listTheory.LENGTH_FLAT,
     listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  decide_tac
QED

Theorem deploy_unit_dload_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (entry_venom_state prog cplan es) /\
    code_layout_valid vs /\
    ~deploy_source_exempt tops (load_contract NONE [] am tx [(NONE, tops)] [])
    ==>
    mem_inv dload_offset_ok dunit.cu_context vs /\
    mem_inv dload_headroom_ok dunit.cu_context vs
Proof
  cheat
QED
