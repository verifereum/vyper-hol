(* The deployment unit's alloca frontier starts past the immutables fixed
 * region (deploy_entry_state), so every reachable frontier, plus LowerDload's
 * 32 bytes per DLOAD, is bounded by the region's size on top of the unit's
 * alloca budget; and the constructor epilogue returns the runtime code plus
 * the immutables.  run_deploy_lowering checks that the runtime code's length
 * plus these stays below 2^256.
 * TOP-LEVEL: deploy_imm_budget_ok.
 * Helpers: run_deploy_lowering_imm_budget, deploy_imm_alloca_budget_ok (the
 * bound without the runtime code, which the memory pieces use).
 *)
Theory ctorDeployImmBudget
Ancestors
  ctorDeployDefs vyperCompiler lowerDloadDefs

Theorem run_deploy_lowering_imm_budget[local]:
  run_deploy_lowering has_constructor rpolicy runtime_bc immutables_len
    constructor_args data_size ctor_internal_fns cenv stmts is_payable
    is_nonreentrant nkey use_transient entry_label = SOME unit ==>
  LENGTH runtime_bc + immutables_len + unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context < dimword (:256)
Proof
  simp[run_deploy_lowering_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  fs[ctx_dload_count_def, rich_listTheory.FILTER_FLAT,
     rich_listTheory.LENGTH_FLAT, listTheory.MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem deploy_imm_budget_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan)
    ==>
    LENGTH runtime_bc + imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context < dimword (:256)
Proof
  rw[deploy_phases_def, imm_len_def] >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[compileVyperTheory.lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  drule run_deploy_lowering_imm_budget >> simp[]
QED

Theorem deploy_imm_alloca_budget_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan)
    ==>
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context < dimword (:256)
Proof
  rpt strip_tac >> drule deploy_imm_budget_ok >> decide_tac
QED
