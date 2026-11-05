(* DLOAD offset and headroom invariants of the raw deployment unit (the deploy
 * counterparts of lower_vyper_runtime_unit_dload_offset_ok/_headroom_ok);
 * the constructor arguments are the data section.
 * TOP-LEVEL: deploy_unit_dload_ok (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployDload
Ancestors
  ctorDeployDefs o1PassContract gasSummary unitMemInv lowerDloadDefs
  ctorDeployMemoryFrontier ctorDeployMemoryRunMem ctorDeployImmBudget

Theorem deploy_unit_dload_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    code_layout_valid vs /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] []))
    ==>
    mem_inv dload_offset_ok dunit.cu_context vs /\
    mem_inv dload_headroom_ok dunit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_unit_run_entry >> strip_tac >>
  drule_all deploy_unit_run_mem_safe >> strip_tac >>
  drule deploy_imm_alloca_budget_ok >> strip_tac >>
  conj_tac
  >- (irule lowered_unit_dload_offset_ok >> metis_tac[]) >>
  irule lowered_unit_dload_headroom_ok_from >> metis_tac[]
QED
