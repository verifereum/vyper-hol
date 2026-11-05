(* Memory safety of the raw deployment unit (the deploy counterpart of
 * lower_vyper_runtime_unit_memory_ok), with no dead bytes.
 * TOP-LEVEL: deploy_unit_memory_ok (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployMemory
Ancestors
  ctorDeployDefs o1PassContract gasSummary unitTransformDefs ptrDiscipline
  ctorDeployMemoryFrontier ctorDeployMemoryRunMem ctorDeployMemoryRunPtr
  ctorDeployImmBudget

Theorem deploy_unit_memory_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] []))
    ==>
    raw_unit_memory_ok dunit.cu_context vs /\
    ptr_discipline (imm_len tops) dunit.cu_context vs /\
    taint_within (deploy_dead tops runtime_bc am tx) dunit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_unit_run_entry >> strip_tac >>
  drule_all deploy_unit_run_mem_safe >> strip_tac >>
  drule_all deploy_unit_run_ptr_safe >> strip_tac >>
  drule deploy_imm_alloca_budget_ok >> strip_tac >>
  conj_tac
  >- (qspecl_then [`imm_len tops`, `dunit.cu_context`, `"__deploy"`, `fn`,
                   `lbl`, `vs`] mp_tac lowered_unit_raw_memory_ok_from >>
      simp[] >> disch_then irule >> decide_tac) >>
  qspecl_then [`deploy_dead tops runtime_bc am tx`, `imm_len tops`, `dunit.cu_context`,
               `"__deploy"`, `fn`, `lbl`, `vs`] mp_tac lowered_unit_ptr_taint >>
  simp[]
QED
