(* Physical memory growth at the endpoint of a counted memory-safe path. *)
Theory fragGasMemoryLength
Ancestors
  executionMemoryLength fragGasPathMem arithmetic

Theorem gas_path_mem_edge_memory_length[local]:
  gas_path_mem_edge ctx fn s n (OK t) ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rw[gas_path_mem_edge_def] >> gvs[fragExecTheory.exit_result_def]
  >> imp_res_tac step_inst_memory_length
  >>~- ([`eval_phis a ins = OK b`],
    qspecl_then [`ins`, `a`] mp_tac eval_phis_memory_length >>
     simp[] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[step_inst_memory_length]
QED

Theorem gas_path_mem_memory_length:
  gas_path_mem ctx fn s n (OK t) ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  Induct_on `gas_path_mem` >>
  simp[fragExecTheory.exit_result_def] >> rpt strip_tac >>
  metis_tac[gas_path_mem_edge_memory_length, LESS_EQ_TRANS]
QED
