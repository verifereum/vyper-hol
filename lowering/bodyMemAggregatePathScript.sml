(* Allocation invariants for counted aggregate continuations. *)
Theory bodyMemAggregatePath
Ancestors
  fragGasPathMem venomMemProofs venomMemDefs venomExecProofs venomState

Theorem aggregate_mem_edge_alloca_inv:
  gas_path_mem_edge ctx func s n (OK u) /\ alloca_inv s ==> alloca_inv u
Proof
  rw[gas_path_mem_edge_def] >>
  imp_res_tac alloca_inv_step_inst_proof >>
  gvs[] >>
  imp_res_tac eval_phis_preserves_alloca_fields >>
  fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem aggregate_mem_path_alloca_inv:
  gas_path_mem ctx func s n (OK u) /\ alloca_inv s ==> alloca_inv u
Proof
  `!ctx func s n result. gas_path_mem ctx func s n result ==>
     !u. result = OK u ==> alloca_inv s ==> alloca_inv u`
    suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_mem_ind >>
  rpt strip_tac >> gvs[] >>
  metis_tac[aggregate_mem_edge_alloca_inv, fragExecTheory.exit_result_def]
QED
