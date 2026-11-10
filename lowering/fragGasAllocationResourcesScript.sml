(* Allocation resources at the very endpoint of a counted safe path. *)
Theory fragGasAllocationResources
Ancestors
  fragGasPathMem allocaHistory allocaFrontierBound
  o1LowerDloadStackFrontier venomMemProofs venomExecProofs
  venomMemDefs venomExecSemantics venomState

Theorem allocation_step_frontier[local]:
  step_inst fuel ctx inst s = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_alloca_fields >> simp[]) >>
  irule ld_step_frontier_mono >> metis_tac[]
QED

Theorem allocation_edge_resources[local]:
  gas_path_mem_edge ctx func s n (OK t) /\
  fn_inst_ids_distinct func /\ alloca_inv s /\ alloca_history func s ==>
  alloca_inv t /\ alloca_history func t /\
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> fs[gas_path_mem_edge_def] >>
  gvs[fragExecTheory.exit_result_def] >>
  rpt (qpat_x_assum `OK _ = step_inst _ _ _ _` (assume_tac o SYM)) >>
  fs[fragExecTheory.exit_result_def] >>
  drule_all allocaHistoryTheory.alloca_history_step >> strip_tac >>
  drule_all alloca_inv_step_inst_proof >>
  drule allocation_step_frontier >> rpt strip_tac >> gvs[] >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
      venomStateTheory.jump_to_def] >>
  metis_tac[history_phi_entry, eval_phis_preserves_alloca_fields]
QED

Theorem gas_path_mem_allocation_resources:
  gas_path_mem ctx func s n (OK t) /\
  fn_inst_ids_distinct func /\ alloca_inv s /\ alloca_history func s ==>
  alloca_inv t /\ alloca_history func t /\
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  `!ctx func s n r. gas_path_mem ctx func s n r ==>
     !t. r = OK t ==> fn_inst_ids_distinct func /\ alloca_inv s /\
       alloca_history func s ==> alloca_inv t /\ alloca_history func t /\
       s.vs_alloca_next <= t.vs_alloca_next` suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_mem_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def] >>
  metis_tac[allocation_edge_resources, arithmeticTheory.LESS_EQ_TRANS]
QED
