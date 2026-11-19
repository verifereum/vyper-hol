Theory bodyFullOriginAllocationGrowth
Ancestors
  fragGasOriginPtr allocationPathGrowth allocationGrowth fragExec
  venomMemDefs venomMemProofs venomExecProofs venomState

Theorem origin_edge_allocation_growth[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (q,G,tq) marks (OK t,Gf,tf) /\ alloca_inv q ==>
  alloca_inv t /\ allocation_growth q t
Proof
  strip_tac >> drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  gvs[exit_result_def] >>
  TRY (qpat_x_assum `OK _ = step_inst _ _ _ _` (assume_tac o SYM)) >>
  drule_all step_inst_allocation_growth >> strip_tac >>
  drule_all alloca_inv_step_inst_proof >> strip_tac >>
  simp[] >>
  TRY (irule alloca_inv_set_inst_idx >> simp[] >> NO_TAC) >>
  drule eval_phis_preserves_alloca_fields >> strip_tac >>
  (conj_tac
   >- (gvs[alloca_inv_def,allocas_non_overlapping_def,alloca_next_valid_def] >>
       metis_tac[]) >>
   irule allocation_growth_trans >>
   goal_assum drule >>
   irule allocation_growth_map_eq >> simp[])
QED

Theorem origin_path_allocation_growth_pair[local]:
  !cx st marks out.
    gas_origin_ptr_path cx st marks out ==>
    case (cx,st,out) of
      ((D,lo,explicit,ctx,func,PG),(q,G,tq),(r,Gf,tf)) =>
        !t. r = OK t /\ alloca_inv q ==>
            alloca_inv t /\ allocation_growth q t
Proof
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[] >> rpt strip_tac >>
  gvs[exit_result_def] >>
  metis_tac[origin_edge_allocation_growth,allocation_growth_trans]
QED

Theorem body_full_origin_path_allocation_growth:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (q,Gq,tq) marks (OK t,Gf,tf) /\ alloca_inv q ==>
  allocation_growth q t
Proof
  strip_tac >> drule origin_path_allocation_growth_pair >> simp[]
QED
