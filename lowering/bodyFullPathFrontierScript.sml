Theory bodyFullPathFrontier
Ancestors
  fragGasOriginPtr lowerDloadFrontier venomExecProofs venomExecSemantics
  venomState fragExec

Theorem body_full_edge_alloca_next_mono[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK u,G',tn') ==>
  s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  gvs[exit_result_def] >>
  TRY (qpat_x_assum `OK _ = _` (assume_tac o SYM) >>
       gvs[exit_result_def] >> NO_TAC) >>
  drule ld_step_frontier_mono >> strip_tac >>
  TRY (drule eval_phis_preserves_alloca_fields >> strip_tac) >>
  gvs[]
QED

Theorem body_full_path_alloca_next_mono_pair[local]:
  !cx st marks out.
    gas_origin_ptr_path cx st marks out ==>
    case (cx,st,out) of
      ((D,lo,explicit,ctx,func,PG),(s,G,tn),(r,G',tn')) =>
        !u. r = OK u ==> s.vs_alloca_next <= u.vs_alloca_next
Proof
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[] >> rpt strip_tac >>
  gvs[exit_result_def] >>
  metis_tac[body_full_edge_alloca_next_mono, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem body_full_path_alloca_next_mono:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK u,G',tn') ==>
  s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> drule body_full_path_alloca_next_mono_pair >> simp[]
QED
