Theory bodyFullPathFrontier
Ancestors
  fragGasOriginPtr lowerDloadFrontier venomExecProofs venomExecSemantics
  venomState fragExec abiStepAllocRecords finite_map

Theorem body_full_edge_alloca_next_mono[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK u,G',tn') ==>
  s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  gvs[exit_result_def, jump_to_def] >>
  metis_tac[ld_step_frontier_mono, eval_phis_preserves_alloca_fields,
            exit_result_def]
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


Theorem body_full_edge_allocas_extend[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK u,G',tn') ==>
  s.vs_allocas SUBMAP u.vs_allocas
Proof
  strip_tac >> drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  gvs[exit_result_def, jump_to_def] >>
  metis_tac[step_inst_allocas_extend, eval_phis_preserves_alloca_fields,
            exit_result_def]
QED

Theorem body_full_path_allocas_extend_pair[local]:
  !cx st marks out.
    gas_origin_ptr_path cx st marks out ==>
    case (cx,st,out) of
      ((D,lo,explicit,ctx,func,PG),(s,G,tn),(r,G',tn')) =>
        !u. r = OK u ==> s.vs_allocas SUBMAP u.vs_allocas
Proof
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[] >> rpt strip_tac >>
  gvs[exit_result_def] >>
  metis_tac[body_full_edge_allocas_extend, SUBMAP_TRANS]
QED

Theorem body_full_path_lookup_old:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK u,G',tn') /\
  FLOOKUP s.vs_allocas aid = SOME region ==>
  FLOOKUP u.vs_allocas aid = SOME region
Proof
  strip_tac >> drule body_full_path_allocas_extend_pair >> simp[] >>
  strip_tac >> drule_all FLOOKUP_SUBMAP >> simp[]
QED
