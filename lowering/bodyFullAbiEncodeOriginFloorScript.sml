Theory bodyFullAbiEncodeOriginFloor
Ancestors
  fragGasOriginPtr fragGasPathPtr ptrSafetyTransport ptrDiscipline
  fragExec venomExecSemantics

Theorem abi_encode_origin_edge_allocas_from[local]:
  gas_origin_ptr_edge (D,lower,explicit,ctx,func,PG)
    (s,G,tn) marks (OK t,G',tt) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  strip_tac >> drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  gvs[exit_result_def] >>
  `?z. step_inst fuel ctx inst s = OK z` by metis_tac[] >>
  drule_all step_inst_allocas_from >> strip_tac >>
  gvs[] >>
  imp_res_tac eval_phis_allocas_from >> gvs[allocas_from_def] >>
  metis_tac[]
QED

Theorem abi_encode_origin_path_allocas_from_pair[local]:
  !cx st marks out.
    gas_origin_ptr_path cx st marks out ==>
    case (cx,st,out) of
      ((D,lower,explicit,ctx,func,PG),(s,G,tn),(r,G',tt)) =>
        !t lo. r = OK t /\ allocas_from lo s /\
          lo <= s.vs_alloca_next ==>
          allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[] >> rpt strip_tac >>
  gvs[exit_result_def] >>
  metis_tac[abi_encode_origin_edge_allocas_from]
QED

Theorem abi_encode_origin_path_allocas_from:
  gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
    (s,G,tn) marks (OK t,G',tt) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  strip_tac >> drule abi_encode_origin_path_allocas_from_pair >> simp[]
QED
