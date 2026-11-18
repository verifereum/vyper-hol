Theory gasOriginPtrLabels
Ancestors
  fragGasOriginPtrLoop fragGasOriginPtrExec fragGasOrigin fragGasOriginPtr fragExec
  venomExecProps venomExecSemantics venomState

Theorem gas_origin_edge_preserves_labels[local]:
  gas_origin_edge memory explicit ctx func s marks (OK t) ==>
  t.vs_labels = s.vs_labels
Proof
  rw[gas_origin_edge_def] >> gvs[exit_result_def] >>
  imp_res_tac step_inst_preserves_labels_always >>
  imp_res_tac eval_phis_preserves_labels >>
  gvs[jump_to_def] >> metis_tac[step_inst_preserves_labels_always]
QED

Theorem gas_origin_path_preserves_labels:
  !memory explicit ctx func s marks r.
    gas_origin_path memory explicit ctx func s marks r ==>
    !t. r = OK t ==> t.vs_labels = s.vs_labels
Proof
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac >>
  rpt strip_tac >> gvs[]
  >- metis_tac[gas_origin_edge_preserves_labels]
  >> gvs[exit_result_def]
QED

Theorem gas_origin_ptr_path_preserves_labels:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK t,G',tn') ==> t.vs_labels = s.vs_labels
Proof
  metis_tac[gas_origin_ptr_path_projections, gas_origin_path_preserves_labels]
QED
