(* Operational frames for operands retained across counted argument paths. *)
Theory bodyIntCallArgPath
Ancestors
  fragGasPath fragGasMode gasSummary venomExecProps venomExecSemantics
  venomState fragExec

Theorem gas_path_edge_labels:
  gas_path_edge ctx func s n (OK t) ==> t.vs_labels = s.vs_labels
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def, jump_to_def] >>
  metis_tac[step_inst_preserves_labels_always, eval_phis_preserves_labels]
QED

Theorem gas_path_labels:
  !ctx func s n r. gas_path ctx func s n r ==>
    !t. r = OK t ==> t.vs_labels = s.vs_labels
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> drule gas_path_edge_labels >> metis_tac[]) >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem gas_marked_exec_labels:
  gas_marked_exec memory (ctx,func) source (es,s) marks res ee (OK t) ==>
  t.vs_labels = s.vs_labels
Proof
  strip_tac >> fs[gas_marked_exec_def] >>
  drule gas_marked_path_exec >> metis_tac[gas_path_labels]
QED
