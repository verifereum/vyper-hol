Theory exprSimAbiEncodeArgsCountedLabels
Ancestors
  fragGasMode fragGasPath abiArgsObservation venomExecProofs

Theorem abi_args_gas_edge_labels[local]:
  gas_path_edge ctx func s n (OK t) ==> t.vs_labels = s.vs_labels
Proof
  rw[gas_path_edge_def] >> gvs[fragExecTheory.exit_result_def]
  >> imp_res_tac step_inst_preserves_labels_always
  >> imp_res_tac venomExecPropsTheory.eval_phis_preserves_labels
  >> gvs[venomStateTheory.jump_to_def]
  >> metis_tac[step_inst_preserves_labels_always]
QED

Theorem abi_args_gas_path_labels[local]:
  !ctx func s n r. gas_path ctx func s n r ==>
    !t. r = OK t ==> t.vs_labels = s.vs_labels
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac >> rpt strip_tac >> gvs[]
  >- metis_tac[abi_args_gas_edge_labels]
  >> gvs[fragExecTheory.exit_result_def]
QED

Theorem abi_args_marked_path_labels:
  gas_marked_path F ctx func s n (OK t) ==> t.vs_labels = s.vs_labels
Proof
  metis_tac[gas_marked_path_exec, abi_args_gas_path_labels]
QED
