Theory exprSimAbiEncodeArgsCountedLabels
Ancestors
  fragGasMode fragGasPath abiArgsObservation venomExecProofs gasOutcome gasSummary gasExemptCert exprSimDefs

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

(* This probe deliberately requires stream-independent success.  Admissibility
   alone is not a replacement for this premise. *)
Theorem abi_args_no_read_outcome_success:
  (!tail. source (es with gas_obs := tail) =
    (INL v, ee with gas_obs := tail)) /\
  gas_outcome F tops (ctx,func) source (es,s0) Q
    (\res fin r. expr_exit res r) ==>
  ?t. Q (INL v) (ee with gas_obs := []) t /\
      t.vs_labels = s0.vs_labels
Proof
  strip_tac >>
  gvs[gas_outcome_def, gas_summary_at_def]
  >- (gvs[gas_marked_exec_def] >>
      first_x_assum (qspec_then `[]` mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      qpat_x_assum `ee with gas_obs := _ = _`
        (mp_tac o Q.AP_TERM `\st. st with gas_obs := []`) >>
      simp[] >> strip_tac >>
      metis_tac[abi_args_marked_path_labels])
  >- (gvs[gas_marked_exec_def] >>
      first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
      strip_tac >> gvs[]) >>
  drule gas_exempt_cert_execution >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def]
QED
