Theory runtimeSymSrcDataCustomError
Ancestors
  runtimeSymSrcDataFrame runtimeSymSrcDataExprCallbacks
  runtimeSymSrcDataExprNonCallback symbolicSourceCompilerExprFrame
  stmtLowering compileEnv

Theorem runtime_data_frame_revert_with_custom_error:
  (!t e. runtime_data_frame (compile_expr c t e)) /\
  (!v. runtime_data_frame (unwrap_value c v)) /\
  (!v b t s. runtime_data_frame (compile_store_memory c v b t s)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!a b i. runtime_data_frame (compile_abi_encode_to_buf a b i)) ==>
  runtime_data_frame (compile_revert_with_custom_error c err)
Proof
  strip_tac >>
  `!es tys. runtime_data_frame (compile_ext_call_args compile_expr c [] tys es)` by
    (rpt gen_tac >>
     match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
       (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
         (Q.GEN `R` symbolic_frame_ext_call_args))) >>
     simp[runtime_data_frame_snapshot_vv, runtime_data_frame_materialize_vv]) >>
  `!dst rows. runtime_data_frame (compile_abi_encode_values_to_buf c dst rows)` by
    simp[runtime_data_frame_abi_encode_values_to_buf] >>
  Cases_on `err` >>
  simp[compile_revert_with_custom_error_def, comp_ignore_bind_def] >>
  Cases_on `c.ce_error_info (nsid_to_string p)` >> simp[] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >>
  IF_CASES_TAC >> simp[] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >> simp[]
QED
