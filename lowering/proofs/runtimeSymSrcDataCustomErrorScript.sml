Theory runtimeSymSrcDataCustomError
Ancestors
  runtimeSymSrcDataFrame stmtLowering compileEnv

Theorem runtime_data_frame_custom_error_store_args:
  (!t e. runtime_data_frame (compile_expr c t e)) /\
  (!v. runtime_data_frame (unwrap_value c v)) /\
  (!v b t s. runtime_data_frame (compile_store_memory c v b t s)) ==>
  !es tys dst offset.
    runtime_data_frame (compile_custom_error_store_args c es tys dst offset)
Proof
  strip_tac >> Induct >> rpt gen_tac >> Cases_on `tys` >>
  simp[compile_custom_error_store_args_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem runtime_data_frame_revert_with_custom_error:
  (!t e. runtime_data_frame (compile_expr c t e)) /\
  (!v. runtime_data_frame (unwrap_value c v)) /\
  (!v b t s. runtime_data_frame (compile_store_memory c v b t s)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!a b i. runtime_data_frame (compile_abi_encode_to_buf a b i)) ==>
  runtime_data_frame (compile_revert_with_custom_error c err)
Proof
  strip_tac >> Cases_on `err` >>
  simp[compile_revert_with_custom_error_def, comp_ignore_bind_def] >>
  Cases_on `c.ce_error_info (nsid_to_string p)` >> simp[] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac
       >- simp[runtime_data_frame_custom_error_store_args] >>
       gen_tac >> BETA_TAC) >>
  IF_CASES_TAC >> simp[] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >> simp[]
QED
