(* Compile-time contexts for the ordinary slice pipeline. *)
Theory exprSimSliceOrdinaryContext
Ancestors
  exprSimSliceMemory exprSimSliceData exprLoweringProps fragExec
  builtinBytes compileEnv pair arithmetic context exprLowering

Theorem slice_bounds_ci_mono[local]:
  !start len size sa.
    ci_mono sa (SND (compile_assert_slice_bounds start len size sa))
Proof
  rpt gen_tac >>
  rewrite_tac[compile_assert_slice_bounds_def] >>
  rpt (irule ci_mono_bind >> reverse conj_tac >- simp[ci_mono_emit_op] >>
       rpt gen_tac >> BETA_TAC) >> simp[ci_mono_emit_void]
QED

Theorem slice_data_ci_mono:
  !size data start len out sa.
    ci_mono sa (SND (compile_slice_data size data start len out sa))
Proof
  rpt gen_tac >>
  rewrite_tac[compile_slice_data_def] >>
  irule ci_mono_ignore_bind >> conj_tac >- simp[slice_bounds_ci_mono] >>
  gen_tac >> irule ci_mono_bind >> reverse conj_tac
  >- simp[ci_mono_compile_alloc_buffer] >>
  rpt gen_tac >> BETA_TAC >>
  irule ci_mono_bind >> reverse conj_tac >- simp[ci_mono_comp_return] >>
  rpt gen_tac >> BETA_TAC >>
  ntac 2 (irule ci_mono_bind >> reverse conj_tac >- simp[ci_mono_emit_op] >>
          rpt gen_tac >> BETA_TAC) >>
  ntac 2 (irule ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >>
          gen_tac) >>
  simp[ci_mono_comp_return]
QED

Theorem slice_fixed_capture_ci_mono:
  compile_alloc_buffer 32 sa = (alloc,sm) /\
  emit_void MSTORE [alloc.buf_operand; src] sm = (u,sb) ==>
  ci_mono sa sb
Proof
  strip_tac >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_emit_void, SND] >>
  fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]
QED

Theorem slice_pipeline_code_context:
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
  ci_mono s3 s4 /\ ci_mono s4 sb /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 s4 func /\
  fn_has_code s4 sb func /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
  local_ptrs_reserved cenv s3 /\ local_ptrs_reserved cenv s4
Proof
  strip_tac >> fs[ci_mono_def] >>
  `cs_extends s3 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s2 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s3 s4 func /\ fn_has_code s4 sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `local_ptrs_reserved cenv s2` by metis_tac[local_ptrs_reserved_next_var] >>
  `local_ptrs_reserved cenv s3` by metis_tac[local_ptrs_reserved_next_var] >>
  simp[] >> metis_tac[local_ptrs_reserved_next_var]
QED

Theorem slice_ordinary_pipeline_context:
  lower_value compile_expr cenv src_ty src sa = (src_op,s1) /\
  ci_mono s1 s2 /\
  lower_value compile_expr cenv ty start s2 = (start_op,s3) /\
  lower_value compile_expr cenv ty len s3 = (len_op,s4) /\
  as_ptr_val out_ty LocMemory
    (compile_slice_data src_len src_data start_op len_op out_size s4) = (vv,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  ci_mono sa s1 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\ ci_mono s4 sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 s4 func /\
  fn_has_code s4 sb func /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
  local_ptrs_reserved cenv s3 /\ local_ptrs_reserved cenv s4
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s2 s3 /\ ci_mono s3 s4` by
    metis_tac[compile_expr_grows, ci_mono_def] >>
  `ci_mono s4 sb` by
    (Cases_on `compile_slice_data src_len src_data start_op len_op out_size s4` >>
     gvs[as_ptr_val_def] >> metis_tac[slice_data_ci_mono, SND]) >>
  simp[] >> irule slice_pipeline_code_context >> simp[]
QED
