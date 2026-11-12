(* Compile-time boundaries for the special-order external slice pipeline. *)
Theory exprSimSliceExtcodeContext
Ancestors
  exprSimSliceOrdinaryContext exprLoweringProps exprLowering builtinBytes
  compileEnv pair

(* The corresponding compiler-properties theorem is local. *)
Theorem slice_extcode_bounds_ci_mono[local]:
  !start len size sa.
    ci_mono sa (SND (compile_assert_slice_bounds start len size sa))
Proof
  rpt gen_tac >> rewrite_tac[compile_assert_slice_bounds_def] >>
  rpt (irule ci_mono_bind >> reverse conj_tac >- simp[ci_mono_emit_op] >>
       rpt gen_tac >> BETA_TAC) >> simp[ci_mono_emit_void]
QED

Theorem slice_extcode_ci_mono:
  !addr start len sz sa.
    ci_mono sa (SND (compile_slice_extcode addr start len sz sa))
Proof
  rpt gen_tac >> rewrite_tac[compile_slice_extcode_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
                         slice_extcode_bounds_ci_mono, ci_mono_compile_slice_out_buf]) ORELSE
       gen_tac ORELSE strip_tac ORELSE
       (Cases_on `av` >> rewrite_tac[pairTheory.UNCURRY_DEF] >> BETA_TAC)) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
       slice_extcode_bounds_ci_mono, ci_mono_compile_slice_out_buf]
QED

Theorem slice_extcode_pipeline_context:
  lower_value compile_expr cenv ty start sa = (start_op,s1) /\
  lower_value compile_expr cenv ty len s1 = (len_op,s2) /\
  lower_value compile_expr cenv ty addr s2 = (addr_op,s3) /\
  as_ptr_val out_ty LocMemory
    (compile_slice_extcode addr_op start_op len_op out_size s3) = (vv,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sb func /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
  local_ptrs_reserved cenv s3
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3` by
    metis_tac[compile_expr_grows, ci_mono_def] >>
  `ci_mono s3 sb` by
    (Cases_on `compile_slice_extcode addr_op start_op len_op out_size s3` >>
     gvs[as_ptr_val_def] >> metis_tac[slice_extcode_ci_mono, SND]) >>
  simp[] >> mp_tac (Q.INST [`s4` |-> `sb`] slice_pipeline_code_context) >>
  simp[ci_mono_refl]
QED
