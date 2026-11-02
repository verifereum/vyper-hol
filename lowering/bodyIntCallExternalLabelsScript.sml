(* Structural boundaries for external-call compilation. *)
Theory bodyIntCallExternalLabels
Ancestors
  bodyIntCallExprLabels bodyIntCallAbiLabels builtinSimple exprLowering
  bodyIntCallContextLabels bodyIntCallLabelFrame bodyIntCallLabelReservations
  compileEnv list

Theorem compiler_block_tail_select:
  compiler_block_tail (compile_select cond_op then_op else_op)
Proof
  rewrite_tac[compile_select_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_select:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_select cond_op then_op else_op)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_select_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives]
QED

Theorem compiler_block_tail_extcodesize_check:
  compiler_block_tail (compile_extcodesize_check addr)
Proof
  rewrite_tac[compile_extcodesize_check_def] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_extcodesize_check:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_extcodesize_check addr)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_extcodesize_check_def] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_return_value_decode:
  compiler_block_tail (compile_return_value_decode buf lo hi)
Proof
  rewrite_tac[compile_return_value_decode_def, comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_select] >>
       gen_tac >> BETA_TAC) >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_return_value_decode:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_return_value_decode buf lo hi)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_return_value_decode_def, comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives, compiler_label_hoare_select] >>
       gen_tac >> BETA_TAC) >> simp[compiler_label_hoare_context_primitives]
QED

Theorem compiler_block_tail_extcall_store_values:
  !vals off. compiler_block_tail (compile_extcall_store_values cenv vals buf off)
Proof
  Induct >> simp[compile_extcall_store_values_def, compiler_block_tail_primitives] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_extcall_store_values_def, LET_THM, comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_unwrap_value] >>
       gen_tac >> BETA_TAC) >>
  Cases_on `is_word_type h1` >> Cases_on `is_bytestring_type h1` >> simp[] >>
  irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives, compiler_block_tail_store_bytestring]
QED

Theorem compiler_label_hoare_extcall_store_values:
  !vals off origin pending.
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_extcall_store_values cenv vals buf off)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct
  >- simp[compile_extcall_store_values_def, compiler_label_hoare_typed_primitives] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_extcall_store_values_def, LET_THM, comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_unwrap_value] >>
       gen_tac >> BETA_TAC) >>
  Cases_on `is_word_type h1` >> Cases_on `is_bytestring_type h1` >> simp[] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_label_hoare_alloc_buffer:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_alloc_buffer sz) (\r out. compiler_label_reservation origin pending out)
Proof
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_alloc_buffer_label_bounds]
QED

Theorem compiler_block_tail_materialize_vv:
  compiler_block_tail (compile_materialize_vv cenv ty vv)
Proof
  rewrite_tac[compile_materialize_vv_def, comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer,
               compiler_block_tail_unwrap_value, compiler_block_tail_store_memory] >>
       gen_tac >> BETA_TAC) >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_materialize_vv:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_materialize_vv cenv ty vv)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_materialize_vv_def, comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_alloc_buffer, compiler_label_hoare_unwrap_value,
               compiler_label_hoare_store_memory] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_ext_call_kwarg:
  (!ty. compiler_block_tail (cfn cenv ty e)) ==>
  compiler_block_tail (compile_ext_call_kwarg cfn cenv return_type k e)
Proof
  strip_tac >> rewrite_tac[compile_ext_call_kwarg_def] >> IF_CASES_TAC
  >- (irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
      gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
      simp[compiler_block_tail_materialize_vv, compiler_block_tail_primitives]) >>
  irule compiler_block_tail_bind >>
  simp[compiler_block_tail_lower_value, compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_ext_call_kwarg:
  (!ty origin pending.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn cenv ty e) (\r out. compiler_label_reservation origin pending out)) ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_ext_call_kwarg cfn cenv return_type k e)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rpt gen_tac >> rewrite_tac[compile_ext_call_kwarg_def] >> IF_CASES_TAC
  >- (irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
      gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_materialize_vv, compiler_label_hoare_typed_primitives]) >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_lower_value, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_ext_call_kwargs:
  !es ks. EVERY (\e. !ty. compiler_block_tail (cfn cenv ty e)) es ==>
  compiler_block_tail (compile_ext_call_kwargs cfn cenv return_type ks es)
Proof
  Induct >- (Cases >> simp[compile_ext_call_kwargs_def, compiler_block_tail_primitives]) >>
  gen_tac >> Cases_on `ks` >>
  simp[compile_ext_call_kwargs_def, compiler_block_tail_primitives] >> strip_tac >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_ext_call_kwarg >> simp[]) >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> PairCases_on `x` >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_ext_call_kwargs:
  !es ks. EVERY (\e. !ty origin pending.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn cenv ty e) (\r out. compiler_label_reservation origin pending out)) es ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_ext_call_kwargs cfn cenv return_type ks es)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct
  >- (Cases >> simp[compile_ext_call_kwargs_def, compiler_label_hoare_typed_primitives]) >>
  gen_tac >> Cases_on `ks` >>
  simp[compile_ext_call_kwargs_def, compiler_label_hoare_typed_primitives] >>
  strip_tac >> rpt gen_tac >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_ext_call_kwarg >> simp[]) >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> PairCases_on `x` >> simp[compiler_label_hoare_typed_primitives]
QED
