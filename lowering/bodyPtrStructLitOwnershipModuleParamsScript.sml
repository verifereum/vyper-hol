Theory bodyPtrStructLitOwnershipModuleParams
Ancestors
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  moduleLowering compileEnv

Theorem alloc_run_compile_internal_param_decls:
  !params idx.
    alloc_run fresh_outputs (compile_internal_param_decls params idx)
      (\r st. fresh_outputs st)
Proof
  Induct >> simp[compile_internal_param_decls_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[compile_internal_param_decls_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[alloc_run_emit_op_fresh] >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- fs[SF ETA_ss] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_materialize_internal_params:
  !params ce.
    alloc_run fresh_outputs (materialize_internal_params ce params)
      (\ce' st. fresh_outputs st)
Proof
  Induct
  >- simp[materialize_internal_params_def, comp_return_def,
          alloc_run_def, alloc_frame_refl] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[materialize_internal_params_def] >>
  Cases_on `h1` >> simp[] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `x` >> simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[alloc_run_emit_op_fresh] >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  fs[SF ETA_ss]
QED

Theorem materialize_internal_params_alloca_locals:
  !params ce st ce' st'.
    materialize_internal_params ce params st = (ce',st') ==>
    ce'.ce_alloca_locals = ce.ce_alloca_locals
Proof
  Induct
  >- simp[materialize_internal_params_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[materialize_internal_params_def] >>
  Cases_on `h1` >> simp[]
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
      >- metis_tac[] >>
      Cases_on `x` >> simp[comp_ignore_bind_def, comp_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      first_x_assum drule >> simp[]) >>
  strip_tac >> first_x_assum drule >> simp[]
QED
