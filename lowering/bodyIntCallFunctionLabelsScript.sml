(* Runtime internal wrappers establish their own return-PC environment. *)
Theory bodyIntCallFunctionLabels
Ancestors
  bodyIntCallSupportedStmtLabels bodyIntCallStmtHelperLabels
  bodyIntCallStmtControlLabels bodyIntCallMaterialLabels bodyIntCallLabelFrame
  bodyIntCallLabelReservations bodyIntCallContextLabels moduleLowering
  stmtLowering compileEnv emitHelper

Theorem compiler_block_tail_materialize_internal_params_bind:
  (!bce. bce.ce_return_pc = ce.ce_return_pc ==> compiler_block_tail (k bce)) ==>
  compiler_block_tail (comp_bind (materialize_internal_params ce params) k)
Proof
  strip_tac >> irule compiler_block_tail_bind_result >>
  reverse conj_tac >- simp[compiler_block_tail_materialize_internal_params] >>
  qexists_tac `\bce. bce.ce_return_pc = ce.ce_return_pc` >>
  simp[compiler_block_tail_materialize_internal_params] >>
  metis_tac[materialize_internal_params_return_pc]
QED

Theorem compiler_label_hoare_internal_param_decls:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_internal_param_decls params start)
    (\r out. compiler_label_reservation origin pending out)
Proof
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_internal_param_decls_label_bounds]
QED

Theorem compiler_label_hoare_materialize_internal_params:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (materialize_internal_params ce params)
    (\r out. compiler_label_reservation origin pending out)
Proof
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[materialize_internal_params_label_bounds]
QED

Theorem compiler_label_hoare_materialize_internal_params_result:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (materialize_internal_params ce params)
    (\bce out. bce.ce_return_pc = ce.ce_return_pc /\
      compiler_label_reservation origin pending out)
Proof
  ho_match_mp_tac compiler_label_hoare_result >>
  simp[compiler_label_hoare_materialize_internal_params] >>
  metis_tac[materialize_internal_params_return_pc]
QED

Theorem compiler_block_tail_runtime_internal_function:
  supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists expr_internal_call_root ss ==>
  compiler_block_tail
    (compile_internal_function ce params has_buf F nkey transient view F imm_len ss ret_type)
Proof
  strip_tac >> rewrite_tac[compile_internal_function_def] >>
  simp[comp_ignore_bind_def, tuple_comp_return_bind] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (Cases_on `has_buf` >> simp[compiler_block_tail_primitives] >>
      irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]) >>
  gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_internal_param_decls] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_materialize_internal_params_bind >> gen_tac >> strip_tac >>
  BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (Cases_on `ret_type` >> simp[compiler_block_tail_primitives] >>
      IF_CASES_TAC >> simp[compiler_block_tail_primitives] >>
      irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives,
        compiler_block_tail_alloc_buffer]) >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_supported_stmts >>
      gvs[] >> metis_tac[]) >> gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_block_tail_termination_read >> gen_tac >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (Cases_on `b` >> Cases_on `ret_type` >> simp[compiler_block_tail_primitives]) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_runtime_internal_function:
  supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists expr_internal_call_root ss ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_internal_function ce params has_buf F nkey transient view F imm_len ss ret_type)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[compile_internal_function_def] >>
  simp[comp_ignore_bind_def, tuple_comp_return_bind] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (Cases_on `has_buf` >> simp[compiler_label_hoare_typed_primitives,
        compiler_label_hoare_context_primitives] >>
      irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_context_primitives]) >>
  gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_internal_param_decls] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_context_primitives] >> qx_gen_tac `return_pc` >> BETA_TAC >>
  irule compiler_label_hoare_bind >>
  qexists_tac `\bce out. bce.ce_return_pc =
    SOME (PtrVar return_pc 0) /\ compiler_label_reservation origin pending out` >>
  reverse conj_tac
  >- (ho_match_mp_tac compiler_label_hoare_result >>
      simp[compiler_label_hoare_materialize_internal_params] >>
      rpt strip_tac >> drule materialize_internal_params_return_pc >> simp[]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_pure_pre >> strip_tac >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (Cases_on `ret_type` >> simp[compiler_label_hoare_typed_primitives] >>
      IF_CASES_TAC >> simp[compiler_label_hoare_typed_primitives] >>
      irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_alloc_buffer]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_supported_stmts >> gvs[] >> metis_tac[]) >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_label_hoare_termination_read >> gen_tac >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (Cases_on `b` >> Cases_on `ret_type` >>
      simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_context_primitives]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compile_runtime_internal_function_label_bounds:
  supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists expr_internal_call_root ss ==>
  !st r out.
    compile_internal_function ce params has_buf F nkey transient view F imm_len ss ret_type st =
      (r,out) /\ compile_state_ok st ==>
    compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
    bound_labels out SUBSET (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  strip_tac >> ho_match_mp_tac compiler_label_hoare_label_bounds >> gen_tac >>
  simp[SF ETA_ss] >>
  irule (SRULE [SF ETA_ss] compiler_label_hoare_runtime_internal_function) >> metis_tac[]
QED
