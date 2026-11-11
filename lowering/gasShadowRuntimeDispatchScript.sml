(* Dispatch is independent of shadowed function bodies. *)
Theory gasShadowRuntimeDispatch
Ancestors
  gasShadowRuntimeOps gasShadowCompileContext gasShadowState moduleLowering
  compileEnv emitHelper list

Theorem gas_shadow_compiles_compile_selector_checks:
  !sels mid. gas_shadow_compiles (compile_selector_checks mid sels)
    (compile_selector_checks mid sels)
Proof
  Induct >> simp[compile_selector_checks_def, gas_shadow_compiles_return] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  rewrite_tac[compile_selector_checks_def, comp_ignore_bind_def] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_emit_op_same] >>
  gen_tac >> BETA_TAC >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op_same,
               gas_shadow_compiles_fresh_label,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block] >>
       gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_compile_sparse_bucket_search:
  !sels mid fb. gas_shadow_compiles (compile_sparse_bucket_search mid sels fb)
    (compile_sparse_bucket_search mid sels fb)
Proof
  Induct >> simp[compile_sparse_bucket_search_def, gas_shadow_compiles_emit_inst] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> Cases_on `h2` >>
  rewrite_tac[compile_sparse_bucket_search_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_bind, gas_shadow_compiles_emit_op_same,
               gas_shadow_compiles_fresh_label, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block, gas_shadow_compiles_return] >>
       gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_alloc_bucket_labels:
  !n. gas_shadow_compiles (alloc_bucket_labels n) (alloc_bucket_labels n)
Proof
  Induct >> simp[alloc_bucket_labels_def, gas_shadow_compiles_return,
    gas_shadow_compiles_bind, gas_shadow_compiles_emit_op_same, gas_shadow_compiles_fresh_label]
QED

Theorem gas_shadow_compiles_create_bucket_blocks:
  !mid lbls buckets fb.
  gas_shadow_compiles (create_bucket_blocks mid lbls buckets fb)
    (create_bucket_blocks mid lbls buckets fb)
Proof
  recInduct create_bucket_blocks_ind >> rpt strip_tac >>
  simp[create_bucket_blocks_def, comp_ignore_bind_def,
       gas_shadow_compiles_return, gas_shadow_compiles_bind, gas_shadow_compiles_emit_op_same,
       gas_shadow_compiles_new_block,
       gas_shadow_compiles_compile_sparse_bucket_search]
QED

Theorem gas_shadow_compiles_emit_dense_data_sections:
  !buckets metadata entry.
  gas_shadow_compiles (emit_dense_data_sections buckets metadata entry)
    (emit_dense_data_sections buckets metadata entry)
Proof
  Induct >> simp[emit_dense_data_sections_def, gas_shadow_compiles_return] >>
  rpt gen_tac >>
  simp[emit_dense_data_sections_def, comp_ignore_bind_def] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_emit_data_section] >>
  gen_tac >> BETA_TAC >> match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (ho_match_mp_tac gas_shadow_compiles_foldl >> simp[gas_shadow_compiles_return] >>
      rpt strip_tac >> pairarg_tac >>
      simp[gas_shadow_compiles_bind, gas_shadow_compiles_emit_op_same, gas_shadow_compiles_emit_data_item]) >>
  simp[]
QED

Theorem gas_shadow_compiles_compile_selector_dispatch_linear:
  gas_shadow_compiles (compile_selector_dispatch_linear sels fb)
    (compile_selector_dispatch_linear sels fb)
Proof
  rewrite_tac[compile_selector_dispatch_linear_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op_same, gas_shadow_compiles_fresh_label,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block,
               gas_shadow_compiles_compile_selector_checks] >>
       gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_emit_inst]
QED

Theorem gas_shadow_compiles_compile_selector_dispatch_sparse:
  gas_shadow_compiles (compile_selector_dispatch_sparse sels n_buckets fb)
    (compile_selector_dispatch_sparse sels n_buckets fb)
Proof
  Cases_on `n_buckets <= 1` >>
  simp[compile_selector_dispatch_sparse_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op_same, gas_shadow_compiles_fresh_label,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block,
               gas_shadow_compiles_compile_selector_checks,
               gas_shadow_compiles_alloc_bucket_labels, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_emit_data_section] >>
       gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_emit_inst, gas_shadow_compiles_create_bucket_blocks] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (ho_match_mp_tac gas_shadow_compiles_foldl >>
      simp[gas_shadow_compiles_return, gas_shadow_compiles_emit_data_item]) >>
  simp[gas_shadow_compiles_create_bucket_blocks]
QED

Theorem gas_shadow_compiles_compile_selector_dispatch_dense:
  gas_shadow_compiles
    (compile_selector_dispatch_dense sels n_buckets metadata buckets entry labels fb)
    (compile_selector_dispatch_dense sels n_buckets metadata buckets entry labels fb)
Proof
  simp[compile_selector_dispatch_dense_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op_same, gas_shadow_compiles_fresh_label,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block,
               gas_shadow_compiles_return, gas_shadow_compiles_emit_void,
               gas_shadow_compiles_emit_data_section] >>
       gen_tac >> BETA_TAC) >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (ho_match_mp_tac gas_shadow_compiles_foldl >>
      simp[gas_shadow_compiles_return, gas_shadow_compiles_bind,
           gas_shadow_compiles_emit_data_item]) >>
  simp[gas_shadow_compiles_emit_dense_data_sections]
QED
