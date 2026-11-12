Theory entryModuleScaffoldCode
Ancestors
  entryCodePredicate entryContextCodePredicate entryDecoderCode
  entryDecoderRecursiveCode moduleLowering compileEnv

Theorem entry_code_internal_param_decls:
  !params idx. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_internal_param_decls params idx)
Proof
  Induct >> simp[compile_internal_param_decls_def, entry_code_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_internal_param_decls_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return]
QED

Theorem entry_code_materialize_internal_params:
  !params ce. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (materialize_internal_params ce params)
Proof
  Induct >> simp[materialize_internal_params_def, entry_code_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[materialize_internal_params_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[] >>
  rename1 `SOME binding` >> Cases_on `binding` >> simp[] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_decode_args:
  !args ce off hi adj. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_decode_args ce args off CALLDATALOAD hi adj)
Proof
  Induct >> simp[compile_decode_args_def, entry_code_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_decode_args_def, comp_ignore_bind_def] >>
  IF_CASES_TAC
  >- (rpt (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_emit_op, entry_code_clamp_basetype] >>
        rpt gen_tac >> BETA_TAC) >>
      irule entry_code_bind >> reverse conj_tac
      >- (rpt BasicProvers.TOP_CASE_TAC >>
          simp[entry_code_return, entry_code_emit_void]) >> simp[]) >>
  IF_CASES_TAC >> BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_decode_to_buf] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_register_positional_args:
  !args ce off. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_register_positional_args ce args off)
Proof
  Induct >> simp[compile_register_positional_args_def, entry_code_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_register_positional_args_def, comp_ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_return, entry_code_decode_args] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_entry_checks:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_entry_checks min_cds payable)
Proof
  simp[compile_entry_checks_def, comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[entry_code_return] >>
      rpt (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
      simp[entry_code_emit_void]) >>
  rpt gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[entry_code_return] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_void]
QED

Theorem entry_code_selector_checks[local]:
  !sels mid. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_selector_checks mid sels)
Proof
  Induct >> simp[compile_selector_checks_def, entry_code_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_selector_checks_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_fresh_label,
            entry_code_emit_inst, entry_code_new_block] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_selector_dispatch_linear:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_selector_dispatch_linear sels fallback)
Proof
  simp[compile_selector_dispatch_linear_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_fresh_label,
            entry_code_emit_inst, entry_code_new_block,
            entry_code_selector_checks] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_inst]
QED

Theorem entry_code_fold_sequence[local]:
  !xs m. entry_preserves_code P m /\
    (!x. entry_preserves_code P (f x)) ==>
    entry_preserves_code P
      (FOLDL (\m x. comp_ignore_bind m (f x)) m xs)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> simp[comp_ignore_bind_def] >> irule entry_code_bind >> simp[]
QED

Theorem entry_code_sparse_bucket_search[local]:
  !sels mid fallback. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_sparse_bucket_search mid sels fallback)
Proof
  Induct >> simp[compile_sparse_bucket_search_def, entry_code_emit_inst] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_sparse_bucket_search_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_fresh_label] >>
    rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[entry_code_return] >>
      rpt (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
      simp[entry_code_emit_op]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_inst, entry_code_new_block] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_alloc_bucket_labels[local]:
  !n. entry_preserves_code P (alloc_bucket_labels n)
Proof
  Induct >> simp[Once alloc_bucket_labels_def, entry_code_return] >>
  irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_fresh_label] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_return]
QED

Theorem entry_code_create_bucket_blocks[local]:
  !lbls buckets mid fallback.
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (create_bucket_blocks mid lbls buckets fallback)
Proof
  Induct >> Cases_on `buckets` >>
  simp[create_bucket_blocks_def, entry_code_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[create_bucket_blocks_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_new_block, entry_code_sparse_bucket_search] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_selector_dispatch_sparse:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_selector_dispatch_sparse sels n_buckets fallback)
Proof
  simp[compile_selector_dispatch_sparse_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_fresh_label,
            entry_code_emit_inst, entry_code_new_block] >>
    rpt gen_tac >> BETA_TAC) >>
  IF_CASES_TAC >> simp[comp_ignore_bind_def]
  >- (irule entry_code_bind >>
      simp[entry_code_selector_checks, entry_code_emit_inst]) >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_bucket_labels, entry_code_return,
            entry_code_emit_op, entry_code_emit_void, entry_code_emit_inst,
            entry_code_data_section] >> rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (rewrite_tac[GSYM comp_ignore_bind_def] >>
      ho_match_mp_tac entry_code_fold_sequence >>
      simp[entry_code_return, entry_code_data_item]) >>
  simp[entry_code_create_bucket_blocks]
QED

Theorem entry_code_dense_data_sections[local]:
  !buckets bytes info. entry_preserves_code P
    (emit_dense_data_sections buckets bytes info)
Proof
  Induct >> simp[emit_dense_data_sections_def, entry_code_return] >>
  rpt gen_tac >> simp[comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_data_section] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >> reverse conj_tac
  >- (rewrite_tac[GSYM comp_ignore_bind_def] >>
      ho_match_mp_tac entry_code_fold_sequence >> simp[entry_code_return] >>
      gen_tac >> pairarg_tac >> simp[comp_ignore_bind_def] >>
      rpt (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_data_item] >> rpt gen_tac >> BETA_TAC) >>
      simp[entry_code_data_item]) >> simp[]
QED

Theorem entry_code_selector_dispatch_dense:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_selector_dispatch_dense sels n_buckets bytes buckets info
      labels fallback)
Proof
  simp[compile_selector_dispatch_dense_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_fresh_label,
            entry_code_emit_inst, entry_code_emit_void,
            entry_code_new_block, entry_code_data_section] >>
    rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (rewrite_tac[GSYM comp_ignore_bind_def] >>
      ho_match_mp_tac entry_code_fold_sequence >> simp[entry_code_return] >>
      gen_tac >> simp[comp_ignore_bind_def] >>
      rpt (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_data_item] >> rpt gen_tac >> BETA_TAC) >>
      simp[entry_code_data_item]) >>
  simp[entry_code_dense_data_sections]
QED
