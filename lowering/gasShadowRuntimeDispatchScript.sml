(* Dispatch is independent of shadowed function bodies. *)
Theory gasShadowRuntimeDispatch
Ancestors
  gasShadowModuleArgs gasShadow gasShadowRuntimeOps gasShadowCompileContext gasShadowState moduleLowering
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

Theorem gas_shadow_compiles_compile_group_entries:
  !entries mid common kwvars off.
  gas_shadow_compiles (compile_group_entries mid entries common kwvars off)
    (compile_group_entries mid entries
      (common with ec_body := MAP gas_shadow_stmt common.ec_body)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) kwvars) off)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_group_entries_def, gas_shadow_compiles_return] >>
  PairCases_on `h` >>
  simp[compile_group_entries_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op_same,
               gas_shadow_compiles_fresh_label, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block, gas_shadow_compiles_compile_entry_checks,
               gas_shadow_compiles_entry_point_kwargs] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compile_external_groups:
  !groups mid s t. gas_shadow_state s t ==>
  FST (compile_external_groups mid
    (MAP (\group. case group of
      ExternalSingle selector package => ExternalSingle selector (gas_shadow_external_package package)
    | ExternalDefaults common entries specs off => ExternalDefaults
        (common with ec_body := MAP gas_shadow_stmt common.ec_body) entries
        (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) specs) off) groups) t) =
  MAP (\job. case job of
      ExternalLegacyJob package => ExternalLegacyJob (gas_shadow_external_package package)
    | ExternalCommonJob common kwvars => ExternalCommonJob
        (common with ec_body := MAP gas_shadow_stmt common.ec_body)
        (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) kwvars))
    (FST (compile_external_groups mid groups s)) /\
  gas_shadow_state (SND (compile_external_groups mid groups s))
    (SND (compile_external_groups mid
    (MAP (\group. case group of
      ExternalSingle selector package => ExternalSingle selector (gas_shadow_external_package package)
    | ExternalDefaults common entries specs off => ExternalDefaults
        (common with ec_body := MAP gas_shadow_stmt common.ec_body) entries
        (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) specs) off) groups) t))
Proof
  Induct >> rpt gen_tac
  >- simp[compile_external_groups_def, comp_return_def] >>
  Cases_on `h`
  >- (rename1 `ExternalSingle selector package` >>
      PairCases_on `selector` >> strip_tac >>
      qspecl_then [`[(selector0,selector1)]`, `mid`] mp_tac
        gas_shadow_compiles_compile_selector_checks >>
      rewrite_tac[gas_shadow_compiles_def] >> disch_then drule_all >> strip_tac >>
      first_x_assum (qspecl_then [`mid`,
        `SND (compile_selector_checks mid [(selector0,selector1)] s)`,
        `SND (compile_selector_checks mid [(selector0,selector1)] t)`] mp_tac) >>
      simp[] >> strip_tac >>
      gvs[compile_external_groups_def, comp_ignore_bind_def, comp_bind_def,
          comp_return_def, pairTheory.UNCURRY]) >>
  strip_tac >> rename1 `ExternalDefaults common entries specs off` >>
  qspecl_then [`specs`, `common.ec_env`] mp_tac
    gas_shadow_compile_create_kwarg_allocas >>
  disch_then drule_all >> strip_tac >>
  Cases_on `compile_create_kwarg_allocas common.ec_env specs s` >>
  Cases_on `compile_create_kwarg_allocas common.ec_env
    (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) specs) t` >> gvs[] >>
  `gas_shadow_compiles (compile_group_entries mid entries common q off)
    (compile_group_entries mid entries
      (common with ec_body := MAP gas_shadow_stmt common.ec_body)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) q) off)` by
    simp[gas_shadow_compiles_compile_group_entries] >>
  qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
  rewrite_tac[gas_shadow_compiles_def] >> disch_then drule_all >> strip_tac >>
  first_x_assum (qspecl_then [`mid`,
    `SND (compile_group_entries mid entries common q off r)`,
    `SND (compile_group_entries mid entries
      (common with ec_body := MAP gas_shadow_stmt common.ec_body)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) q) off r')`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[compile_external_groups_def, comp_ignore_bind_def, comp_bind_def,
      comp_return_def, pairTheory.UNCURRY]
QED

Theorem gas_shadow_compile_group_dispatch_linear:
  !groups fb s t. gas_shadow_state s t ==>
  FST (compile_group_dispatch_linear
    (MAP (\group. case group of
      ExternalSingle selector package => ExternalSingle selector (gas_shadow_external_package package)
    | ExternalDefaults common entries specs off => ExternalDefaults
        (common with ec_body := MAP gas_shadow_stmt common.ec_body) entries
        (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) specs) off) groups) fb t) =
  MAP (\job. case job of
      ExternalLegacyJob package => ExternalLegacyJob (gas_shadow_external_package package)
    | ExternalCommonJob common kwvars => ExternalCommonJob
        (common with ec_body := MAP gas_shadow_stmt common.ec_body)
        (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) kwvars))
    (FST (compile_group_dispatch_linear groups fb s)) /\
  gas_shadow_state (SND (compile_group_dispatch_linear groups fb s))
    (SND (compile_group_dispatch_linear
    (MAP (\group. case group of
      ExternalSingle selector package => ExternalSingle selector (gas_shadow_external_package package)
    | ExternalDefaults common entries specs off => ExternalDefaults
        (common with ec_body := MAP gas_shadow_stmt common.ec_body) entries
        (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) specs) off) groups) fb t))
Proof
  ntac 2 gen_tac >>
  rewrite_tac[GSYM gas_shadow_compiles_mapped_result_iff,
    compile_group_dispatch_linear_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op_same, gas_shadow_compiles_fresh_label,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block] >>
       gen_tac >> BETA_TAC >> rewrite_tac[comp_bind_assoc]) >>
  irule gas_shadow_compiles_bind_mapped >>
  qexists_tac `MAP (\job. case job of
    ExternalLegacyJob package => ExternalLegacyJob (gas_shadow_external_package package)
  | ExternalCommonJob common kwvars => ExternalCommonJob
      (common with ec_body := MAP gas_shadow_stmt common.ec_body)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) kwvars))` >>
  reverse conj_tac >- simp[gas_shadow_compile_external_groups] >>
  gen_tac >> BETA_TAC >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_emit_inst] >>
  simp[gas_shadow_compiles_def, comp_bind_def, comp_return_def]
QED
