Theory concretizePtrMetadataTransport
Ancestors
  o1PassContract venomPassDispatcher venomPassSchedule
  fmpLowerDefs makeSsaCurrentDefs simplifyCfgDefs singleUseExpansionDefs
  cfgNormDefs dftDefs venomInst list

Theorem ptr_make_ssa_mems[local]:
  (FST (make_ssa_current_fn s fn)).fn_mems_used = fn.fn_mems_used
Proof
  simp[make_ssa_current_fn_def] >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem ptr_sue_mems[local]:
  (FST (sue_expand_function_supply s fn)).fn_mems_used = fn.fn_mems_used
Proof
  simp[sue_expand_function_supply_def] >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >> simp[]
QED

Theorem ptr_dft_mems[local]:
  (dft_fn fn).fn_mems_used = fn.fn_mems_used
Proof
  simp[dft_fn_def] >> pairarg_tac >> simp[]
QED

Theorem ptr_fmp_mems[local]:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  fn'.fn_mems_used = fn.fn_mems_used
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       fmp_checked_seal_def, fmp_seal_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ptr_insert_split_mems[local]:
  !s fn pred bb. (FST (insert_split_supply s fn pred bb)).fn_mems_used = fn.fn_mems_used
Proof
  rpt gen_tac >> simp[insert_split_supply_def] >>
  Cases_on `build_split_block_supply s pred bb` >>
  rename1 `_ = (first,rest)` >> PairCases_on `rest` >> simp[]
QED

Theorem ptr_find_split_mems[local]:
  !bbs fn s. (FST (find_and_split_supply fn s bbs)).fn_mems_used = fn.fn_mems_used
Proof
  Induct >> simp[find_and_split_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >- simp[] >>
  Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)` >> simp[] >>
  Cases_on `insert_split_supply s fn x h` >>
  qspecl_then [`s`,`fn`,`x`,`h`] mp_tac ptr_insert_split_mems >> simp[]
QED

Theorem ptr_cfg_iter_mems[local]:
  !n s fn. (FST (cfg_norm_iter_supply n s fn)).fn_mems_used = fn.fn_mems_used
Proof
  Induct >> simp[cfg_norm_iter_supply_def] >> rpt gen_tac >>
  Cases_on `cfg_norm_round_supply s fn` >>
  rename1 `_ = (first,rest)` >> PairCases_on `rest` >> simp[] >>
  qspec_then `fn.fn_blocks` (qspecl_then [`fn`,`s`] mp_tac) ptr_find_split_mems >>
  simp[GSYM cfg_norm_round_supply_def] >> strip_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem ptr_merge_jump_mems[local]:
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  fn'.fn_mems_used = fn.fn_mems_used
Proof
  simp[do_merge_jump_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem ptr_bypass_mems[local]:
  !succs fn lm bb fn' lm' changed.
    try_bypass fn lm bb succs = (fn',lm',changed) ==>
    fn'.fn_mems_used = fn.fn_mems_used
Proof
  Induct >> simp[try_bypass_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[ptr_merge_jump_mems]
QED

Theorem ptr_collapse_mems[local]:
  (!fn lm vis lbl.
     (FST (collapse_dfs fn lm vis lbl)).fn_mems_used = fn.fn_mems_used) /\
  (!fn lm vis succs.
     (FST (collapse_dfs_succs fn lm vis succs)).fn_mems_used = fn.fn_mems_used)
Proof
  ho_match_mp_tac collapse_dfs_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[Once collapse_dfs_def] >>
      Cases_on `lookup_block lbl fn.fn_blocks` >> simp[] >>
      rename1 `_ = SOME bb` >>
      Cases_on `bb_succs bb` >> simp[]
      >- (gvs[try_bypass_def] >> Cases_on `MEM lbl vis` >> simp[]) >>
      rename1 `_ = next::rest` >> Cases_on `rest` >> simp[]
      >- (Cases_on `lookup_block next fn.fn_blocks` >> simp[] >>
          rename1 `_ = SOME next_bb` >>
          Cases_on `can_merge_blocks fn bb next_bb` >> simp[] >>
          Cases_on `MEM lbl vis` >> simp[] >> metis_tac[]) >>
      pairarg_tac >> simp[] >>
      `func'.fn_mems_used = fn.fn_mems_used` by
        metis_tac[ptr_bypass_mems] >>
      Cases_on `bypassed` >> simp[] >>
      Cases_on `MEM lbl vis` >> simp[] >> metis_tac[]) >>
  conj_tac >- simp[Once collapse_dfs_def] >>
  rpt gen_tac >> strip_tac >> simp[Once collapse_dfs_def] >>
  pairarg_tac >> gvs[]
QED

Theorem ptr_cfg_simple_mems[local]:
  (remove_unreachable_blocks fn).fn_mems_used = fn.fn_mems_used /\
  (fix_all_phis fn).fn_mems_used = fn.fn_mems_used /\
  (subst_block_labels_fn lm fn).fn_mems_used = fn.fn_mems_used
Proof
  simp[remove_unreachable_blocks_def, fix_all_phis_def,
       cfgTransformTheory.subst_block_labels_fn_def] >>
  Cases_on `fn_entry_label fn` >> simp[]
QED

Theorem ptr_cfg_round_mems[local]:
  !fn. (FST (simplify_cfg_round_with_labels fn)).fn_mems_used = fn.fn_mems_used
Proof
  gen_tac >> simp[simplify_cfg_round_with_labels_def] >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  pairarg_tac >> simp[ptr_cfg_simple_mems] >>
  qspecl_then [`fix_all_phis (remove_unreachable_blocks fn)`, `[]`, `[]`, `x`]
    mp_tac (cj 1 ptr_collapse_mems) >>
  simp[ptr_cfg_simple_mems] >> strip_tac >>
  IF_CASES_TAC >> simp[ptr_cfg_simple_mems]
QED

Theorem ptr_cfg_simplify_iter_mems[local]:
  !n fn. (FST (simplify_cfg_iter_with_labels n fn)).fn_mems_used = fn.fn_mems_used
Proof
  Induct >> simp[simplify_cfg_iter_with_labels_def] >> gen_tac >>
  pairarg_tac >> simp[] >>
  qspec_then `fn` mp_tac ptr_cfg_round_mems >> simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[] >> pairarg_tac >>
  first_x_assum (qspec_then `func'` mp_tac) >> gvs[]
QED

Theorem ptr_suffix_step_mems[local]:
  MEM pass (DROP 3 o1_fn_passes) /\
  fn_pass_step rpolicy pass observed s fn out ==>
  out.fpo_function.fn_mems_used = fn.fn_mems_used
Proof
  simp[o1_fn_passes_def] >> strip_tac >>
  gvs[fn_pass_step_def] >>
  gvs[execute_configured_fn_pass_fmp,
      execute_configured_fn_pass_make_ssa,
      execute_configured_fn_pass_simplify_cfg,
      execute_configured_fn_pass_sue,
      execute_configured_fn_pass_dft,
      execute_configured_fn_pass_cfg_normalization, AllCaseEqs()] >>
  metis_tac[ptr_fmp_mems, ptr_make_ssa_mems, ptr_sue_mems,
            ptr_dft_mems, ptr_cfg_iter_mems, ptr_cfg_simplify_iter_mems,
            cfg_norm_function_supply_def, simplify_cfg_fn_with_labels_def,
            pairTheory.FST]
QED

Theorem ptr_suffix_steps_mems[local]:
  !passes fn fn'. EVERY (\pass. MEM pass (DROP 3 o1_fn_passes)) passes /\
    fn_steps rpolicy passes fn fn' ==>
    fn'.fn_mems_used = fn.fn_mems_used
Proof
  Induct >> simp[fn_steps_def] >> rpt strip_tac >>
  drule_all ptr_suffix_step_mems >>
  first_x_assum drule_all >> simp[]
QED

Theorem ptr_o1_suffix_mems:
  fn_steps rpolicy (DROP 3 o1_fn_passes) fn fn' ==>
  fn'.fn_mems_used = fn.fn_mems_used
Proof
  strip_tac >> irule ptr_suffix_steps_mems >>
  qexists `DROP 3 o1_fn_passes` >> simp[EVERY_MEM] >>
  goal_assum drule
QED

Theorem ptr_o1_walk_callee_mems:
  o1_walk_view rpolicy 2 C' fn observed /\
  MEM name (fn_invoke_targets fn) /\
  lookup_function name C'.ctx_functions = SOME g' ==>
  ?g. lookup_function name observed.cu_context.ctx_functions = SOME g /\
      g.fn_mems_used = g'.fn_mems_used
Proof
  simp[o1_walk_view_def, walk_view_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule ptr_o1_suffix_mems >> strip_tac >>
  goal_assum drule >> simp[]
QED
