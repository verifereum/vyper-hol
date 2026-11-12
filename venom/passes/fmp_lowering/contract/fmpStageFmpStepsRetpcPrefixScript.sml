Theory fmpStageFmpStepsRetpcPrefix
Ancestors
  fmpStageRel fmpStepLayout fmpLowerDefs fmpLowerProps
  list rich_list finite_map callLayoutDefs irSupply venomInst

Theorem fmp_retpc_install_prefix[local]:
  split_fmp_entry fn = SOME (FmpEntryLayout users (SOME inst) suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 =
    SOME (FmpRootLayout n root pc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root pc s2) blocks = SOME (out,s3) ==>
  ?entry rest tail.
    out = entry::rest /\
    entry.bb_instructions =
      (if fn_is_context_entry ctx fn then
         users ++ OPTION_TO_LIST pc ++ OPTION_TO_LIST root ++ tail
       else users ++ OPTION_TO_LIST root ++ OPTION_TO_LIST pc ++ tail)
Proof
  strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >> gvs[] >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST (SOME inst) ++ tail` by
    simp[OPTION_TO_LIST_def] >>
  `(pc = NONE <=> (SOME inst : instruction option) = NONE)` by simp[] >>
  drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fmp_retpc_lowered_no_root_prefix:
  fmp_stage_lowered infos ctx runner fn fn' /\
  split_fmp_entry fn = SOME (FmpEntryLayout users (SOME inst) suffix) /\
  fn.fn_fmp_signature = NONE /\
  FLOOKUP infos fn.fn_name = SOME info /\ ~info.fi_needs_fmp ==>
  ?entry rest tail. fn'.fn_blocks = entry::rest /\
    entry.bb_instructions = users ++ [inst] ++ tail
Proof
  simp[fmp_stage_lowered_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def]
  >- (drule split_fmp_entry_reconstruct >> simp[] >> metis_tac[]) >>
  Cases_on `root_layout` >> gvs[] >>
  drule_all fmp_retpc_install_prefix >>
  gvs[fmp_make_root_layout_def, OPTION_TO_LIST_def]
QED

Theorem fmp_retpc_lowered_root_prefix:
  fmp_stage_lowered infos ctx runner fn fn' /\
  split_fmp_entry fn = SOME (FmpEntryLayout users (SOME inst) suffix) /\
  fn.fn_fmp_signature = NONE /\ ~fn_is_context_entry ctx fn /\
  FLOOKUP infos fn.fn_name = SOME info /\ info.fi_needs_fmp ==>
  ?entry rest tail id. fn'.fn_blocks = entry::rest /\
    entry.bb_instructions = users ++
      [mk_inst id FMP_PARAM [Lit (n2w (LENGTH users))] [runner];
       set_param_index (SUC (LENGTH users)) inst] ++ tail
Proof
  simp[fmp_stage_lowered_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def] >>
  Cases_on `root_layout` >> gvs[] >>
  drule_all fmp_retpc_install_prefix >>
  gvs[fmp_make_root_layout_def, AllCaseEqs(), OPTION_TO_LIST_def] >>
  metis_tac[]
QED

Theorem fmp_retpc_lowered_entry_label:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn'.fn_blocks = entry::rest ==>
  fn_entry_label fn = SOME entry.bb_label
Proof
  simp[fmp_stage_lowered_def] >> strip_tac >>
  `fmp_lower_function ctx sp fn = SOME (fn',sp')` by
    simp[fmp_lower_function_def] >>
  drule fmp_lower_function_preserves_entry_label >>
  simp[fn_entry_label_def, entry_block_def]
QED

Theorem fmp_retpc_root_location:
  split_fmp_entry fn = SOME (FmpEntryLayout users (SOME inst) suffix) /\
  fn.fn_blocks = entry::rest /\ fn.fn_fmp_signature = NONE /\
  ~fn_is_context_entry ctx fn /\
  FLOOKUP infos fn.fn_name = SOME info ==>
  fmp_stage_root infos ctx fn =
    if info.fi_needs_fmp then SOME (entry.bb_label,SUC (LENGTH users)) else NONE
Proof
  strip_tac >> simp[fmp_stage_root_def] >>
  Cases_on `info.fi_needs_fmp` >> simp[]
QED

Theorem fmp_retpc_prefix_plan_absent:
  split_fmp_entry fn = SOME (FmpEntryLayout users (SOME inst) suffix) /\
  fn.fn_blocks = entry::rest /\ n <= LENGTH users ==>
  ~((entry.bb_label,n) IN FDOM (fmp_stage_plan infos ctx fn))
Proof
  strip_tac >> Cases_on `analyze_fmp_reclaims infos ctx fn`
  >- simp[fmp_stage_plan_def] >>
  rename1 `analyze_fmp_reclaims infos ctx fn = SOME plan` >>
  simp[fmp_stage_plan_def] >> strip_tac >>
  drule split_fmp_entry_reconstruct >> simp[] >> strip_tac >> gvs[] >>
  `lookup_block entry.bb_label fn.fn_blocks = SOME entry` by
    simp[lookup_block_def, FIND_thm] >>
  `EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM])
     (users ++ [inst])` by
    (drule split_fmp_entry_parameter_prefix >> simp[]) >>
  `MEM ((entry.bb_label,n),plan ' (entry.bb_label,n))
     (fmp_plan_to_alist fn plan)` by
    simp[MEM_fmp_plan_to_alist, FLOOKUP_DEF] >>
  drule (Q.INST [`prefix` |-> `users ++ [inst]`]
    analyze_fmp_reclaims_parameter_prefix_absent) >>
  simp[] >>
  qexistsl [`users`, `suffix`, `entry.bb_label`, `inst`, `entry`, `n`,
    `plan ' (entry.bb_label,n)`] >> gvs[EVERY_APPEND]
QED
