(* Static user-arity interfaces of successful FMP lowering. *)
Theory fmpStageCoverBackFmpArity
Ancestors
  fmpLowerDefs callLayoutDefs venomInst list o1PassContract fmpStepLayout

Theorem fmp_lower_invoke_user_arity:
  fn.fn_fmp_signature = NONE /\
  fmp_lower_function_with_info infos ctx sp fn = SOME (fn',sp') /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label name::args ==>
  ?callee. lookup_function name ctx.ctx_functions = SOME callee /\
    LENGTH args = LENGTH (fn_user_param_insts callee)
Proof
  strip_tac >>
  `fmp_lower_input infos ctx fn` by
    (gvs[fmp_lower_function_with_info_def, AllCaseEqs()]) >>
  `IS_SOME (fmp_resolve_invoke infos ctx inst)` by
    (gvs[fmp_lower_input_def, fmp_lower_blocks_shape_def,
         fmp_lower_insts_shape_def, fn_insts_def, fn_insts_blocks_MEM,
         EVERY_MEM] >>
     `fmp_lower_inst_shape infos ctx inst` by metis_tac[] >>
     gvs[fmp_lower_inst_shape_def]) >>
  Cases_on `fmp_resolve_invoke infos ctx inst` >> gvs[] >>
  PairCases_on `x` >>
  drule fmp_resolve_invoke_some >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem split_fmp_entry_from_suffix_no_params[local]:
  split_fmp_entry_from k acc insts = SOME (FmpEntryLayout users pc tail) ==>
  no_param_insts tail
Proof
  map_every qid_spec_tac [`k`, `acc`] >> Induct_on `insts`
  >- simp[split_fmp_entry_from_def, no_param_insts_def] >>
  simp[Once split_fmp_entry_from_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem split_fmp_entry_user_insts[local]:
  split_fmp_entry fn = SOME (FmpEntryLayout users pc tail) ==>
  fn_user_param_insts fn = users
Proof
  strip_tac >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  drule split_fmp_entry_users >> strip_tac >>
  `no_param_insts tail` by
    (gvs[split_fmp_entry_def] >>
     drule split_fmp_entry_from_suffix_no_params >> simp[]) >>
  Cases_on `pc`
  >- (gvs[fn_user_param_insts_def, fn_entry_insts_def, entry_block_def,
          FILTER_APPEND_DISTRIB, every_user_param_queries,
          no_param_insts_def, FILTER_EQ_NIL, EVERY_MEM, is_param_opcode_iff]) >>
  drule fmpLowerPropsTheory.split_fmp_entry_retpc_opcode >> strip_tac >>
  gvs[fn_user_param_insts_def, fn_entry_insts_def, entry_block_def,
      FILTER_APPEND_DISTRIB, every_user_param_queries,
      no_param_insts_def, FILTER_EQ_NIL, EVERY_MEM, is_param_opcode_iff]
QED

Theorem fmp_root_user_param_count[local]:
  split_fmp_entry fn = SOME (FmpEntryLayout users pc tail) /\
  fmp_make_root_layout ctx fn info runner sp = SOME (FmpRootLayout n root pc' sp') /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_lower_blocks infos ctx runner sp' (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover sp'') /\
  fmp_install_root ctx fn (FmpRootLayout n root pc' sp'') blocks = SOME (out,sp3) ==>
  LENGTH (fn_user_param_insts fn) <=
  LENGTH (fn_user_param_insts (fn with fn_blocks := out))
Proof
  strip_tac >>
  drule split_fmp_entry_user_insts >> strip_tac >>
  drule split_fmp_entry_users >> strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >> gvs[] >>
  `entry.bb_instructions = fn_user_param_insts fn ++ OPTION_TO_LIST pc ++ tail'` by
    (Cases_on `pc` >> gvs[OPTION_TO_LIST_def]) >>
  drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  simp[fn_user_param_insts_def, fn_entry_insts_def, entry_block_def,
       FILTER_APPEND_DISTRIB, every_user_param_queries] >>
  Cases_on `fn_is_context_entry ctx fn` >> simp[FILTER_APPEND_DISTRIB, rich_listTheory.FILTER_FILTER]
QED

Theorem fmp_lower_user_param_count:
  fmp_lower_function_with_info infos ctx sp fn = SOME (fn',sp') ==>
  LENGTH (fn_user_param_insts fn) <= LENGTH (fn_user_param_insts fn')
Proof
  simp[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule fmp_checked_seal_some >> strip_tac >>
  gvs[fmp_seal_def, fn_user_param_insts_def, fn_entry_insts_def, entry_block_def] >>
  irule (SRULE [fn_user_param_insts_def, fn_entry_insts_def, entry_block_def]
    fmp_root_user_param_count) >>
  gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]
QED
