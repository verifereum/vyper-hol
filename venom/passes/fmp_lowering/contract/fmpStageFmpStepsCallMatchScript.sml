Theory fmpStageFmpStepsCallMatch
Ancestors
  fmpStageFmpStepsCallOrdinal fmpStageFmpStepsCallAbi
  fmpStageOpBase fmpStageControl fmpStepLayout fmpLowerDefs
  fmpStageRel venomExecProofs contextCodegenRel o1PassContract
  list rich_list finite_map

Theorem call_invoke_past_root[local]:
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  lookup_block rl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE ==>
  rp <= idx
Proof
  simp[fmp_stage_root_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  drule split_fmp_entry_parameter_prefix >> strip_tac >>
  gvs[lookup_block_def, FIND_thm] >>
  `LENGTH (users ++ OPTION_TO_LIST retpc) <= idx` by
    (spose_not_then assume_tac >>
     `idx < LENGTH (users ++ OPTION_TO_LIST retpc)` by decide_tac >>
     fs[EVERY_EL, EL_APPEND1, OPTION_TO_LIST_def] >>
     first_x_assum (qspec_then `idx` mp_tac) >> simp[]) >>
  Cases_on `fn_is_context_entry ctx fn` >> simp[] >>
  Cases_on `retpc` >> gvs[OPTION_TO_LIST_def, split_fmp_entry_def, AllCaseEqs()]
QED
