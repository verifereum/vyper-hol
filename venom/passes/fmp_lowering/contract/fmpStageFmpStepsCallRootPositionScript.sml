Theory fmpStageFmpStepsCallRootPosition
Ancestors
  fmpStageRel fmpLowerDefs fmpStepLayout venomInst callLayoutDefs
  list rich_list option

Theorem call_root_retpc[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  split_fmp_entry fn = SOME (FmpEntryLayout users retpc rest) /\
  ~fn_is_context_entry ctx fn ==> retpc <> NONE
Proof
  simp[fmp_stage_lowered_def, fmp_stage_root_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `FLOOKUP infos fn.fn_name` >> gvs[] >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _` mp_tac >>
  simp[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[fmp_make_root_layout_def, AllCaseEqs()]
QED

Theorem call_prefix_no_invoke[local]:
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]) prefix /\
  idx < LENGTH (prefix ++ rest) /\
  (EL idx (prefix ++ rest)).inst_opcode = INVOKE ==>
  LENGTH prefix <= idx
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `idx < LENGTH prefix` by decide_tac >>
  fs[EVERY_EL, EL_APPEND1] >>
  first_x_assum (qspec_then `idx` mp_tac) >> simp[]
QED

Theorem fmp_call_invoke_past_root:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  lookup_block rl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE ==> rp <= idx
Proof
  rpt strip_tac >>
  qpat_assum `fmp_stage_root _ _ _ = _`
    (strip_assume_tac o SRULE [fmp_stage_root_def, AllCaseEqs()]) >>
  gvs[] >> drule split_fmp_entry_reconstruct >> strip_tac >>
  `LENGTH (users ++ OPTION_TO_LIST retpc) <= idx` by
    (irule call_prefix_no_invoke >> reverse conj_tac
     >- (drule split_fmp_entry_parameter_prefix >>
         Cases_on `retpc` >> simp[OPTION_TO_LIST_def]) >>
     qexists `rest` >> Cases_on `retpc` >>
     gvs[lookup_block_def, FIND_thm, OPTION_TO_LIST_def]) >>
  Cases_on `fn_is_context_entry ctx fn` >> gvs[] >>
  drule_all call_root_retpc >> strip_tac >>
  Cases_on `retpc` >> gvs[OPTION_TO_LIST_def]
QED
