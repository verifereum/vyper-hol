Theory fmpStageFmpStepsRetInvokeCode
Ancestors
  fmpStageControl fmpStageOpBase fmpStageRel fmpLowerDefs
  o1PassContract contextCodegenRel venomExecSemantics venomInst

Theorem fmp_return_root_excluded:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE /\
  (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) ==>
  !rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\ lbl = rl ==>
    rp <> SUC idx
Proof
  rpt strip_tac >> gvs[] >>
  `INVOKE <> RETPC_PARAM` by simp[] >>
  metis_tac[fmp_stage_root_crossing]
QED
