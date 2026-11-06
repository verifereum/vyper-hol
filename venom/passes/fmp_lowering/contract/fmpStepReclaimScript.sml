Theory fmpStepReclaim
Ancestors
  fmpStepAnalysis fmpStepStack fmpReclaimProps fmpReclaimDefs fmpAliasDefs
  list pair

Theorem analyze_fmp_reclaims_output:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  FLOOKUP plan point = SOME target ==>
  ?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = DALLOCA /\
         MEM target inst.inst_outputs
Proof
  strip_tac >> drule_all analyze_fmp_reclaims_target_checked >> strip_tac >>
  drule_all fmp_reclaim_states_stack >> strip_tac >>
  `fmp_dalloca_output fn target` by
    (drule_at (Pos last) fmp_reclaim_target_stack >>
     simp[fmp_stack_valid_def] >>
     disch_then (qspec_then `fmp_dalloca_output fn` mp_tac) >> simp[]) >>
  fs[fmp_dalloca_output_def] >> metis_tac[]
QED

Theorem fmp_reclaim_step_point:
  FST (fmp_reclaim_step infos fn live env p inst s) = SOME v ==>
  fmp_is_reclaim_point infos inst
Proof
  Cases_on `s` >- simp[fmp_reclaim_step_def] >>
  spose_not_then assume_tac >>
  gvs[fmp_reclaim_step_def, fmp_pop_at_def, fmp_pop_target_def]
QED

Theorem analyze_fmp_reclaims_position:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  FLOOKUP plan point = SOME target ==>
  ?bb. lookup_block (FST point) fn.fn_blocks = SOME bb /\
       SND point < LENGTH bb.bb_instructions /\
       fmp_is_reclaim_point infos (EL (SND point) bb.bb_instructions)
Proof
  strip_tac >> drule_all analyze_fmp_reclaims_target_checked >> strip_tac >>
  metis_tac[fmp_reclaim_step_point]
QED

Theorem fmp_reclaim_point_opcodes:
  fmp_is_reclaim_point infos inst ==>
  MEM inst.inst_opcode [DALLOCA; JMP; JNZ; DJMP; INVOKE]
Proof
  simp[fmp_is_reclaim_point_def, fmp_callee_info_def,
       fmpAnalysisDefsTheory.fmp_invoke_target_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[]
QED

Theorem fmp_reclaim_point_not_prefix:
  fmp_is_reclaim_point infos inst ==>
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> PARAM /\
  inst.inst_opcode <> FMP_PARAM /\ inst.inst_opcode <> RETPC_PARAM
Proof
  strip_tac >> drule fmp_reclaim_point_opcodes >> simp[] >>
  strip_tac >> gvs[]
QED
