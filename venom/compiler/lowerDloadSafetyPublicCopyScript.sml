Theory lowerDloadSafetyPublicCopy
Ancestors
  lowerDloadPublicCopyPointEffect
  lowerDloadOracleCallAssembly lowerDloadExternalBoundary
  lowerDloadSafetyWriteAssembly lowerDloadSafetyReadCoverage
  lowerDloadSafetyAccountReadEffects lowerDloadSafetyAllocBounds
  lowerDloadSafetyAmbient lowerDloadSafetyUpdates lowerDloadSafetyValues
  lowerDloadSafetyKernel lowerDloadSafetyRelation ptrDiscipline
  lowerDloadSafetyAssemblyPremises contextCodegenRel codegenRel memLocDefs pointerConfinedDefs venomWf venomInst venomExecSemantics venomState
  finite_map pred_set list words arithmetic

Theorem ld_sync_public_copy_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  ~in_revert_forward fn s /\ t.vs_alloca_next < dimword(:256) /\
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H)
      inst ss = ld_erase A o_f H' /\
    ld_dyn_agree (dyn_floor C vs0) (step_taint inst s ss tn).t_mem
      ss.vs_memory ts.vs_memory /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\ ts.vs_inst_idx = t.vs_inst_idx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ld_sync_taint_ok >> strip_tac >>
  drule_all ld_sync_access_ok >> strip_tac >>
  drule ld_sync_slots >> strip_tac >>
  drule ld_sync_maps >> strip_tac >>
  `EVERY (ld_maps A) (f::fs)` by simp[] >>
  drule_all ld_sync_dyn_floor >> strip_tac >>
  `f.lf_tgt = t` by (drule ld_sync_active >> simp[]) >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_alloc_target_no_wrap >> simp[] >> metis_tac[]) >>
  drule_all ld_sync_public_copy_effect_at >> disch_then ACCEPT_TAC
QED
