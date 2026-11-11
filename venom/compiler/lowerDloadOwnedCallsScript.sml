(* Unconditional call transitions for owned prefix coverage. *)
Theory lowerDloadOwnedCalls
Ancestors
  lowerDloadOwnedTransitionBoundary lowerDloadReturnInvokePush
  lowerDloadReturnInvokePop lowerDloadReturnReconstruction
  lowerDloadSafetyAmbient lowerDloadSafetyRelation
  venomExecSemantics venomInst lowerDloadSafetyRunInduction
Libs lowerDloadOwnedTransitionPackageLib lowerDloadReturnPackageLib

Theorem ld_owned_callee_entry:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\
  setup_callee calleeT argsT t = SOME ct /\
  enters_block calleeT ct tp /\ active_inst calleeT ti tp /\
  lookup_block tp.vs_current_bb calleeT.fn_blocks = SOME bb ==>
  ^ld_owned lo P C C' vs0 Sigma names calleeT ti tp
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >>
  drule_all ld_invoke_active_push >> strip_tac >>
  drule_at (Pos hd) ld_point_owned >>
  disch_then drule >> disch_then drule >>
  simp[Abbr `Goal`]
QED

Theorem ld_owned_invoke_next:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
  fn' = ld_image f /\ ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\ lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  inst.inst_opcode = INVOKE /\ step_inst fuel C' inst t = OK q /\
  active_inst fn' nexti (q with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^ld_owned lo P C C' vs0 Sigma names fn' nexti
    (q with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >>
  drule_all ld_invoke_success >> strip_tac >>
  drule_all ld_invoke_return_reconstruction >> strip_tac >>
  drule_all ld_invoke_pop_core >> disch_tac >>
  drule_at (Pos hd) ld_transfer_point_owned >>
  disch_then drule >> disch_then drule >> simp[Abbr `Goal`]
QED
