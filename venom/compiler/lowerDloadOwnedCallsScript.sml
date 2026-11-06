(* Unconditional call transitions for owned prefix coverage. *)
Theory lowerDloadOwnedCalls
Ancestors
  lowerDloadOwnedTransitionBoundary lowerDloadReturnInvokePush
  lowerDloadReturnInvokePop lowerDloadReturnReconstruction
  lowerDloadSafetyAmbient lowerDloadSafetyRelation
  venomExecSemantics venomInst
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
