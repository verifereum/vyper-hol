(* TOP-LEVEL: enc_mid_const_ready. All code generation preconditions. *)
Theory foldedValueParityAbiReady
Ancestors
  foldedValueParityAbiInput foldedValueParityAbiCompute
  foldedValueParityCompute compileVyper codegenReadyCompute
Libs foldedValueParityLib foldedValueParityAbiDftLib numLib

Theorem enc_mid_const_ready:
  codegen_ready enc_mid_const_context
Proof
  CONV_TAC (RAND_CONV (REWR_CONV enc_mid_const_context_def)) >>
  READY_OPEN_TAC >>
  eval_call ``canonical_param_prefix`` >>
  eval_call ``wf_function`` >>
  eval_call ``fn_inst_wf`` >>
  eval_call ``ssa_form`` >>
  DOM_SUBGOAL_TAC
  >- (CONV_TAC (restricted_eval [``def_dominates_uses_exec``]) >>
      CONV_TAC (REWR_CONV codegenReadyComputeTheory.def_dominates_uses_exec_def) >>
      eval_call ``cfg_analyze`` >>
      CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
      eval_call ``dom_analyze`` >>
      CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
      EVERY_GOALS_TAC >>
      FIRST [ACCEPT_TAC TRUTH,
        CONV_TAC (RAND_CONV finite_eval) >>
        ABBREV_EVERY_TAC >> EVERY_GOALS_TAC >>
        FIRST [markerLib.UNABBREV_TAC "available_check" >>
          CONV_TAC head_beta_conv >> DOM_BRANCH_TAC >> DOM_EVAL_TAC]]) >>
  eval_call ``single_use_form`` >>
  eval_call ``cfg_is_normalized`` >>
  PARITY_NORMALIZE_TAC
QED

val () = audit "foldedValueParityAbiReady";
val () = if null (hyp enc_mid_const_ready) then ()
  else raise Fail "undischarged readiness context";
