(* Checked mutation-base program, event topics and method-ID certificates. *)
Theory evalCompilerBytecodeExternalBaseProgram
Ancestors
  compileVyper concretizeMemLocDefs alist byte integer_word option
Libs
  proofAuditLib
  evalCompilerBytecodeLib evalCompilerEntryLib evalCompilerEntryFixtureLib
  vyperCheckContractFrontendLib vyperCheckContractLib jsonASTLib JSONDecode cv_transLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-entries"]
val () = cv_auto_trans vyperEventTheory.event_hash_def

Theorem base_E1_hash:
  vyperEvent$event_hash FEMPTY "E1" [BaseT (UintT 256)] =
    0x47e2689743f14e97f7dcfa5eec10ba1dff02f83b3d1d4b9c07b206cbbda66450
Proof
  CONV_TAC (LAND_CONV cv_transLib.cv_eval) >> EVAL_TAC
QED
Theorem base_E2_hash:
  vyperEvent$event_hash FEMPTY "E2" [BaseT (UintT 256)] =
    0xa48a6b249a5084126c3da369fbc9b16827ead8cb5cdc094b717d3f1dcd995e29
Proof
  CONV_TAC (LAND_CONV cv_transLib.cv_eval) >> EVAL_TAC
QED
val () = computeLib.upd_compset (computeLib.add_thms
  [base_E1_hash, base_E2_hash, build_event_info_def, build_compile_env_def])

Theorem base_f_selector:
  compute_selector FEMPTY "f" [BaseT (UintT 256)] = (0xb3de648b,"fn_f",F)
Proof
  simp_tac pure_ss [compute_selector_def, LET_THM] >>
  entry_stage "function_selector" >> EVAL_TAC
QED
val () = computeLib.upd_compset (computeLib.add_thms [base_f_selector])

Theorem base_burn_selector:
  compute_selector FEMPTY "burn" [BaseT (UintT 256)] = (0x42966c68,"fn_burn",F)
Proof
  simp_tac pure_ss [compute_selector_def, LET_THM] >>
  entry_stage "function_selector" >> EVAL_TAC
QED
val () = computeLib.upd_compset (computeLib.add_thms [base_burn_selector])

Theorem base_cps_selector:
  compute_selector FEMPTY "cps" [BaseT (BytesT (Fixed 16))] = (0x6daaba68,"fn_cps",F)
Proof
  simp_tac pure_ss [compute_selector_def, LET_THM] >>
  entry_stage "function_selector" >> EVAL_TAC
QED
val () = computeLib.upd_compset (computeLib.add_thms [base_cps_selector])

Theorem base_p_selector:
  compute_selector FEMPTY "p" [BaseT (UintT 256)] = (0xa9692047,"fn_p",F)
Proof
  simp_tac pure_ss [compute_selector_def, LET_THM] >>
  entry_stage "function_selector" >> EVAL_TAC
QED
val () = computeLib.upd_compset (computeLib.add_thms [base_p_selector])

Theorem base_k_selector:
  compute_selector FEMPTY "k" [] = (0xb4f40c61,"fn_k",F)
Proof
  simp_tac pure_ss [compute_selector_def, LET_THM] >>
  entry_stage "function_selector" >> EVAL_TAC
QED
val () = computeLib.upd_compset (computeLib.add_thms [base_k_selector])

Definition base_dom1_program_def:
  base_dom1_program = ^(checked_entry_fixture "base_dom1")
End


val () = proofAuditLib.check_theory "evalCompilerBytecodeExternalBaseProgram";
