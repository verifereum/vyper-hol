Theory e2eDeployStepProbe
Ancestors e2eDeployProbe vfmCompute vfmExecution
Libs finite_mapLib wordsLib cv_transLib
val () = computeLib.upd_compset add_finite_map_compset
Theorem probe_first_instruction:
  FLOOKUP (parse_code 0 FEMPTY probe_deploy_bytes) 0 = SOME JumpDest
Proof
  rewrite_tac[probe_deploy_bytes_def] >>
  CONV_TAC cv_eval
QED

Theorem probe_code_length:
  LENGTH probe_deploy_bytes = 57
Proof
  EVAL_TAC
QED

Theorem probe_jumpdest_step:
  step (probe_creation_state s) =
    (INL (), (probe_creation_state s) with contexts updated_by
      (\cs. [(FST (HD cs) with <|pc := 1; gasUsed := 1|>, SND (HD cs))]))
Proof
  simp[Once vfmExecutionTheory.step_def, probe_creation_state_def,
       vfmExecutionTheory.handle_def, vfmExecutionTheory.bind_def,
       vfmExecutionTheory.get_current_context_def, vfmExecutionTheory.return_def,
       probe_first_instruction, probe_code_length,
       vfmExecutionTheory.step_inst_def, vfmExecutionTheory.consume_gas_def,
       vfmExecutionTheory.assert_def, vfmExecutionTheory.set_current_context_def,
       vfmExecutionTheory.inc_pc_or_jump_def] >>
  simp[vfmExecutionTheory.ignore_bind_def, vfmExecutionTheory.bind_def,
       vfmExecutionTheory.get_current_context_def, vfmExecutionTheory.return_def,
       vfmExecutionTheory.assert_def, vfmExecutionTheory.set_current_context_def,
       vfmExecutionTheory.is_call_def, vfmOperationTheory.opcode_def]
QED

(* These are execution-interface probes, not a deployment proof. *)
val _ = List.app (fn thy => List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("non-clean deployment probe: " ^ name)
  end) (DB.thms thy)) ["e2eDeployProbe", "e2eDeployStepProbe"];
