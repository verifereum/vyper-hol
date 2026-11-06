Theory ctorDeployLoweringEntryWitness
Ancestors
  ctorDeployLoweringEntrySource ctorDeployLoweringDefs vyperInterpreter
  vyperContext vyperState asmOracleRegression asmSem vfmContext vfmState e2eDefs e2eDeployDefs
  vfmExecution vfmExecutionProp vfmConstants vfmOperation venomExecSemantics
  stackPlanTypes venomCompilerTypes stackPlanGen asmIR
  vyperTypeEntryReadiness vyperTypeInitialState vyperTypeContractSoundness
Libs finite_mapLib wordsLib

Theorem deploy_ctor_noninit_source_start:
  ?am_c es0.
    deploy_ctor_start
      [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
      initial_machine_state
      (empty_call_txn with <| function_name := "__init__"; is_creation := T;
                              block_number := 1; block_hashes := [0w] |>)
      (Payable,F,[],am_c,es0)
Proof
  simp[deploy_ctor_start_def, empty_call_txn_def,
       deploy_ctor_noninit_selection_probe] >>
  EVAL_TAC >> simp[find_var_decl_by_name_def, COND_RAND, COND_RATOR]
QED

Theorem deploy_ctor_noninit_typing:
  deploy_typing_ok
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
    initial_machine_state
    (empty_call_txn with <| function_name := "__init__"; is_creation := T;
                              block_number := 1; block_hashes := [0w] |>)
Proof
  simp[e2eDeployDefsTheory.deploy_typing_ok_def,
       initial_machine_state_def, empty_call_txn_def,
       machine_well_typed_def, call_tx_well_typed_def,
       checked_deployment_constants_ready_def] >>
  EVAL_TAC >> simp[find_var_decl_by_name_def, COND_RAND, COND_RATOR]
QED

Theorem deploy_ctor_noninit_storage:
  deploy_storage_ok
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
    initial_machine_state
    (empty_call_txn with <| function_name := "__init__"; is_creation := T;
                              block_number := 1; block_hashes := [0w] |>)
Proof
  EVAL_TAC >> simp[find_var_decl_by_name_def, COND_RAND, COND_RATOR]
QED

Theorem deploy_ctor_noninit_source_ready:
  deploy_source_ok
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
    initial_machine_state
    (empty_call_txn with <| function_name := "__init__"; is_creation := T;
                              block_number := 1; block_hashes := [0w] |>)
Proof
  simp[ctorDeployDefsTheory.deploy_source_ok_def,
       deploy_ctor_noninit_supported_probe, deploy_ctor_noninit_typing,
       deploy_ctor_noninit_storage] >> EVAL_TAC >> rpt strip_tac >> gvs[supportedStmtTraverseTheory.supported_stmt_expr_exists_def]
QED

Theorem deploy_ctor_zero_gas_jumpdest_terminal:
  es.contexts = [(c,r)] /\
  FLOOKUP c.msgParams.parsed c.pc = SOME JumpDest /\
  c.msgParams.gasLimit = 0 ==>
  ISR (FST (step es))
Proof
  rpt strip_tac >>
  simp[vfmExecutionTheory.step_def, vfmExecutionTheory.get_current_context_def,
       vfmExecutionTheory.bind_def, vfmExecutionTheory.ignore_bind_def,
       vfmExecutionTheory.handle_def, vfmExecutionTheory.return_def,
       vfmExecutionTheory.step_inst_def, vfmExecutionTheory.consume_gas_def,
       vfmExecutionTheory.assert_def, vfmExecutionTheory.fail_def,
       vfmExecutionTheory.handle_step_def,
       vfmExecutionTheory.handle_create_def, vfmExecutionTheory.handle_exception_def,
       vfmExecutionTheory.get_return_data_def, vfmExecutionTheory.get_output_to_def,
       vfmExecutionTheory.reraise_def, vfmExecutionTheory.get_gas_left_def,
       vfmExecutionTheory.get_num_contexts_def, vfmExecutionTheory.set_return_data_def,
       vfmExecutionTheory.set_current_context_def] >>
  Cases_on `c.msgParams.outputTo` >>
  simp[vfmExecutionTheory.reraise_def, vfmExecutionTheory.bind_def,
       vfmExecutionTheory.ignore_bind_def, vfmExecutionTheory.get_current_context_def,
       vfmExecutionTheory.assert_def, vfmExecutionTheory.fail_def,
       vfmExecutionTheory.return_def, vfmExecutionTheory.set_current_context_def] >>
  Cases_on `c.gasUsed = 0` >> simp[vfmExecutionTheory.reraise_def]
QED

Theorem deploy_ctor_empty_stack_terminal_trace:
  es.contexts <> [] /\
  (FST (HD es.contexts)).stack = [] /\
  (ISR (FST (step es)) \/
   LENGTH (SND (step es)).contexts < LENGTH es.contexts) ==>
  call_trace es = []
Proof
  Cases_on `step es` >> rpt strip_tac >>
  gvs[] >>
  asm_rewrite_tac[callTraceTheory.call_trace_def, callTraceTheory.frame_obs_def] >>
  once_rewrite_tac[callTraceTheory.frame_obs_tr_def] >>
  asm_rewrite_tac[] >>
  Cases_on `q` >>
  simp[callTraceTheory.observe_def, callTraceTheory.observable_call_def] >>
  IF_CASES_TAC >> simp[]
QED

local
val witness_cs = finite_mapLib.add_finite_map_compset
  (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset ())));
val witness_cs = computeLib.add_thms
  [listTheory.SET_TO_LIST_EMPTY, alistTheory.fmap_to_alist_FEMPTY,
   finite_mapTheory.DRESTRICT_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY,
   pred_setTheory.IN_COMPL, pred_setTheory.IN_SING,
   deploy_ctor_empty_operand_set_probe, deploy_ctor_empty_spillmap_probe] witness_cs;
val witness_bc = #1 (pairSyntax.dest_pair
  (List.nth (#2 (strip_comb (concl deploy_ctor_noninit_phases)), 2)));
val witness_es = ``let s = make_asm_call_state
      (asm_oracle_initial with <| as_block_ctx := empty_block_context with bc_number := 1w;
                                 as_prev_hashes := [0w] |>) 0w 0 0 [] ^witness_bc F in
    s with contexts := MAP (\(c,r). (c with msgParams := c.msgParams with outputTo := Code 0w,r)) s.contexts``;
in
Theorem deploy_ctor_noninit_bytecode:
  ^witness_bc =
    [91w;95w;95w;128w;97w;0w;15w;144w;57w;95w;243w;91w;95w;128w;253w]
Proof
  simp_tac (srw_ss()) [stackPlanGenTheory.context_plan_ops_def,
                       asmIRTheory.data_segment_asm_def] >>
  CONV_TAC (computeLib.CBV_CONV witness_cs)
QED

end
