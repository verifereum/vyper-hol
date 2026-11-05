(* Small source-selection and emitted-cursor boundaries for deploy entry. *)
Theory ctorDeployLoweringEntrySource
Ancestors
  ctorDeployLoweringDefs e2eDeployDefs emitHelperProps compileVyper
  vyperInterpreter vyperTypeContract supportedProgram
  venomInst venomWf venomState

Theorem deploy_ctor_start_nonreentrant_false:
  !tops deploy_bc am tx es mut nr body am_c es0.
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) ==>
  nr = F
Proof
  rpt gen_tac >>
  pure_rewrite_tac[deploy_state_rel_def, deploy_ctor_start_def,
                   constructor_args_encode_def] >>
  rpt strip_tac >>
  qpat_x_assum `tx.function_name = _` (fn th =>
    qpat_x_assum `lookup_function NONE tx.function_name _ _ = _`
      (mp_tac o PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `lookup_function NONE "__init__" _ _ = _`
    (fn th => pure_rewrite_tac[th]) >>
  simp_tac bool_ss [optionTheory.SOME_11, pairTheory.PAIR_EQ]
QED

Theorem deploy_ctor_fresh_label_cursor:
  fresh_label prefix st = (lbl, st') ==>
  st'.cs_current_bb = st.cs_current_bb /\
  LENGTH st'.cs_current_insts = LENGTH st.cs_current_insts /\
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_next_id = st.cs_next_id
Proof
  strip_tac >> drule fresh_label_props >> simp[]
QED

(* Adversarial selection check: deployment visibility does not constrain name. *)
Theorem deploy_ctor_noninit_selection_probe:
  function_header_ok Deploy Payable F F "other" [] [] NoneT /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]] =
      SOME (Payable,F,[],[],NoneT,[]) /\
  classify_functions
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]] =
      ([],[],NONE,SOME (Payable,F,F,"other",[],[],NoneT,[Return NONE]))
Proof
  EVAL_TAC
QED

Theorem deploy_ctor_noninit_supported_probe:
  supported_program
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]] /\
  contract_namespaces_ok T
    [(NONE,[FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]])] /\
  contract_namespaces_ok F
    [(NONE,[FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]])]
Proof
  EVAL_TAC
QED

Theorem deploy_ctor_noninit_typecheck_probe:
  IS_SOME (check_contract T [] 0w
    [(NONE,[FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]])]) /\
  IS_SOME (check_contract F [] 0w
    [(NONE,[FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]])])
Proof
  EVAL_TAC
QED

Theorem deploy_ctor_noninit_lower_probe:
  IS_SOME (lower_vyper_deploy_unit
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> [])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED


Theorem deploy_ctor_noninit_unit_wf_probe:
  unit_wf (THE (lower_vyper_deploy_unit
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> []))
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >>
  simp[venomInstTheory.fn_insts_blocks_def, venomWfTheory.bb_well_formed_def,
       venomWfTheory.inst_wf_def, venomInstTheory.fn_labels_def,
       venomStateTheory.get_label_def, venomInstTheory.is_terminator_def] >>
  EVAL_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      `i = 0 \/ i = 1 \/ i = 2` by decide_tac >>
      gvs[venomInstTheory.is_terminator_def]) >>
  rpt strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2` by decide_tac >> gvs[]
QED

Theorem deploy_ctor_noninit_raw_inputs_probe:
  raw_static_inputs_wf (THE (lower_vyper_deploy_unit
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> [])).cu_context
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def,
    staticLayoutWfTheory.raw_static_inputs_wf_def,
    staticLayoutWfTheory.forced_positions_wf_def,
    staticLayoutDefsTheory.reserved_intervals_wf_def,
    finite_mapTheory.FEVERY_FEMPTY,
    venomInstTheory.fn_insts_blocks_def]
QED


Theorem deploy_ctor_noninit_lower_eq:
  lower_vyper_deploy_unit
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> [] =
  SOME <|cu_context :=
    <|ctx_functions :=
      [<|fn_name := "__deploy";
         fn_blocks :=
           [<|bb_label := "__deploy";
              bb_instructions :=
                [<|inst_id := 0; inst_opcode := JMP;
                   inst_operands := [Label "@ctor_exit_0"]; inst_outputs := []|>]|>;
            <|bb_label := "@ctor_exit_0";
              bb_instructions :=
                [<|inst_id := 1; inst_opcode := ALLOCA;
                   inst_operands := [Lit 0w]; inst_outputs := ["%0"]|>;
                 <|inst_id := 2; inst_opcode := CODECOPY;
                   inst_operands := [Var "%0"; Label "runtime_begin"; Lit 0w];
                   inst_outputs := []|>;
                 <|inst_id := 3; inst_opcode := RETURN;
                   inst_operands := [Var "%0"; Lit 0w]; inst_outputs := []|>]|>];
         fn_call_abi := <|ica_has_memory_return_buffer := NONE;
                          ica_user_return_count := NONE|>;
         fn_noinline := F; fn_forced_alloc_positions := FEMPTY;
         fn_eom := NONE; fn_mems_used := []; fn_fmp_signature := NONE|>];
      ctx_entry := SOME "__deploy"; ctx_global_reserved := []|>;
    cu_data_segment := [<|ds_label := "runtime_begin"; ds_items := [DataBytes []]|>]|>
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

local
  val stage_cs = computeLib.add_thms
    [venomPipelineRunnerTheory.run_callee_first_def,
     venomPipelineRunnerTheory.run_pipeline_stages_def,
     venomPipelineRunnerTheory.run_named_fn_schedules_def,
     venomFnScheduleRunnerTheory.run_configured_fn_passes_def,
     venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def,
     irSupplyTheory.fn_ir_inst_ids_def,
     irSupplyTheory.fn_ir_vars_def,
     irSupplyTheory.fn_ir_labels_def]
    (computeLib.copy (computeLib.the_compset ()));
in
Theorem deploy_ctor_noninit_simplify_probe:
  IS_SOME (run_pipeline_stage
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    (PS_MapFunctions (CFP_Simple VP_SimplifyCFG))
    (THE (lower_vyper_deploy_unit
      [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
      <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |> []))
    (init_ir_supply (THE (lower_vyper_deploy_unit
      [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
      <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |> []))))
Proof
  rewrite_tac[deploy_ctor_noninit_lower_eq] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_noninit_prewalk_eq:
  run_pipeline_stages
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    [PS_MapFunctions (CFP_Simple VP_SimplifyCFG);
     PS_MapFunctions (CFP_Simple VP_DretDesugar); PS_DiscardAnalyses]
    (THE (lower_vyper_deploy_unit
      [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
      <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |> []))
    (init_ir_supply (THE (lower_vyper_deploy_unit
      [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
      <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |> []))) =
  SOME
    (<|cu_context :=
       <|ctx_functions :=
           [<|fn_name := "__deploy";
              fn_blocks :=
                [<|bb_label := "__deploy";
                   bb_instructions :=
                     [<|inst_id := 1; inst_opcode := ALLOCA;
                        inst_operands := [Lit 0w]; inst_outputs := ["%0"]|>;
                      <|inst_id := 2; inst_opcode := CODECOPY;
                        inst_operands :=
                          [Var "%0"; Label "runtime_begin"; Lit 0w];
                        inst_outputs := []|>;
                      <|inst_id := 3; inst_opcode := RETURN;
                        inst_operands := [Var "%0"; Lit 0w];
                        inst_outputs := []|>]|>];
              fn_call_abi :=
                <|ica_has_memory_return_buffer := NONE;
                  ica_user_return_count := NONE|>; fn_noinline := F;
              fn_forced_alloc_positions := FEMPTY; fn_eom := NONE;
              fn_mems_used := []; fn_fmp_signature := NONE|>];
         ctx_entry := SOME "__deploy"; ctx_global_reserved := []|>;
     cu_data_segment :=
       [<|ds_label := "runtime_begin"; ds_items := [DataBytes []]|>]|>,
     <|irs_next_inst := 4; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := [0; 1; 2; 3]; irs_used_vars := ["%0"; "%0"; "%0"];
       irs_used_labels :=
         ["__deploy"; "__deploy"; "__deploy"; "@ctor_exit_0"; "@ctor_exit_0";
          "runtime_begin"; "runtime_begin"]|>)
Proof
  rewrite_tac[deploy_ctor_noninit_lower_eq] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

val (pre_unit, pre_supply) = pairSyntax.dest_pair
  (rand (rhs (concl deploy_ctor_noninit_prewalk_eq)));

Theorem deploy_ctor_noninit_callgraph_probe:
  fcg_postorder (fcg_analyze (^pre_unit).cu_context) "__deploy" =
    ["__deploy"] /\
  prune_unit_fcg_unreachable ^pre_unit
    (fcg_analyze (^pre_unit).cu_context) = ^pre_unit /\
  reachable_fcg_acyclic (^pre_unit).cu_context
    (fcg_analyze (^pre_unit).cu_context)
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_noninit_ssa_probe:
  run_configured_fn_passes execute_configured_fn_pass
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    [CFP_Simple VP_MakeSSA] "__deploy" ^pre_unit ^pre_supply =
    SOME (^pre_unit, ^pre_supply)
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

val dload_supply = ``^pre_supply with irs_used_labels :=
  "code_end" :: (^pre_supply).irs_used_labels``;

Theorem deploy_ctor_noninit_dload_probe:
  run_configured_fn_passes execute_configured_fn_pass
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    [CFP_Simple VP_LowerDload] "__deploy" ^pre_unit ^pre_supply =
    SOME (^pre_unit, ^dload_supply)
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

val concrete_unit = ``^pre_unit with cu_context :=
  ((^pre_unit).cu_context with ctx_functions :=
    [HD (^pre_unit).cu_context.ctx_functions with
      <|fn_blocks := [<|bb_label := "__deploy"; bb_instructions :=
        [<|inst_id := 1; inst_opcode := ASSIGN;
           inst_operands := [Lit 0w]; inst_outputs := ["%0"]|>;
         <|inst_id := 2; inst_opcode := CODECOPY;
           inst_operands := [Var "%0"; Label "runtime_begin"; Lit 0w];
           inst_outputs := []|>;
         <|inst_id := 3; inst_opcode := RETURN;
           inst_operands := [Var "%0"; Lit 0w]; inst_outputs := []|>]|>];
        fn_eom := SOME 0; fn_mems_used := [(Allocation 1,0,0)]|>])``;

Theorem deploy_ctor_noninit_concretize_probe:
  run_configured_fn_passes execute_configured_fn_pass
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    [CFP_Simple VP_ConcretizeMemLoc] "__deploy" ^pre_unit ^dload_supply =
    SOME (^concrete_unit, ^dload_supply)
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs) >>
  simp[wordsTheory.dimword_def] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

val fmp_unit = ``^concrete_unit with cu_context :=
  ((^concrete_unit).cu_context with ctx_functions :=
   [HD (^concrete_unit).cu_context.ctx_functions with fn_fmp_signature :=
     SOME <|fms_has_fmp_param := F; fms_publishes := F|>])``;

Theorem deploy_ctor_noninit_fmp_probe:
  run_configured_fn_passes execute_configured_fn_pass
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    [CFP_Simple VP_FmpLowering] "__deploy" ^concrete_unit ^dload_supply =
    SOME (^fmp_unit, ^dload_supply)
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

val final_unit = ``^fmp_unit with cu_context :=
 ((^fmp_unit).cu_context with ctx_functions :=
 [HD (^fmp_unit).cu_context.ctx_functions with fn_blocks :=
 [<|bb_label := "__deploy"; bb_instructions :=
  [<|inst_id := 4; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
     inst_outputs := ["formal_var_0"]|>;
   <|inst_id := 1; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
     inst_outputs := ["%0"]|>;
   <|inst_id := 5; inst_opcode := ASSIGN; inst_operands := [Var "%0"];
     inst_outputs := ["formal_var_1"]|>;
   <|inst_id := 2; inst_opcode := CODECOPY;
     inst_operands := [Var "formal_var_1"; Label "runtime_begin"; Var "formal_var_0"];
     inst_outputs := []|>;
   <|inst_id := 6; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
     inst_outputs := ["formal_var_2"]|>;
   <|inst_id := 7; inst_opcode := ASSIGN; inst_operands := [Var "%0"];
     inst_outputs := ["formal_var_3"]|>;
   <|inst_id := 3; inst_opcode := RETURN;
     inst_operands := [Var "formal_var_3"; Var "formal_var_2"];
     inst_outputs := []|>]|>]])``;
val final_supply = ``^dload_supply with
 <|irs_next_inst := 8; irs_next_var := 4;
   irs_used_inst_ids := [7;6;5;4;0;1;2;3];
   irs_used_vars := ["formal_var_3";"formal_var_2";"formal_var_1";
                    "formal_var_0";"%0";"%0";"%0"]|>``;

Theorem deploy_ctor_noninit_postfmp_probe:
  run_configured_fn_passes execute_configured_fn_pass
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    [CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG;
     CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
     CFP_Simple VP_CFGNormalization]
    "__deploy" ^fmp_unit ^dload_supply = SOME (^final_unit, ^final_supply)
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

end
