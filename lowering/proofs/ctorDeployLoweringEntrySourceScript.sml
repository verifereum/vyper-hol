(* Small source-selection and emitted-cursor boundaries for deploy entry. *)
Theory ctorDeployLoweringEntrySource
Ancestors
  ctorDeployLoweringDefs ctorDeployDefs e2eDeployDefs emitHelperProps compileVyper
  vyperInterpreter vyperTypeContract supportedProgram
  venomInst venomWf venomState
Libs finite_mapLib

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
  EVAL_TAC
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

Theorem deploy_ctor_fn_pass_fold_append:
  !xs s fn lm fn1 lm1 s1 ys fn2 lm2 s2.
    run_configured_fn_pass_fold runner rp xs unit s fn lm =
      SOME (fn1,lm1,s1) /\
    run_configured_fn_pass_fold runner rp ys unit s1 fn1 lm1 =
      SOME (fn2,lm2,s2) ==>
    run_configured_fn_pass_fold runner rp (xs ++ ys) unit s fn lm =
      SOME (fn2,lm2,s2)
Proof
  Induct_on `xs` >>
  simp[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

local
  val _ = load "wordsLib";
  val stage_cs = computeLib.add_thms
    [listTheory.SET_TO_LIST_EMPTY,
     venomPipelineRunnerTheory.run_callee_first_def,
     venomPipelineRunnerTheory.run_pipeline_stages_def,
     venomPipelineRunnerTheory.run_named_fn_schedules_def,
     venomFnScheduleRunnerTheory.run_configured_fn_passes_def,
     venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def,
     irSupplyTheory.fn_ir_inst_ids_def,
     irSupplyTheory.fn_ir_vars_def,
     irSupplyTheory.fn_ir_labels_def]
    (computeLib.copy (computeLib.the_compset ()));
  val stage_cs = finite_mapLib.add_finite_map_compset stage_cs;
  val stage_cs = computeLib.add_thms
    [alistTheory.fmap_to_alist_FEMPTY,
     finite_mapTheory.DRESTRICT_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY,
     pred_setTheory.IN_COMPL, pred_setTheory.IN_SING] stage_cs;
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

Theorem deploy_ctor_noninit_fold_ssa:
  run_configured_fn_pass_fold execute_configured_fn_pass
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    [CFP_Simple VP_MakeSSA; CFP_Simple VP_LowerDload]
    ^pre_unit ^pre_supply (HD (^pre_unit).cu_context.ctx_functions) [] =
    SOME (HD (^pre_unit).cu_context.ctx_functions, [], ^dload_supply)
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_noninit_fold_concretize:
  run_configured_fn_pass_fold execute_configured_fn_pass
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    [CFP_Simple VP_ConcretizeMemLoc]
    ^pre_unit ^dload_supply (HD (^pre_unit).cu_context.ctx_functions) [] =
    SOME (HD (^concrete_unit).cu_context.ctx_functions, [], ^dload_supply)
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs) >>
  simp[wordsTheory.dimword_def] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_noninit_fold_fmp:
  run_configured_fn_pass_fold execute_configured_fn_pass
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    [CFP_Simple VP_FmpLowering]
    ^pre_unit ^dload_supply (HD (^concrete_unit).cu_context.ctx_functions) [] =
    SOME (HD (^fmp_unit).cu_context.ctx_functions, [], ^dload_supply)
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_noninit_fold_postfmp:
  run_configured_fn_pass_fold execute_configured_fn_pass
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    [CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG;
     CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
     CFP_Simple VP_CFGNormalization]
    ^pre_unit ^dload_supply (HD (^fmp_unit).cu_context.ctx_functions) [] =
    SOME (HD (^final_unit).cu_context.ctx_functions, [], ^final_supply)
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_noninit_fold_all:
  run_configured_fn_pass_fold execute_configured_fn_pass
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    ([CFP_Simple VP_MakeSSA; CFP_Simple VP_LowerDload] ++
     ([CFP_Simple VP_ConcretizeMemLoc] ++
      ([CFP_Simple VP_FmpLowering] ++
       [CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG;
        CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
        CFP_Simple VP_CFGNormalization])))
    ^pre_unit ^pre_supply (HD (^pre_unit).cu_context.ctx_functions) [] =
    SOME (HD (^final_unit).cu_context.ctx_functions, [], ^final_supply)
Proof
  irule deploy_ctor_fn_pass_fold_append >>
  irule_at Any deploy_ctor_noninit_fold_ssa >>
  irule deploy_ctor_fn_pass_fold_append >>
  irule_at Any deploy_ctor_noninit_fold_concretize >>
  irule deploy_ctor_fn_pass_fold_append >>
  irule_at Any deploy_ctor_noninit_fold_fmp >>
  irule deploy_ctor_noninit_fold_postfmp
QED


Theorem deploy_ctor_noninit_schedule_eq:
  run_configured_fn_passes execute_configured_fn_pass
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    o1_fn_passes "__deploy" ^pre_unit ^pre_supply =
    SOME (^final_unit, ^final_supply)
Proof
  rewrite_tac[venomFnScheduleRunnerTheory.run_configured_fn_passes_def,
              venomPassScheduleTheory.o1_fn_passes_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_configured_fn_pass_fold``]) >>
  rewrite_tac[CONV_RULE
    (computeLib.RESTR_EVAL_CONV [``run_configured_fn_pass_fold``])
    deploy_ctor_noninit_fold_all] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_noninit_walk_eq:
  run_callee_first
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    o1_fn_passes ["__deploy"] ^pre_unit ^pre_supply =
    SOME (^final_unit, ^final_supply)
Proof
  rewrite_tac[venomPipelineRunnerTheory.run_callee_first_def,
              venomPipelineRunnerTheory.run_named_fn_schedules_def,
              deploy_ctor_noninit_schedule_eq] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_noninit_pipeline_eq:
  o1PipelineCorrect$o1_pipeline
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
    (THE (lower_vyper_deploy_unit
      [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]
      <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |> [])) =
    SOME <|po_unit := ^final_unit; po_final_assembly := FAP_Optimize|>
Proof
  rewrite_tac[o1PipelineCorrectTheory.o1_pipeline_def,
    venomPipelineDriverTheory.run_venom_pipeline_def] >>
  rewrite_tac[venomPassScheduleTheory.o1_pipeline_spec_def,
              deploy_ctor_noninit_prewalk_eq,
              deploy_ctor_noninit_lower_eq] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``run_pipeline_stages``, ``run_callee_first``]) >>
  rewrite_tac[CONV_RULE
    (computeLib.RESTR_EVAL_CONV [``run_pipeline_stages``])
    (REWRITE_RULE [deploy_ctor_noninit_lower_eq] deploy_ctor_noninit_prewalk_eq)] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``run_pipeline_stages``, ``run_callee_first``]) >>
  rewrite_tac[CONV_RULE
    (computeLib.RESTR_EVAL_CONV [``run_callee_first``])
    deploy_ctor_noninit_walk_eq] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED


Theorem deploy_ctor_codegen_computation_probe:
  SET_TO_LIST (FDOM (FEMPTY : operand |-> num)) = [] /\
  DRESTRICT ((FEMPTY : operand |-> num) |+ (Var "x",0))
    (COMPL {Var "x"}) = FEMPTY
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_noninit_max_eom_eq:
  max_live_eom (^final_unit).cu_context = SOME 0
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_stack_find_probe:
  stack_find (\x. x = Var "x") [Var "y"; Var "x"] = SOME 1
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

val final_ctx = ``(^final_unit).cu_context``;
val final_fn = ``HD (^final_ctx).ctx_functions``;
val final_fcg = ``fcg_analyze ^final_ctx``;
val final_growth = ``cleanup_growth_table ^final_ctx ^final_fcg``;
val final_ch = ``cleanup_caller_height (LENGTH (^final_ctx).ctx_functions)
                  ^final_ctx ^final_fcg "__deploy"``;

Theorem deploy_ctor_empty_operand_set_probe:
  SET_TO_LIST (EMPTY : operand set) = []
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_empty_spillmap_probe:
  fmap_to_alist (FEMPTY : operand |-> num) = []
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

val stage_cs = computeLib.add_thms
  [deploy_ctor_empty_operand_set_probe, deploy_ctor_empty_spillmap_probe] stage_cs;


Theorem deploy_ctor_noninit_fnplan_probe:
  IS_SOME (generate_fn_plan_with_cleanup ^final_ch ^final_growth ^final_fn 0 0)
Proof
  CONV_TAC (computeLib.CBV_CONV stage_cs) >>
  rewrite_tac[deploy_ctor_empty_operand_set_probe,
              deploy_ctor_empty_spillmap_probe] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs) >>
  rewrite_tac[deploy_ctor_empty_operand_set_probe,
              deploy_ctor_empty_spillmap_probe] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

val final_ops = ``[SOLabel "__deploy"; SOPush (Lit 0w); SOPush (Lit 0w);
    SODup 1; SOPushLabel "runtime_begin"; SOSwap 1; SOEmit "CODECOPY";
    SOPush (Lit 0w); SOEmit "RETURN"]``;
val final_ps = ``<|ps_stack := []; ps_spilled := FEMPTY;
    ps_alloc := <|sa_free_slots := []; sa_next_offset := 0; sa_spill_base := 0|>;
    ps_label_counter := 0; ps_cleanup_height := SOME 0;
    ps_cleanup_growth := [("__deploy",SOME 10)]; ps_cleanup_promised := F|>``;

Theorem deploy_ctor_noninit_fnplan_eq:
  generate_fn_plan_with_cleanup ^final_ch ^final_growth ^final_fn 0 0 =
    SOME (^final_ops, ^final_ps)
Proof
  CONV_TAC (LAND_CONV (computeLib.CBV_CONV stage_cs)) >>
  rewrite_tac[deploy_ctor_empty_operand_set_probe,
              deploy_ctor_empty_spillmap_probe] >>
  CONV_TAC (LAND_CONV (computeLib.CBV_CONV stage_cs)) >>
  rewrite_tac[deploy_ctor_empty_operand_set_probe,
              deploy_ctor_empty_spillmap_probe] >>
  CONV_TAC (LAND_CONV (computeLib.CBV_CONV stage_cs)) >>
  REFL_TAC
QED

val final_plan = ``<|cp_regions :=
    [<|sr_fn_name := "__deploy"; sr_spill_base := 0; sr_spill_end := 0;
       sr_plan := ^final_ops|>];
    cp_max_static_eom := 0; cp_peak_spill_end := 0; cp_initial_fmp := 0|>``;

Theorem deploy_ctor_noninit_plan_eq:
  generate_context_plan ^final_ctx = SOME ^final_plan
Proof
  rewrite_tac[stackPlanGenTheory.generate_context_plan_def,
    stackPlanGenTheory.generate_context_plan_with_def,
    deploy_ctor_noninit_max_eom_eq] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_fn_plan_with_cleanup``]) >>
  rewrite_tac[CONV_RULE
    (computeLib.RESTR_EVAL_CONV [``generate_fn_plan_with_cleanup``])
    deploy_ctor_noninit_fnplan_eq] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs) >>
  simp[wordsTheory.dimword_def]
QED

Theorem deploy_ctor_noninit_codegen_eq:
  codegen_assembly
    <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> ^final_unit =
  SOME (execute_plan 0 (context_plan_ops ^final_plan) ++
        data_segment_asm (^final_unit).cu_data_segment ++
        [AsmDataHeader "code_end"])
Proof
  rewrite_tac[codegenTheory.codegen_assembly_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_context_plan``]) >>
  rewrite_tac[CONV_RULE
    (computeLib.RESTR_EVAL_CONV [``generate_context_plan``])
    deploy_ctor_noninit_plan_eq] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

val deploy_prog = ``execute_plan 0 (context_plan_ops ^final_plan) ++
  data_segment_asm (^final_unit).cu_data_segment ++ [AsmDataHeader "code_end"]``;
val deploy_rpolicy = ``<|rpol_target := all_capabilities;
  rpol_frontend_dispatch := Linear; rpol_final_assembly := FAP_Optimize|>``;
val deploy_tops = ``[FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]``;

Theorem deploy_ctor_noninit_phases:
  deploy_phases <|cpol_target := all_capabilities|> ^deploy_tops
    (assemble ^deploy_prog, [])
    (^deploy_rpolicy, THE (lower_vyper_deploy_unit ^deploy_tops ^deploy_rpolicy []),
     <|po_unit := ^final_unit; po_final_assembly := FAP_Optimize|>,
     ^deploy_prog, ^final_plan)
Proof
  rewrite_tac[deploy_phases_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``lower_vyper_deploy_unit``, ``o1PipelineCorrect$o1_pipeline``,
     ``codegen_assembly``, ``generate_context_plan``, ``assembly_target_safe``,
     ``execute_plan``, ``data_segment_asm``, ``assemble``]) >>
  rewrite_tac[CONV_RULE (computeLib.RESTR_EVAL_CONV
    [``lower_vyper_deploy_unit``, ``o1PipelineCorrect$o1_pipeline``,
     ``codegen_assembly``, ``generate_context_plan``, ``assembly_target_safe``,
     ``execute_plan``, ``data_segment_asm``, ``assemble``])
    deploy_ctor_noninit_pipeline_eq,
    CONV_RULE (computeLib.RESTR_EVAL_CONV
    [``codegen_assembly``, ``generate_context_plan``, ``execute_plan``,
     ``data_segment_asm``]) deploy_ctor_noninit_codegen_eq,
    CONV_RULE (computeLib.RESTR_EVAL_CONV [``generate_context_plan``])
    deploy_ctor_noninit_plan_eq] >>
  rewrite_tac[CONV_RULE (computeLib.RESTR_EVAL_CONV
    [``lower_vyper_deploy_unit``]) deploy_ctor_noninit_lower_eq] >>
  CONV_TAC (computeLib.CBV_CONV stage_cs)
QED

Theorem deploy_ctor_noninit_start_body:
  tx.function_name = "__init__" /\
  deploy_ctor_start ^deploy_tops am tx (mut,nr,body',am_c,es0) ==>
  body' = []
Proof
  simp[deploy_ctor_start_def] >>
  rpt strip_tac >>
  gvs[deploy_ctor_noninit_selection_probe]
QED

val ctor_key = ``assign_nkeys ^deploy_tops 0 "other"``;
val ctor_env0 = ``(build_compile_env ^deploy_tops Deploy Payable "other" []
    NoneT [Return NONE] F) with
  <|ce_is_ctor := T; ce_raw_return := F;
    ce_nonreentrant := (F,^ctor_key,F,F); ce_target := all_capabilities|>``;

Theorem deploy_ctor_noninit_package:
  set_constructor_package_target (^deploy_rpolicy).rpol_target
    (package_constructor ^deploy_tops F (assign_nkeys ^deploy_tops 0)
      (Payable,F,F,"other",[],[],NoneT,[Return NONE])) =
  (^ctor_env0,[],T,F,^ctor_key,F,[Return NONE],NoneT)
Proof
  simp[package_constructor_def, set_constructor_package_target_def,
       update_cenv_nonreentrant_def, build_positional_args_def]
QED

val ctor_env1 = ``^ctor_env0 with ce_imm_alloca := NONE``;
val ctor_env = ``^ctor_env1 with ce_ctor_exit_label := SOME "@ctor_exit_0"``;
val closed_state = rhs o concl o EVAL;
val ctor_init = closed_state ``initial_compile_state "__deploy"``;
val ctor_sa = closed_state ``SND (fresh_label "ctor_exit" ^ctor_init)``;
val ctor_sb = closed_state ``SND (emit_inst JMP [Label "@ctor_exit_0"] [] ^ctor_sa)``;
val ctor_exit = closed_state ``SND (new_block "@ctor_exit_0" ^ctor_sb)``;
val ctor_old = closed_state ``FST (new_block "@ctor_exit_0" ^ctor_sb)``;
val ctor_final = closed_state ``SND (compile_constructor_epilogue 0 0 (Lit 0w) ^ctor_exit)``;

Theorem deploy_ctor_noninit_body_compile:
  compile_stmts ^ctor_env NoLoop NoneT [Return NONE] ^ctor_sa = ((),^ctor_sb)
Proof
  simp[stmtLoweringTheory.compile_stmt_def,
       build_compile_env_deploy_no_internal_return] >>
  EVAL_TAC
QED

val ctor_unit = ``THE (lower_vyper_deploy_unit ^deploy_tops ^deploy_rpolicy [])``;
val ctor_func = ``HD (^ctor_unit).cu_context.ctx_functions``;

Theorem deploy_ctor_noninit_code:
  deploy_ctor_code ^deploy_tops ^deploy_rpolicy [] ^ctor_unit
    ([Return NONE],^ctor_env,F,^ctor_key,F,Lit 0w,"@ctor_exit_0",
     ^ctor_sa,^ctor_sb,^ctor_sb,^ctor_exit,^ctor_exit,^ctor_final,^ctor_func)
Proof
  rewrite_tac[deploy_ctor_code_def] >>
  qexistsl [`[]`, `[]`, `NONE`,
    `(Payable,F,F,"other",[],[],NoneT,[Return NONE])`,
    `^ctor_env0`, `[]`, `T`, `NoneT`, `0`, `^ctor_init`,
    `^ctor_init`, `^ctor_env1`, `^ctor_init`, `^ctor_init`, `^ctor_old`] >>
  rewrite_tac[deploy_ctor_noninit_package,deploy_ctor_noninit_body_compile,
              deploy_ctor_noninit_lower_eq] >>
  simp[moduleLoweringTheory.compile_register_constructor_args_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``build_compile_env``, ``assign_nkeys``]) >>
  simp[boolTheory.EXISTS_DEF] >> SELECT_ELIM_TAC >> simp[]
QED

end
