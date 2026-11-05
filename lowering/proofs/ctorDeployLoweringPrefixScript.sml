(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringPrefix
Ancestors
  ctorDeployLoweringDefs o1PassContract vyperTypeContractSoundness
  vyperContext e2eDefs vyperInterpreter

Theorem deploy_prefix_abi_not_binding:
  vyper_to_abi_list FEMPTY [BaseT (UintT 256)] [IntV (-1)] =
    SOME [NumV (Num (-1))] /\
  bind_arguments FEMPTY [("x", BaseT (UintT 256))] [IntV (-1)] = NONE
Proof
  EVAL_TAC >> simp[]
QED

Theorem deploy_prefix_negative_tx_typed:
  call_tx_well_typed (empty_call_txn with args := [IntV (-1)])
Proof
  simp[call_tx_well_typed_def, empty_call_txn_def]
QED

Theorem deploy_prefix_binding_error_not_exempt:
  !tops. ~unspecified_behaviour_exempt tops (RuntimeError "call bind_arguments")
Proof
  simp[unspecified_behaviour_exempt_def]
QED

Theorem deploy_prefix_negative_no_start:
  !am tx mut nr body am_c es0.
  tx.function_name = "__init__" /\ tx.args = [IntV (-1)] ==>
  ~deploy_ctor_start
    [FunctionDecl Deploy Payable F F "__init__"
       [("x", BaseT (UintT 256))] [] NoneT []]
    am tx (mut,nr,body,am_c,es0)
Proof
  simp[deploy_ctor_start_def, lookup_function_def, type_env_all_modules_def,
       type_env_def] >> EVAL_TAC >> simp[]
QED

Theorem deploy_prefix_negative_source_probe:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let tx = empty_call_txn with <|function_name := "__init__";
                                args := [IntV (-1)]|> in
  deploy_source_ok tops initial_machine_state tx /\
  (!gobs. load_contract NONE gobs initial_machine_state tx [(NONE,tops)] [] =
          INR (Error (RuntimeError "call bind_arguments")))
Proof
  EVAL_TAC >>
  simp[vyperStateTheory.find_var_decl_by_name_def,
       supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
       vyperStateTheory.raise_def, COND_RAND, COND_RATOR]
QED

Theorem deploy_prefix_negative_lowering_probe:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  IS_SOME (lower_vyper_deploy_unit tops rp [])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem deploy_prefix_negative_unit_wf_probe:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  venomCompilerWf$unit_wf (THE (lower_vyper_deploy_unit tops rp []))
Proof
  EVAL_TAC >>
  simp[wordsTheory.dimword_def, venomInstTheory.fn_insts_blocks_def,
       venomWfTheory.bb_well_formed_compute, venomWfTheory.inst_wf_def,
       venomInstTheory.is_terminator_def, venomStateTheory.get_label_def,
       venomInstTheory.fn_labels_def] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_static_probe:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  staticLayoutWf$raw_static_inputs_wf
    (THE (lower_vyper_deploy_unit tops rp [])).cu_context
Proof
  simp[LET_THM, staticLayoutWfTheory.raw_static_inputs_wf_def,
       staticLayoutWfTheory.forced_positions_wf_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def,
                   venomInstTheory.fn_insts_blocks_def] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_prewalk_probe:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  let unit = THE (lower_vyper_deploy_unit tops rp []) in
  IS_SOME (venomPipelineRunner$run_pipeline_stages rp
    venomPassSchedule$o1_pipeline_spec.ps_pre_walk_stages unit
    (irSupply$init_ir_supply unit))
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_lowered_artifact:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  lower_vyper_deploy_unit tops rp [] = SOME
    <|cu_context :=
      <|ctx_functions :=
        [<|fn_name := "__deploy";
           fn_blocks :=
             [<|bb_label := "__deploy"; bb_instructions :=
                [<|inst_id := 0; inst_opcode := ALLOCA;
                   inst_operands := [Lit 32w]; inst_outputs := ["%0"]|>;
                 <|inst_id := 1; inst_opcode := ADD;
                   inst_operands := [Lit 0w; Lit 0w]; inst_outputs := ["%1"]|>;
                 <|inst_id := 2; inst_opcode := DLOAD;
                   inst_operands := [Var "%1"]; inst_outputs := ["%2"]|>;
                 <|inst_id := 3; inst_opcode := MSTORE;
                   inst_operands := [Var "%0"; Var "%2"]; inst_outputs := []|>;
                 <|inst_id := 4; inst_opcode := JMP;
                   inst_operands := [Label "@ctor_exit_0"]; inst_outputs := []|>]|>;
              <|bb_label := "@ctor_exit_0"; bb_instructions :=
                [<|inst_id := 5; inst_opcode := ALLOCA;
                   inst_operands := [Lit 0w]; inst_outputs := ["%3"]|>;
                 <|inst_id := 6; inst_opcode := CODECOPY;
                   inst_operands := [Var "%3"; Label "runtime_begin"; Lit 0w];
                   inst_outputs := []|>;
                 <|inst_id := 7; inst_opcode := RETURN;
                   inst_operands := [Var "%3"; Lit 0w]; inst_outputs := []|>]|>];
           fn_call_abi := <|ica_has_memory_return_buffer := NONE;
                           ica_user_return_count := NONE|>;
           fn_noinline := F; fn_forced_alloc_positions := FEMPTY;
           fn_eom := NONE; fn_mems_used := []; fn_fmp_signature := NONE|>];
        ctx_entry := SOME "__deploy"; ctx_global_reserved := []|>;
      cu_data_segment := [<|ds_label := "runtime_begin"; ds_items := [DataBytes []]|>]|>
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem deploy_prefix_negative_supply_artifact:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  irSupply$init_ir_supply (THE (lower_vyper_deploy_unit tops rp [])) =
    <|irs_next_inst := 8; irs_next_var := 0; irs_next_label := 0;
      irs_used_inst_ids := [0;1;2;3;4;5;6;7];
      irs_used_vars := ["%0";"%1";"%2";"%1";"%0";"%2";"%3";"%3";"%3"];
      irs_used_labels := ["__deploy";"__deploy";"__deploy";
                          "@ctor_exit_0";"@ctor_exit_0";"runtime_begin";
                          "runtime_begin"]|>
Proof
  simp_tac bool_ss [LET_THM] >>
  pure_rewrite_tac[deploy_prefix_negative_lowered_artifact |>
                   SIMP_RULE bool_ss [LET_THM]] >>
  simp[irSupplyTheory.init_ir_supply_def,
       irSupplyTheory.unit_ir_inst_ids_def, irSupplyTheory.unit_ir_vars_def,
       irSupplyTheory.unit_ir_labels_def, irSupplyTheory.fn_ir_inst_ids_def,
       irSupplyTheory.fn_ir_vars_def, irSupplyTheory.fn_ir_labels_def,
       irSupplyTheory.data_section_ir_labels_def,
       irSupplyTheory.block_ir_inst_ids_def, irSupplyTheory.block_ir_vars_def,
       irSupplyTheory.block_ir_labels_def, irSupplyTheory.inst_ir_vars_def,
       irSupplyTheory.inst_ir_labels_def] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_prewalk_artifact:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  let unit = THE (lower_vyper_deploy_unit tops rp []) in
  venomPipelineRunner$run_pipeline_stages rp
    venomPassSchedule$o1_pipeline_spec.ps_pre_walk_stages unit
    (irSupply$init_ir_supply unit) = SOME
    (<|cu_context :=
      <|ctx_functions :=
        [<|fn_name := "__deploy";
           fn_blocks :=
             [<|bb_label := "__deploy"; bb_instructions :=
                [<|inst_id := 0; inst_opcode := ALLOCA;
                   inst_operands := [Lit 32w]; inst_outputs := ["%0"]|>;
                 <|inst_id := 1; inst_opcode := ADD;
                   inst_operands := [Lit 0w; Lit 0w]; inst_outputs := ["%1"]|>;
                 <|inst_id := 2; inst_opcode := DLOAD;
                   inst_operands := [Var "%1"]; inst_outputs := ["%2"]|>;
                 <|inst_id := 3; inst_opcode := MSTORE;
                   inst_operands := [Var "%0"; Var "%2"]; inst_outputs := []|>;
                 <|inst_id := 5; inst_opcode := ALLOCA;
                   inst_operands := [Lit 0w]; inst_outputs := ["%3"]|>;
                 <|inst_id := 6; inst_opcode := CODECOPY;
                   inst_operands := [Var "%3"; Label "runtime_begin"; Lit 0w];
                   inst_outputs := []|>;
                 <|inst_id := 7; inst_opcode := RETURN;
                   inst_operands := [Var "%3"; Lit 0w]; inst_outputs := []|>]|>];
           fn_call_abi := <|ica_has_memory_return_buffer := NONE;
                           ica_user_return_count := NONE|>;
           fn_noinline := F; fn_forced_alloc_positions := FEMPTY;
           fn_eom := NONE; fn_mems_used := []; fn_fmp_signature := NONE|>];
        ctx_entry := SOME "__deploy"; ctx_global_reserved := []|>;
      cu_data_segment := [<|ds_label := "runtime_begin"; ds_items := [DataBytes []]|>]|>,
     <|irs_next_inst := 8; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := [0;1;2;3;4;5;6;7];
       irs_used_vars := ["%0";"%1";"%2";"%1";"%0";"%2";"%3";"%3";"%3"];
       irs_used_labels := ["__deploy";"__deploy";"__deploy";
                           "@ctor_exit_0";"@ctor_exit_0";"runtime_begin";
                           "runtime_begin"]|>)
Proof
  simp_tac bool_ss [LET_THM] >>
  pure_rewrite_tac[deploy_prefix_negative_supply_artifact |>
                    SIMP_RULE bool_ss [LET_THM],
                  deploy_prefix_negative_lowered_artifact |>
                    SIMP_RULE bool_ss [LET_THM]] >>
  EVAL_TAC
QED

Theorem deploy_prefix_negative_schedule_artifact:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  let unit = THE (lower_vyper_deploy_unit tops rp []) in
  let (pre,supply) = THE (venomPipelineRunner$run_pipeline_stages rp
    venomPassSchedule$o1_pipeline_spec.ps_pre_walk_stages unit
    (irSupply$init_ir_supply unit)) in
  fcgDefs$fcg_postorder (fcgDefs$fcg_analyze pre.cu_context) "__deploy" =
    ["__deploy"] /\
  fcgPruning$prune_unit_fcg_unreachable pre (fcgDefs$fcg_analyze pre.cu_context) = pre
Proof
  simp_tac bool_ss [LET_THM] >>
  pure_rewrite_tac[deploy_prefix_negative_prewalk_artifact |>
                    SIMP_RULE bool_ss [LET_THM]] >>
  EVAL_TAC >> simp[venomInstTheory.fn_insts_blocks_def] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_ssa_artifact:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  let unit = THE (lower_vyper_deploy_unit tops rp []) in
  let (pre,supply) = THE (venomPipelineRunner$run_pipeline_stages rp
    venomPassSchedule$o1_pipeline_spec.ps_pre_walk_stages unit
    (irSupply$init_ir_supply unit)) in
  venomFnScheduleRunner$run_configured_fn_passes
    venomPassDispatcher$execute_configured_fn_pass rp
    [CFP_Simple VP_MakeSSA] "__deploy" pre supply = SOME (pre,supply)
Proof
  simp_tac bool_ss [LET_THM] >>
  pure_rewrite_tac[deploy_prefix_negative_prewalk_artifact |>
                    SIMP_RULE bool_ss [LET_THM]] >>
  EVAL_TAC
QED

Theorem deploy_prefix_negative_dload_artifact:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  let unit = THE (lower_vyper_deploy_unit tops rp []) in
  let (pre,supply) = THE (venomPipelineRunner$run_pipeline_stages rp
    venomPassSchedule$o1_pipeline_spec.ps_pre_walk_stages unit
    (irSupply$init_ir_supply unit)) in
  venomFnScheduleRunner$run_configured_fn_passes
    venomPassDispatcher$execute_configured_fn_pass rp
    [CFP_Simple VP_LowerDload] "__deploy" pre supply = SOME
    (<|cu_context :=
      <|ctx_functions :=
        [<|fn_name := "__deploy";
           fn_blocks :=
             [<|bb_label := "__deploy"; bb_instructions :=
                [<|inst_id := 0; inst_opcode := ALLOCA;
                   inst_operands := [Lit 32w]; inst_outputs := ["%0"]|>;
                 <|inst_id := 1; inst_opcode := ADD;
                   inst_operands := [Lit 0w; Lit 0w]; inst_outputs := ["%1"]|>;
                 <|inst_id := 8; inst_opcode := ALLOCA;
                   inst_operands := [Lit 32w]; inst_outputs := ["formal_var_0"]|>;
                 <|inst_id := 9; inst_opcode := ADD;
                   inst_operands := [Var "%1"; Label "code_end"];
                   inst_outputs := ["formal_var_1"]|>;
                 <|inst_id := 10; inst_opcode := CODECOPY;
                   inst_operands := [Var "formal_var_0"; Var "formal_var_1"; Lit 32w];
                   inst_outputs := []|>;
                 <|inst_id := 11; inst_opcode := MLOAD;
                   inst_operands := [Var "formal_var_0"]; inst_outputs := ["%2"]|>;
                 <|inst_id := 3; inst_opcode := MSTORE;
                   inst_operands := [Var "%0"; Var "%2"]; inst_outputs := []|>;
                 <|inst_id := 5; inst_opcode := ALLOCA;
                   inst_operands := [Lit 0w]; inst_outputs := ["%3"]|>;
                 <|inst_id := 6; inst_opcode := CODECOPY;
                   inst_operands := [Var "%3"; Label "runtime_begin"; Lit 0w];
                   inst_outputs := []|>;
                 <|inst_id := 7; inst_opcode := RETURN;
                   inst_operands := [Var "%3"; Lit 0w]; inst_outputs := []|>]|>];
           fn_call_abi := <|ica_has_memory_return_buffer := NONE;
                           ica_user_return_count := NONE|>;
           fn_noinline := F; fn_forced_alloc_positions := FEMPTY;
           fn_eom := NONE; fn_mems_used := []; fn_fmp_signature := NONE|>];
        ctx_entry := SOME "__deploy"; ctx_global_reserved := []|>;
      cu_data_segment := [<|ds_label := "runtime_begin"; ds_items := [DataBytes []]|>]|>,
     <|irs_next_inst := 12; irs_next_var := 2; irs_next_label := 0;
       irs_used_inst_ids := [11;10;9;8;0;1;2;3;4;5;6;7];
       irs_used_vars := ["formal_var_1";"formal_var_0";
                         "%0";"%1";"%2";"%1";"%0";"%2";"%3";"%3";"%3"];
       irs_used_labels := ["code_end";"__deploy";"__deploy";"__deploy";
                           "@ctor_exit_0";"@ctor_exit_0";"runtime_begin";
                           "runtime_begin"]|>)
Proof
  simp_tac bool_ss [LET_THM] >>
  pure_rewrite_tac[deploy_prefix_negative_prewalk_artifact |>
                    SIMP_RULE bool_ss [LET_THM]] >>
  EVAL_TAC
QED

(* ML term abbreviations only: no logical constants are introduced. *)
val prefix_dload_unit_tm = deploy_prefix_negative_dload_artifact
  |> concl |> find_term (fn tm => is_eq tm andalso
       optionSyntax.is_some (rhs tm)) |> rhs |> rand
  |> pairSyntax.dest_pair |> fst;
val prefix_dload_fn_tm =
  ``HD (^prefix_dload_unit_tm).cu_context.ctx_functions``;

Theorem deploy_prefix_negative_cfg_artifact:
  cfgDefs$cfg_analyze ^prefix_dload_fn_tm =
    <|cfg_succs := FEMPTY |+ ("__deploy", []);
      cfg_preds := FEMPTY |+ ("__deploy", []);
      cfg_reachable := FEMPTY |+ ("__deploy", T);
      cfg_dfs_post := ["__deploy"]; cfg_dfs_pre := ["__deploy"]|>
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem deploy_prefix_negative_bp_artifact:
  concretizeMemLocDefs$bp_analyze_fuel 48
    (cfgDefs$cfg_analyze ^prefix_dload_fn_tm) ^prefix_dload_fn_tm =
  FEMPTY |+ ("%0", [Ptr (Allocation 0) (SOME 0)])
         |+ ("formal_var_0", [Ptr (Allocation 8) (SOME 0)])
         |+ ("%3", [Ptr (Allocation 5) (SOME 0)])
Proof
  pure_rewrite_tac[deploy_prefix_negative_cfg_artifact] >> EVAL_TAC >>
  simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> simp[]
QED

Theorem deploy_prefix_negative_alloc_items_artifact:
  concretizeMemLocDefs$static_alloca_items ^prefix_dload_fn_tm =
    SOME [(Allocation 0,32); (Allocation 8,32); (Allocation 5,0)]
Proof
  EVAL_TAC >> simp[wordsTheory.word_0_n2w, wordsTheory.w2n_n2w,
                   wordsTheory.dimword_def]
QED

Theorem deploy_prefix_addr_cmp_probe:
  toto$apto concretizeMemLocDefs$inst_addr_to ("__deploy",8) ("__deploy",9) = LESS
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_addr_merge_probe:
  enumeral$smerge concretizeMemLocDefs$inst_addr_to
    [("__deploy",8)] [("__deploy",9)] = [("__deploy",8);("__deploy",9)]
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_addr_merge_same_probe:
  enumeral$smerge concretizeMemLocDefs$inst_addr_to
    [("__deploy",8)] [("__deploy",8)] = [("__deploy",8)]
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_addr_inter_probe:
  enumeral$sinter concretizeMemLocDefs$inst_addr_to
    [("__deploy",8)] [("__deploy",9)] = []
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_word_size_probe:
  words$w2n (32w : 256 word) = 32
Proof
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem deploy_prefix_word_zero_probe:
  words$w2n (0w : 256 word) = 0
Proof
  simp[wordsTheory.word_0_n2w, wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

val _ = computeLib.add_funs
  [deploy_prefix_word_size_probe, deploy_prefix_word_zero_probe];

Theorem deploy_prefix_word_eval_probe:
  words$w2n (32w : 256 word) = 32 /\
  words$w2n (0w : 256 word) = 0
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_alloc_size_0:
  concretizeMemLocDefs$get_alloca_size ^prefix_dload_fn_tm (Allocation 0) = 32
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_alloc_size_8:
  concretizeMemLocDefs$get_alloca_size ^prefix_dload_fn_tm (Allocation 8) = 32
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_alloc_size_5:
  concretizeMemLocDefs$get_alloca_size ^prefix_dload_fn_tm (Allocation 5) = 0
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_negative_alloc_map_artifact:
  concretizeMemLocDefs$compute_alloc_map_fuel_in_context 48
    (^prefix_dload_unit_tm).cu_context ^prefix_dload_fn_tm
    (concretizeMemLocDefs$bp_analyze_fuel 48
      (cfgDefs$cfg_analyze ^prefix_dload_fn_tm) ^prefix_dload_fn_tm)
    (cfgDefs$cfg_analyze ^prefix_dload_fn_tm) FEMPTY [] =
    FEMPTY |+ (Allocation 0,0) |+ (Allocation 5,0) |+ (Allocation 8,0)
Proof
  pure_rewrite_tac[deploy_prefix_negative_bp_artifact,
                   deploy_prefix_negative_cfg_artifact,
                   deploy_prefix_negative_alloc_items_artifact,
                   deploy_prefix_alloc_size_0, deploy_prefix_alloc_size_8,
                   deploy_prefix_alloc_size_5] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_layout_artifact:
  concretizeMemLocDefs$compute_function_layout_fuel_in_context 48
    (^prefix_dload_unit_tm).cu_context [] ^prefix_dload_fn_tm =
    SOME <|cl_positions := FEMPTY |+ (Allocation 0,0)
            |+ (Allocation 5,0) |+ (Allocation 8,0); cl_eom := 32|>
Proof
  pure_rewrite_tac[concretizeMemLocDefsTheory.compute_function_layout_fuel_in_context_def,
    deploy_prefix_negative_alloc_items_artifact] >>
  simp_tac bool_ss [LET_THM] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``cfgDefs$cfg_analyze``, ``concretizeMemLocDefs$bp_analyze_fuel``,
     ``concretizeMemLocDefs$compute_alloc_map_fuel_in_context``]) >>
  pure_rewrite_tac[deploy_prefix_negative_bp_artifact,
                  deploy_prefix_negative_cfg_artifact,
                  deploy_prefix_negative_alloc_map_artifact] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_concrete_fn_artifact:
  concretizeMemLocDefs$concretize_function_fuel_in_context 48
    (^prefix_dload_unit_tm).cu_context [] ^prefix_dload_fn_tm =
  SOME (^prefix_dload_fn_tm with
    <|fn_blocks := [<|bb_label := "__deploy"; bb_instructions :=
       [<|inst_id := 0; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
          inst_outputs := ["%0"]|>;
        <|inst_id := 1; inst_opcode := ADD; inst_operands := [Lit 0w; Lit 0w];
          inst_outputs := ["%1"]|>;
        <|inst_id := 8; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
          inst_outputs := ["formal_var_0"]|>;
        <|inst_id := 9; inst_opcode := ADD; inst_operands := [Var "%1"; Label "code_end"];
          inst_outputs := ["formal_var_1"]|>;
        <|inst_id := 10; inst_opcode := CODECOPY;
          inst_operands := [Var "formal_var_0"; Var "formal_var_1"; Lit 32w];
          inst_outputs := []|>;
        <|inst_id := 11; inst_opcode := MLOAD; inst_operands := [Var "formal_var_0"];
          inst_outputs := ["%2"]|>;
        <|inst_id := 3; inst_opcode := MSTORE; inst_operands := [Var "%0"; Var "%2"];
          inst_outputs := []|>;
        <|inst_id := 5; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
          inst_outputs := ["%3"]|>;
        <|inst_id := 6; inst_opcode := CODECOPY;
          inst_operands := [Var "%3"; Label "runtime_begin"; Lit 0w]; inst_outputs := []|>;
        <|inst_id := 7; inst_opcode := RETURN; inst_operands := [Var "%3"; Lit 0w];
          inst_outputs := []|>]|>];
      fn_eom := SOME 32;
      fn_mems_used := [(Allocation 0,0,32);(Allocation 8,0,32);(Allocation 5,0,0)]|>)
Proof
  pure_rewrite_tac[concretizeMemLocDefsTheory.concretize_function_fuel_in_context_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``concretizeMemLocDefs$compute_function_layout_fuel_in_context``]) >>
  pure_rewrite_tac[deploy_prefix_negative_layout_artifact |>
    CONV_RULE (LAND_CONV (computeLib.RESTR_EVAL_CONV
      [``concretizeMemLocDefs$compute_function_layout_fuel_in_context``]))] >>
  EVAL_TAC
QED

val prefix_dload_supply_tm = deploy_prefix_negative_dload_artifact
  |> concl |> find_term (fn tm => is_eq tm andalso
       optionSyntax.is_some (rhs tm)) |> rhs |> rand
  |> pairSyntax.dest_pair |> snd;
val prefix_concrete_fn_tm = deploy_prefix_negative_concrete_fn_artifact
  |> concl |> rhs |> rand;
val prefix_concrete_unit_tm =
  ``^prefix_dload_unit_tm with cu_context :=
    ((^prefix_dload_unit_tm).cu_context with ctx_functions := [^prefix_concrete_fn_tm])``;

Theorem deploy_prefix_negative_concretize_artifact:
  venomFnScheduleRunner$run_configured_fn_passes
    venomPassDispatcher$execute_configured_fn_pass
    (THE (resolve_o1_policy (o1_policy all_capabilities)))
    [CFP_Simple VP_ConcretizeMemLoc] "__deploy"
    ^prefix_dload_unit_tm ^prefix_dload_supply_tm =
    SOME (^prefix_concrete_unit_tm, ^prefix_dload_supply_tm)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``concretizeMemLocDefs$concretize_function_fuel_in_context``]) >>
  pure_rewrite_tac[deploy_prefix_negative_concrete_fn_artifact |>
    CONV_RULE (LAND_CONV (computeLib.RESTR_EVAL_CONV
      [``concretizeMemLocDefs$concretize_function_fuel_in_context``]))] >>
  EVAL_TAC
QED

val prefix_fmp_unit_tm =
  ``^prefix_concrete_unit_tm with cu_context :=
    ((^prefix_concrete_unit_tm).cu_context with ctx_functions :=
      [^prefix_concrete_fn_tm with fn_fmp_signature :=
         SOME <|fms_has_fmp_param := F; fms_publishes := F|>])``;

Theorem deploy_prefix_negative_fmp_artifact:
  venomFnScheduleRunner$run_configured_fn_passes
    venomPassDispatcher$execute_configured_fn_pass
    (THE (resolve_o1_policy (o1_policy all_capabilities)))
    [CFP_Simple VP_FmpLowering] "__deploy"
    ^prefix_concrete_unit_tm ^prefix_dload_supply_tm =
    SOME (^prefix_fmp_unit_tm, ^prefix_dload_supply_tm)
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_negative_ssa2_artifact:
  venomFnScheduleRunner$run_configured_fn_passes
    venomPassDispatcher$execute_configured_fn_pass
    (THE (resolve_o1_policy (o1_policy all_capabilities)))
    [CFP_Simple VP_MakeSSA] "__deploy"
    ^prefix_fmp_unit_tm ^prefix_dload_supply_tm =
    SOME (^prefix_fmp_unit_tm, ^prefix_dload_supply_tm)
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_negative_cfg2_artifact:
  venomFnScheduleRunner$run_configured_fn_passes
    venomPassDispatcher$execute_configured_fn_pass
    (THE (resolve_o1_policy (o1_policy all_capabilities)))
    [CFP_Simple VP_SimplifyCFG] "__deploy"
    ^prefix_fmp_unit_tm ^prefix_dload_supply_tm =
    SOME (^prefix_fmp_unit_tm, ^prefix_dload_supply_tm)
Proof
  EVAL_TAC
QED

val prefix_sue_insts_tm = ``[
  <|inst_id := 0; inst_opcode := ASSIGN; inst_operands := [Lit 0w]; inst_outputs := ["%0"]|>;
  <|inst_id := 13; inst_opcode := ASSIGN; inst_operands := [Lit 0w]; inst_outputs := ["formal_var_3"]|>;
  <|inst_id := 12; inst_opcode := ASSIGN; inst_operands := [Lit 0w]; inst_outputs := ["formal_var_2"]|>;
  <|inst_id := 1; inst_opcode := ADD; inst_operands := [Var "formal_var_3"; Var "formal_var_2"]; inst_outputs := ["%1"]|>;
  <|inst_id := 8; inst_opcode := ASSIGN; inst_operands := [Lit 0w]; inst_outputs := ["formal_var_0"]|>;
  <|inst_id := 9; inst_opcode := ADD; inst_operands := [Var "%1"; Label "code_end"]; inst_outputs := ["formal_var_1"]|>;
  <|inst_id := 15; inst_opcode := ASSIGN; inst_operands := [Var "formal_var_0"]; inst_outputs := ["formal_var_5"]|>;
  <|inst_id := 14; inst_opcode := ASSIGN; inst_operands := [Lit 32w]; inst_outputs := ["formal_var_4"]|>;
  <|inst_id := 10; inst_opcode := CODECOPY; inst_operands := [Var "formal_var_5"; Var "formal_var_1"; Var "formal_var_4"]; inst_outputs := []|>;
  <|inst_id := 16; inst_opcode := ASSIGN; inst_operands := [Var "formal_var_0"]; inst_outputs := ["formal_var_6"]|>;
  <|inst_id := 11; inst_opcode := MLOAD; inst_operands := [Var "formal_var_6"]; inst_outputs := ["%2"]|>;
  <|inst_id := 3; inst_opcode := MSTORE; inst_operands := [Var "%0"; Var "%2"]; inst_outputs := []|>;
  <|inst_id := 5; inst_opcode := ASSIGN; inst_operands := [Lit 0w]; inst_outputs := ["%3"]|>;
  <|inst_id := 18; inst_opcode := ASSIGN; inst_operands := [Var "%3"]; inst_outputs := ["formal_var_8"]|>;
  <|inst_id := 17; inst_opcode := ASSIGN; inst_operands := [Lit 0w]; inst_outputs := ["formal_var_7"]|>;
  <|inst_id := 6; inst_opcode := CODECOPY; inst_operands := [Var "formal_var_8"; Label "runtime_begin"; Var "formal_var_7"]; inst_outputs := []|>;
  <|inst_id := 20; inst_opcode := ASSIGN; inst_operands := [Var "%3"]; inst_outputs := ["formal_var_10"]|>;
  <|inst_id := 19; inst_opcode := ASSIGN; inst_operands := [Lit 0w]; inst_outputs := ["formal_var_9"]|>;
  <|inst_id := 7; inst_opcode := RETURN; inst_operands := [Var "formal_var_10"; Var "formal_var_9"]; inst_outputs := []|>]``;
val prefix_sue_unit_tm = ``^prefix_fmp_unit_tm with cu_context :=
  ((^prefix_fmp_unit_tm).cu_context with ctx_functions :=
    [(HD ((^prefix_fmp_unit_tm).cu_context.ctx_functions)) with fn_blocks :=
      [<|bb_label := "__deploy"; bb_instructions := ^prefix_sue_insts_tm|>]])``;
val prefix_sue_supply_tm = ``<|irs_next_inst := 21; irs_next_var := 11; irs_next_label := 0;
  irs_used_inst_ids := [20;19;18;17;16;15;14;13;12;11;10;9;8;0;1;2;3;4;5;6;7];
  irs_used_vars := ["formal_var_10";"formal_var_9";"formal_var_8";"formal_var_7";"formal_var_6";
    "formal_var_5";"formal_var_4";"formal_var_3";"formal_var_2";"formal_var_1";"formal_var_0";
    "%0";"%1";"%2";"%1";"%0";"%2";"%3";"%3";"%3"];
  irs_used_labels := ["code_end";"__deploy";"__deploy";"__deploy";"@ctor_exit_0";"@ctor_exit_0";
    "runtime_begin";"runtime_begin"]|>``;

Theorem deploy_prefix_negative_sue_artifact:
  venomFnScheduleRunner$run_configured_fn_passes
    venomPassDispatcher$execute_configured_fn_pass
    (THE (resolve_o1_policy (o1_policy all_capabilities)))
    [CFP_Simple VP_SingleUseExpansion] "__deploy"
    ^prefix_fmp_unit_tm ^prefix_dload_supply_tm =
    SOME (^prefix_sue_unit_tm, ^prefix_sue_supply_tm)
Proof
  EVAL_TAC
QED

val prefix_sue_insts = prefix_sue_insts_tm |> listSyntax.dest_list |> fst;
val prefix_dft_insts_tm = listSyntax.mk_list
  (map (fn n => List.nth (prefix_sue_insts,n))
    [7,2,1,3,5,4,6,8,9,10,0,11,14,12,13,15,17,16,18],
   type_of (hd prefix_sue_insts));
val prefix_dft_unit_tm = ``^prefix_sue_unit_tm with cu_context :=
  ((^prefix_sue_unit_tm).cu_context with ctx_functions :=
    [(HD ((^prefix_sue_unit_tm).cu_context.ctx_functions)) with fn_blocks :=
      [<|bb_label := "__deploy"; bb_instructions := ^prefix_dft_insts_tm|>]])``;

Theorem deploy_prefix_negative_dft_artifact:
  venomFnScheduleRunner$run_configured_fn_passes
    venomPassDispatcher$execute_configured_fn_pass
    (THE (resolve_o1_policy (o1_policy all_capabilities)))
    [CFP_Simple VP_DFT] "__deploy"
    ^prefix_sue_unit_tm ^prefix_sue_supply_tm =
    SOME (^prefix_dft_unit_tm, ^prefix_sue_supply_tm)
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_negative_normalize_artifact:
  venomFnScheduleRunner$run_configured_fn_passes
    venomPassDispatcher$execute_configured_fn_pass
    (THE (resolve_o1_policy (o1_policy all_capabilities)))
    [CFP_Simple VP_CFGNormalization] "__deploy"
    ^prefix_dft_unit_tm ^prefix_sue_supply_tm =
    SOME (^prefix_dft_unit_tm, ^prefix_sue_supply_tm)
Proof
  EVAL_TAC
QED

(* Normalize syntax only; these ML abbreviations introduce no HOL constants. *)
fun prefix_normal_tm tm = computeLib.EVAL_CONV tm |> concl |> rhs;
val prefix_pre_pair_tm = deploy_prefix_negative_prewalk_artifact
  |> concl |> find_term (fn tm => is_eq tm andalso optionSyntax.is_some (rhs tm))
  |> rhs |> rand |> pairSyntax.dest_pair;
val prefix_pre_unit_tm = prefix_normal_tm (fst prefix_pre_pair_tm);
val prefix_pre_supply_tm = prefix_normal_tm (snd prefix_pre_pair_tm);
val prefix_final_unit_tm = prefix_normal_tm prefix_dft_unit_tm;
val prefix_final_supply_tm = prefix_normal_tm prefix_sue_supply_tm;
val prefix_final_fn_tm = prefix_normal_tm
  ``HD ((^prefix_final_unit_tm).cu_context.ctx_functions)``;
val prefix_sue_fn_tm = prefix_normal_tm
  ``HD ((^prefix_sue_unit_tm).cu_context.ctx_functions)``;
val prefix_fmp_fn_tm = prefix_normal_tm
  ``HD ((^prefix_fmp_unit_tm).cu_context.ctx_functions)``;
val prefix_rp_tm = prefix_normal_tm
  ``THE (resolve_o1_policy (o1_policy all_capabilities))``;

Theorem deploy_prefix_negative_fold9:
  venomFnScheduleRunner$run_configured_fn_pass_fold
    venomPassDispatcher$execute_configured_fn_pass ^prefix_rp_tm []
    ^prefix_pre_unit_tm ^prefix_final_supply_tm ^prefix_final_fn_tm [] =
    SOME (^prefix_final_fn_tm, [], ^prefix_final_supply_tm)
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_negative_fold8:
  venomFnScheduleRunner$run_configured_fn_pass_fold
    venomPassDispatcher$execute_configured_fn_pass ^prefix_rp_tm
    [CFP_Simple VP_CFGNormalization]
    ^prefix_pre_unit_tm ^prefix_final_supply_tm ^prefix_final_fn_tm [] =
    SOME (^prefix_final_fn_tm, [], ^prefix_final_supply_tm)
Proof
  once_rewrite_tac[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomFnScheduleRunner$run_configured_fn_pass_fold``]) >>
  pure_rewrite_tac[deploy_prefix_negative_fold9] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_fold7:
  venomFnScheduleRunner$run_configured_fn_pass_fold
    venomPassDispatcher$execute_configured_fn_pass ^prefix_rp_tm
    [CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]
    ^prefix_pre_unit_tm ^prefix_final_supply_tm ^prefix_sue_fn_tm [] =
    SOME (^prefix_final_fn_tm, [], ^prefix_final_supply_tm)
Proof
  once_rewrite_tac[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomFnScheduleRunner$run_configured_fn_pass_fold``]) >>
  pure_rewrite_tac[deploy_prefix_negative_fold8] >> EVAL_TAC
QED

val prefix_tail6_tm = ``[CFP_Simple VP_SingleUseExpansion;
  CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]``;
val prefix_dload_supply_norm_tm = prefix_normal_tm prefix_dload_supply_tm;

Theorem deploy_prefix_negative_fold6:
  venomFnScheduleRunner$run_configured_fn_pass_fold
    venomPassDispatcher$execute_configured_fn_pass ^prefix_rp_tm ^prefix_tail6_tm
    ^prefix_pre_unit_tm ^prefix_dload_supply_norm_tm ^prefix_fmp_fn_tm [] =
    SOME (^prefix_final_fn_tm, [], ^prefix_final_supply_tm)
Proof
  once_rewrite_tac[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomFnScheduleRunner$run_configured_fn_pass_fold``]) >>
  pure_rewrite_tac[deploy_prefix_negative_fold7] >> EVAL_TAC
QED

val prefix_tail5_tm = ``CFP_Simple VP_SimplifyCFG :: ^prefix_tail6_tm``;

Theorem deploy_prefix_negative_fold5:
  venomFnScheduleRunner$run_configured_fn_pass_fold
    venomPassDispatcher$execute_configured_fn_pass ^prefix_rp_tm ^prefix_tail5_tm
    ^prefix_pre_unit_tm ^prefix_dload_supply_norm_tm ^prefix_fmp_fn_tm [] =
    SOME (^prefix_final_fn_tm, [], ^prefix_final_supply_tm)
Proof
  once_rewrite_tac[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomFnScheduleRunner$run_configured_fn_pass_fold``]) >>
  pure_rewrite_tac[deploy_prefix_negative_fold6] >> EVAL_TAC
QED

val prefix_tail4_tm = ``CFP_Simple VP_MakeSSA :: ^prefix_tail5_tm``;

Theorem deploy_prefix_negative_fold4:
  venomFnScheduleRunner$run_configured_fn_pass_fold
    venomPassDispatcher$execute_configured_fn_pass ^prefix_rp_tm ^prefix_tail4_tm
    ^prefix_pre_unit_tm ^prefix_dload_supply_norm_tm ^prefix_fmp_fn_tm [] =
    SOME (^prefix_final_fn_tm, [], ^prefix_final_supply_tm)
Proof
  once_rewrite_tac[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomFnScheduleRunner$run_configured_fn_pass_fold``]) >>
  pure_rewrite_tac[deploy_prefix_negative_fold5] >> EVAL_TAC
QED

val prefix_tail3_tm = ``CFP_Simple VP_FmpLowering :: ^prefix_tail4_tm``;
val prefix_concrete_fn_norm_tm = prefix_normal_tm prefix_concrete_fn_tm;

Theorem deploy_prefix_negative_fold3:
  venomFnScheduleRunner$run_configured_fn_pass_fold
    venomPassDispatcher$execute_configured_fn_pass ^prefix_rp_tm ^prefix_tail3_tm
    ^prefix_pre_unit_tm ^prefix_dload_supply_norm_tm ^prefix_concrete_fn_norm_tm [] =
    SOME (^prefix_final_fn_tm, [], ^prefix_final_supply_tm)
Proof
  once_rewrite_tac[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomFnScheduleRunner$run_configured_fn_pass_fold``]) >>
  pure_rewrite_tac[deploy_prefix_negative_fold4] >> EVAL_TAC
QED

val prefix_tail2_tm = ``CFP_Simple VP_ConcretizeMemLoc :: ^prefix_tail3_tm``;
val prefix_dload_fn_norm_tm = prefix_normal_tm prefix_dload_fn_tm;

Theorem deploy_prefix_negative_fold2:
  venomFnScheduleRunner$run_configured_fn_pass_fold
    venomPassDispatcher$execute_configured_fn_pass ^prefix_rp_tm ^prefix_tail2_tm
    ^prefix_pre_unit_tm ^prefix_dload_supply_norm_tm ^prefix_dload_fn_norm_tm [] =
    SOME (^prefix_final_fn_tm, [], ^prefix_final_supply_tm)
Proof
  once_rewrite_tac[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomFnScheduleRunner$run_configured_fn_pass_fold``,
     ``concretizeMemLocDefs$concretize_function_fuel_in_context``]) >>
  pure_rewrite_tac[deploy_prefix_negative_concrete_fn_artifact |>
    CONV_RULE (LAND_CONV (computeLib.RESTR_EVAL_CONV
      [``concretizeMemLocDefs$concretize_function_fuel_in_context``]))] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomFnScheduleRunner$run_configured_fn_pass_fold``]) >>
  pure_rewrite_tac[deploy_prefix_negative_fold3] >> EVAL_TAC
QED

val prefix_tail1_tm = ``CFP_Simple VP_LowerDload :: ^prefix_tail2_tm``;
val prefix_pre_fn_tm = prefix_normal_tm
  ``HD ((^prefix_pre_unit_tm).cu_context.ctx_functions)``;

Theorem deploy_prefix_negative_fold1:
  venomFnScheduleRunner$run_configured_fn_pass_fold
    venomPassDispatcher$execute_configured_fn_pass ^prefix_rp_tm ^prefix_tail1_tm
    ^prefix_pre_unit_tm ^prefix_pre_supply_tm ^prefix_pre_fn_tm [] =
    SOME (^prefix_final_fn_tm, [], ^prefix_final_supply_tm)
Proof
  once_rewrite_tac[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomFnScheduleRunner$run_configured_fn_pass_fold``]) >>
  pure_rewrite_tac[deploy_prefix_negative_fold2] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_fold0:
  venomFnScheduleRunner$run_configured_fn_pass_fold
    venomPassDispatcher$execute_configured_fn_pass ^prefix_rp_tm
    (CFP_Simple VP_MakeSSA :: ^prefix_tail1_tm)
    ^prefix_pre_unit_tm ^prefix_pre_supply_tm ^prefix_pre_fn_tm [] =
    SOME (^prefix_final_fn_tm, [], ^prefix_final_supply_tm)
Proof
  once_rewrite_tac[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomFnScheduleRunner$run_configured_fn_pass_fold``]) >>
  pure_rewrite_tac[deploy_prefix_negative_fold1] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_named_walk:
  venomPipelineRunner$run_named_fn_schedules
    venomPassDispatcher$execute_configured_fn_pass ^prefix_rp_tm
    venomPassSchedule$o1_fn_passes ["__deploy"]
    ^prefix_pre_unit_tm ^prefix_pre_supply_tm =
    SOME (^prefix_final_unit_tm, ^prefix_final_supply_tm)
Proof
  rewrite_tac[venomPipelineRunnerTheory.run_named_fn_schedules_def,
              venomFnScheduleRunnerTheory.run_configured_fn_passes_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomFnScheduleRunner$run_configured_fn_pass_fold``]) >>
  pure_rewrite_tac[deploy_prefix_negative_fold0] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_walk_artifact:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  let unit = THE (lower_vyper_deploy_unit tops rp []) in
  let (pre,supply) = THE (venomPipelineRunner$run_pipeline_stages rp
    venomPassSchedule$o1_pipeline_spec.ps_pre_walk_stages unit
    (irSupply$init_ir_supply unit)) in
  venomPipelineRunner$run_named_fn_schedules
    venomPassDispatcher$execute_configured_fn_pass rp
    venomPassSchedule$o1_fn_passes ["__deploy"] pre supply =
    SOME (^prefix_final_unit_tm, ^prefix_final_supply_tm)
Proof
  simp_tac bool_ss [LET_THM] >>
  pure_rewrite_tac[deploy_prefix_negative_prewalk_artifact |>
                    SIMP_RULE bool_ss [LET_THM]] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomPipelineRunner$run_named_fn_schedules``,
     ``venomPassSchedule$o1_fn_passes``]) >>
  pure_rewrite_tac[deploy_prefix_negative_named_walk] >> REFL_TAC
QED

Theorem deploy_prefix_negative_pipeline_artifact:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let rp = THE (resolve_o1_policy (o1_policy all_capabilities)) in
  o1PipelineCorrect$o1_pipeline rp (THE (lower_vyper_deploy_unit tops rp [])) =
    SOME <|po_unit := ^prefix_final_unit_tm; po_final_assembly := FAP_Optimize|>
Proof
  simp_tac bool_ss [LET_THM, o1PipelineCorrectTheory.o1_pipeline_def,
    venomPipelineDriverTheory.run_venom_pipeline_def] >>
  pure_rewrite_tac[deploy_prefix_negative_unit_wf_probe |>
                    SIMP_RULE bool_ss [LET_THM],
                  deploy_prefix_negative_static_probe |>
                    SIMP_RULE bool_ss [LET_THM],
                  deploy_prefix_negative_prewalk_artifact |>
                    SIMP_RULE bool_ss [LET_THM]] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``venomPipelineRunner$run_named_fn_schedules``,
     ``venomFnScheduleRunner$run_configured_fn_passes``,
     ``venomPassSchedule$o1_fn_passes``]) >>
  pure_rewrite_tac[deploy_prefix_negative_named_walk] >>
  EVAL_TAC >>
  simp[venomInstTheory.fn_insts_blocks_def,
       venomWfTheory.bb_well_formed_compute, venomWfTheory.inst_wf_def,
       venomInstTheory.is_terminator_def, venomStateTheory.get_label_def,
       venomInstTheory.fn_labels_def, wordsTheory.dimword_def] >> EVAL_TAC
QED

val prefix_plan_ctx_tm = ``(^prefix_final_unit_tm).cu_context``;
val prefix_plan_fcg_tm = ``fcgDefs$fcg_analyze ^prefix_plan_ctx_tm``;
val prefix_plan_init_tm = ``stackPlanGen$init_cleanup_plan_state
  (stackPlanGen$cleanup_caller_height 1 ^prefix_plan_ctx_tm ^prefix_plan_fcg_tm "__deploy")
  (stackPlanGen$cleanup_growth_table ^prefix_plan_ctx_tm ^prefix_plan_fcg_tm) 32 0``;
val prefix_plan_dfg_tm = ``dfgDefs$dfg_build_function ^prefix_final_fn_tm``;

Theorem deploy_prefix_negative_emit_first:
  !live. stackPlanGen$emit_input_plan ASSIGN [Lit 32w] live ^prefix_plan_init_tm =
    ([SOPush (Lit 32w)], ^prefix_plan_init_tm with ps_stack := [Lit 32w])
Proof
  gen_tac >> EVAL_TAC
QED

Theorem deploy_prefix_negative_reorder_first:
  stackPlanOps$reorder_plan ^prefix_plan_dfg_tm [Lit 32w]
    (^prefix_plan_init_tm with ps_stack := [Lit 32w]) =
    ([], ^prefix_plan_init_tm with ps_stack := [Lit 32w])
Proof
  EVAL_TAC
QED
val prefix_plan_live_tm = ``livenessDefs$liveness_analyze ^prefix_final_fn_tm``;
val prefix_plan_cfg_tm = ``cfgDefs$cfg_analyze ^prefix_final_fn_tm``;
val prefix_plan_after_first_tm = ``^prefix_plan_init_tm with ps_stack := [Var "formal_var_4"]``;

Theorem deploy_prefix_release_empty_spills[local]:
  !next_liveness ps. ps.ps_spilled = FEMPTY ==>
    stackPlanOps$release_dead_spills next_liveness ps = ps
Proof
  rpt strip_tac >>
  simp[stackPlanOpsTheory.release_dead_spills_def,
       alistTheory.fmap_to_alist_FEMPTY]
QED

val prefix_plan_release_restr_conv = computeLib.RESTR_EVAL_CONV
  [``stackPlanOps$release_dead_spills``];

val prefix_release_const = ``stackPlanOps$release_dead_spills``;
val prefix_plan_rules = List.concat (List.concat (map
  (fn (_,xs) => map (fn clauses.RRules ths => ths
                      | clauses.Conversion _ => []) xs)
  (computeLib.listItems (computeLib.the_compset ()))));
val prefix_plan_cs = wordsLib.add_words_compset true
  (computeLib.copy (computeLib.the_compset ()));
val prefix_plan_cs = computeLib.scrub_const prefix_plan_cs prefix_release_const;
fun prefix_release_elim_conv tm =
  let
    val norm = RAND_CONV computeLib.EVAL_CONV tm
    val ntm = rhs (concl norm)
    val elim = SIMP_CONV (srw_ss()) [deploy_prefix_release_empty_spills] ntm
  in
    if aconv (rhs (concl elim)) (rand ntm) then TRANS norm elim
    else raise Fail "prefix_release_elim_conv: release did not eliminate to state"
  end;
val prefix_plan_cs = computeLib.add_conv
  (prefix_release_const, 2, prefix_release_elim_conv) prefix_plan_cs;
fun prefix_reinstall_callers heads rules cs =
  let fun depends th =
        let val (_,body) = strip_forall (concl th)
            val (_,r) = dest_eq body
        in List.exists (fn h => can (find_term (same_const h)) r) heads end
      val (callers,rest) = List.partition depends rules
      val new_heads = map (fn th => th |> concl |> strip_forall |> snd |>
        dest_eq |> fst |> strip_comb |> fst) callers
  in if null callers then cs
     else prefix_reinstall_callers new_heads rest
            (computeLib.add_thms callers cs)
  end;
val prefix_plan_cs = prefix_reinstall_callers [prefix_release_const]
  prefix_plan_rules prefix_plan_cs;
val prefix_plan_eval_conv = computeLib.CBV_CONV prefix_plan_cs;

Theorem deploy_prefix_negative_first_instruction:
  stackPlanGen$generate_inst_plan ^prefix_plan_live_tm ^prefix_plan_dfg_tm
    ^prefix_plan_cfg_tm ^prefix_final_fn_tm
    (HD ^prefix_dft_insts_tm)
    (livenessDefs$live_vars_at ^prefix_plan_live_tm "__deploy" 1)
    T F "__deploy" ^prefix_plan_init_tm =
  SOME ([SOPush (Lit 32w)], ^prefix_plan_after_first_tm)
Proof
  CONV_TAC prefix_plan_eval_conv
QED

Theorem deploy_prefix_negative_emit_second:
  !live. stackPlanGen$emit_input_plan ASSIGN [Lit 0w] live ^prefix_plan_after_first_tm =
    ([SOPush (Lit 0w)], ^prefix_plan_after_first_tm with ps_stack := [Var "formal_var_4"; Lit 0w])
Proof
  gen_tac >> EVAL_TAC
QED

Theorem deploy_prefix_negative_reorder_second:
  stackPlanOps$reorder_plan ^prefix_plan_dfg_tm [Lit 0w]
    (^prefix_plan_after_first_tm with ps_stack := [Var "formal_var_4"; Lit 0w]) =
    ([], ^prefix_plan_after_first_tm with ps_stack := [Var "formal_var_4"; Lit 0w])
Proof
  EVAL_TAC
QED
val prefix_context_plan_tm = ``
  <|cp_regions :=
      [<|sr_fn_name := "__deploy"; sr_spill_base := 32; sr_spill_end := 32;
         sr_plan :=
           [SOLabel "__deploy"; SOPush (Lit 32w); SOPush (Lit 0w);
            SOPush (Lit 0w); SOEmit "ADD"; SOPushLabel "code_end";
            SOEmit "ADD"; SOPush (Lit 0w); SOSwap 1; SODup 2; SOSwap 3;
            SOSwap 2; SOEmit "CODECOPY"; SOEmit "MLOAD"; SOPush (Lit 0w);
            SOEmit "MSTORE"; SOPush (Lit 0w); SOPush (Lit 0w); SODup 1;
            SOPushLabel "runtime_begin"; SOSwap 1; SOEmit "CODECOPY";
            SOPush (Lit 0w); SOEmit "RETURN"]|>]; cp_max_static_eom := 32;
    cp_peak_spill_end := 0; cp_initial_fmp := 32|>``;

Theorem deploy_prefix_negative_context_plan:
  stackPlanGen$generate_context_plan ^prefix_plan_ctx_tm =
    SOME ^prefix_context_plan_tm
Proof
  CONV_TAC prefix_plan_eval_conv
QED

(* When the source fails before the constructor body (the value transfer
   into a non-payable constructor, the reentrancy lock), so does the unit:
   its payable check and lock come first too. *)
Theorem deploy_ctor_prefix_fail:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs exts ints fb cf.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    classify_functions tops = (exts, ints, fb, SOME cf) /\
    (!mut nr body am_c es0.
       ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) ==>
    ?fuel. !gobs.
      deploy_venom_result_rel tops runtime_bc tx
        (load_contract NONE gobs am tx [(NONE, tops)] [])
        (run_context fuel dunit.cu_context vs)
Proof
  cheat
QED
