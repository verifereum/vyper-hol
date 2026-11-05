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

val prefix_prog_expr_tm = ``
  execute_plan (^prefix_context_plan_tm).cp_initial_fmp
    (context_plan_ops ^prefix_context_plan_tm) ++
  data_segment_asm (^prefix_final_unit_tm).cu_data_segment ++
  [AsmDataHeader "code_end"]``;
val prefix_prog_tm = ``
 [AsmLabel "__deploy"; AsmPush [32w]; AsmPush []; AsmPush []; AsmOp "ADD";
  AsmPushLabel "code_end"; AsmOp "ADD"; AsmPush []; AsmOp "SWAP1";
  AsmOp "DUP2"; AsmOp "SWAP3"; AsmOp "SWAP2"; AsmOp "CODECOPY"; AsmOp "MLOAD";
  AsmPush []; AsmOp "MSTORE"; AsmPush []; AsmPush []; AsmOp "DUP1";
  AsmPushLabel "runtime_begin"; AsmOp "SWAP1"; AsmOp "CODECOPY"; AsmPush [];
  AsmOp "RETURN"; AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT";
  AsmDataHeader "runtime_begin"; AsmDataItem []; AsmDataHeader "code_end"]``;

Theorem deploy_prefix_negative_codegen:
  codegen_assembly ^prefix_rp_tm ^prefix_final_unit_tm = SOME ^prefix_prog_tm
Proof
  rewrite_tac[codegenTheory.codegen_assembly_def] >>
  pure_rewrite_tac[deploy_prefix_negative_context_plan] >>
  EVAL_TAC
QED

Theorem deploy_prefix_negative_assembly_safe:
  assembly_target_safe (^prefix_rp_tm).rpol_target ^prefix_prog_tm
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_negative_assembly_shape:
  ^prefix_prog_tm = ^prefix_prog_expr_tm
Proof
  EVAL_TAC
QED

val prefix_deploy_bc_tm = rhs (concl (computeLib.EVAL_CONV ``assemble ^prefix_prog_tm``));

Theorem deploy_prefix_negative_assembled:
  assemble ^prefix_prog_tm = ^prefix_deploy_bc_tm
Proof
  EVAL_TAC
QED

val prefix_lower_unit_tm = deploy_prefix_negative_lowered_artifact |>
  SIMP_RULE bool_ss [LET_THM] |> concl |> rhs |> rand;

Theorem deploy_prefix_negative_resolve:
  resolve_o1_policy (o1_policy all_capabilities) = SOME ^prefix_rp_tm
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_negative_phases:
  deploy_phases (o1_policy all_capabilities)
    [FunctionDecl Deploy Payable F F "__init__"
      [("x", BaseT (UintT 256))] [] NoneT []]
    (^prefix_deploy_bc_tm, [])
    (^prefix_rp_tm, ^prefix_lower_unit_tm,
     <|po_unit := ^prefix_final_unit_tm; po_final_assembly := FAP_Optimize|>,
     ^prefix_prog_tm, ^prefix_context_plan_tm)
Proof
  rewrite_tac[ctorDeployDefsTheory.deploy_phases_def] >>
  pure_rewrite_tac[deploy_prefix_negative_resolve,
    deploy_prefix_negative_lowered_artifact |>
      SIMP_RULE bool_ss [LET_THM, optionTheory.THE_DEF, deploy_prefix_negative_resolve],
    deploy_prefix_negative_pipeline_artifact |>
      SIMP_RULE bool_ss [LET_THM, optionTheory.THE_DEF, deploy_prefix_negative_resolve,
        deploy_prefix_negative_lowered_artifact |>
          SIMP_RULE bool_ss [LET_THM, optionTheory.THE_DEF, deploy_prefix_negative_resolve]]] >>
  simp_tac (srw_ss()) [deploy_prefix_negative_codegen,
    deploy_prefix_negative_context_plan |> SIMP_RULE (srw_ss()) [],
    deploy_prefix_negative_assembly_safe,
    deploy_prefix_negative_assembly_shape |> SIMP_RULE (srw_ss()) []] >>
  EVAL_TAC
QED

val prefix_tops_tm = ``[FunctionDecl Deploy Payable F F "__init__"
  [("x", BaseT (UintT 256))] [] NoneT []]``;
val prefix_tx_tm = ``empty_call_txn with
  <|function_name := "__init__"; args := [IntV (-1)];
    block_number := 1; block_hashes := [0w]|>``;
val prefix_args_tm = rhs (concl (computeLib.EVAL_CONV
  ``enc (Tuple [Uint 256]) (ListV [NumV (Num (-1))])``));
val prefix_es_tm = ``
  let tx = ^prefix_tx_tm in
  let rb = make_rollback initial_machine_state.accounts
    initial_machine_state.tStorage tx.sender tx.target in
  let ctxt = vfmContext$initial_context tx.target
    (^prefix_deploy_bc_tm ++ ^prefix_args_tm) F (Code tx.target)
    (make_sub_tx tx.sender tx.target tx.value 100000 []) in
  <|contexts := [(ctxt,rb)]; rollback := rb; originalAccounts := rb.accounts;
    msdomain := Collect empty_domain;
    txParams := (<|origin := tx.origin; gasPrice := tx.gas_price;
      baseFeePerGas := tx.base_fee; baseFeePerBlobGas := tx.blob_base_fee;
      blockNumber := tx.block_number; blockTimeStamp := tx.time_stamp;
      blockCoinBase := tx.coinbase; blockGasLimit := tx.gas_limit;
      prevRandao := n2w tx.prev_randao; prevHashes := tx.block_hashes;
      blobHashes := tx.blob_hashes; chainId := tx.chain_id; authRefund := 0|>)|>``;

Theorem deploy_prefix_negative_args_encoded:
  constructor_args_encode ^prefix_tops_tm ^prefix_tx_tm ^prefix_args_tm
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem deploy_prefix_negative_tx_env:
  tx_env_ok ^prefix_tx_tm
Proof
  EVAL_TAC
QED

Theorem deploy_prefix_negative_source_ready:
  deploy_source_ok ^prefix_tops_tm initial_machine_state ^prefix_tx_tm /\
  (!gobs. load_contract NONE gobs initial_machine_state ^prefix_tx_tm
     [(NONE,^prefix_tops_tm)] [] = INR (Error (RuntimeError "call bind_arguments")))
Proof
  EVAL_TAC >>
  simp[vyperStateTheory.find_var_decl_by_name_def,
       supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
       vyperStateTheory.raise_def, COND_RAND, COND_RATOR]
QED


val prefix_ctxt_tm = ``vfmContext$initial_context (^prefix_tx_tm).target
  (^prefix_deploy_bc_tm ++ ^prefix_args_tm) F (Code (^prefix_tx_tm).target)
  (make_sub_tx (^prefix_tx_tm).sender (^prefix_tx_tm).target
     (^prefix_tx_tm).value 100000 [])``;

Theorem deploy_prefix_negative_context_projections:
  (^prefix_ctxt_tm).pc = 0 /\ (^prefix_ctxt_tm).stack = [] /\
  (^prefix_ctxt_tm).memory = empty_buffer /\
  (^prefix_ctxt_tm).msgParams.parsed =
    parse_code 0 FEMPTY (^prefix_deploy_bc_tm ++ ^prefix_args_tm)
Proof
  simp[vfmContextTheory.initial_context_simp,
       vfmContextTheory.initial_msg_params_def]
QED

Theorem deploy_prefix_parse_empty_diagnostic[local]:
  parse_code 0 FEMPTY [] = parse_code 0 FEMPTY []
Proof
  CONV_TAC (LAND_CONV computeLib.EVAL_CONV) >>
  goal_term (fn tm => (print (term_to_string tm ^ "\n"); all_tac)) >>
  CONV_TAC (RHS_CONV computeLib.EVAL_CONV) >> REFL_TAC
QED

Theorem deploy_prefix_empty_buffer_diagnostic[local]:
  empty_buffer = empty_buffer
Proof
  CONV_TAC (LAND_CONV computeLib.EVAL_CONV) >>
  goal_term (fn tm => (print (term_to_string tm ^ "\n"); all_tac)) >>
  CONV_TAC (RHS_CONV computeLib.EVAL_CONV) >> REFL_TAC
QED

Theorem deploy_prefix_buffer_list_diagnostic[local]:
  buffer_of_list [] = buffer_of_list []
Proof
  CONV_TAC (LAND_CONV computeLib.EVAL_CONV) >>
  goal_term (fn tm => (print (term_to_string tm ^ "\n"); all_tac)) >>
  CONV_TAC (RHS_CONV computeLib.EVAL_CONV) >> REFL_TAC
QED

Theorem deploy_prefix_domain_diagnostic[local]:
  Collect empty_domain = Collect empty_domain
Proof
  CONV_TAC (LAND_CONV computeLib.EVAL_CONV) >>
  goal_term (fn tm => (print (term_to_string tm ^ "\n"); all_tac)) >>
  CONV_TAC (RHS_CONV computeLib.EVAL_CONV) >> REFL_TAC
QED

Theorem deploy_prefix_short_parse:
  parse_code 0 FEMPTY [91w;96w;32w] =
    FEMPTY |+ (0, JumpDest) |+ (1, Push 1 [32w])
Proof
  simp[Once vfmContextTheory.parse_code_def, vfmOperationTheory.parse_opcode_cond_thm,
       vfmOperationTheory.opcode_def, wordsTheory.dimword_8] >>
  simp[Once vfmContextTheory.parse_code_def, vfmOperationTheory.parse_opcode_cond_thm,
       vfmOperationTheory.opcode_def, wordsTheory.dimword_8] >>
  simp[Once vfmContextTheory.parse_code_def] >> EVAL_TAC
QED

val prefix_parse_unfold_tac = CONV_TAC
  (LAND_CONV (ONCE_REWRITE_CONV [vfmContextTheory.parse_code_def]));
val prefix_parse_reduce_tac = CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
  [vfmOperationTheory.parse_opcode_cond_thm,
   vfmOperationTheory.opcode_def, wordsTheory.dimword_8]));
val prefix_parse_let_tac = CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
  [LET_THM, vfmOperationTheory.opcode_def, wordsTheory.dimword_8]));

Theorem deploy_prefix_parse_prefix:
  parse_code 0 FEMPTY (^prefix_deploy_bc_tm ++ ^prefix_args_tm) =
  parse_code 11
    (FEMPTY |+ (0, JumpDest) |+ (1, Push 1 [32w]) |+ (3, Push 0 [])
      |+ (4, Push 0 []) |+ (5, Add) |+ (6, Push 2 [0w;33w])
      |+ (9, Add) |+ (10, Push 0 []))
    (DROP 11 (^prefix_deploy_bc_tm ++ ^prefix_args_tm))
Proof
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``parse_code``])
QED

Theorem deploy_prefix_parse_middle:
  parse_code 11 m (DROP 11 (^prefix_deploy_bc_tm ++ ^prefix_args_tm)) =
  parse_code 21
    (m |+ (11, Swap 0) |+ (12, Dup 1) |+ (13, Swap 2) |+ (14, Swap 1)
       |+ (15, CodeCopy) |+ (16, MLoad) |+ (17, Push 0 []) |+ (18, MStore)
       |+ (19, Push 0 []) |+ (20, Push 0 []))
    (DROP 21 (^prefix_deploy_bc_tm ++ ^prefix_args_tm))
Proof
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``parse_code``])
QED

Theorem deploy_prefix_parse_end:
  parse_code 21 m (DROP 21 (^prefix_deploy_bc_tm ++ ^prefix_args_tm)) =
  parse_code 33
    (m |+ (21, Dup 0) |+ (22, Push 2 [0w;33w]) |+ (25, Swap 0)
       |+ (26, CodeCopy) |+ (27, Push 0 []) |+ (28, Return)
       |+ (29, JumpDest) |+ (30, Push 0 []) |+ (31, Dup 0) |+ (32, Revert))
    (DROP 33 (^prefix_deploy_bc_tm ++ ^prefix_args_tm))
Proof
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``parse_code``])
QED

Theorem deploy_prefix_parse_args:
  parse_code 33 m (DROP 33 (^prefix_deploy_bc_tm ++ ^prefix_args_tm)) =
    m |+ (33, Stop) |+ (34, Stop) |+ (35, Stop) |+ (36, Stop)
      |+ (37, Stop) |+ (38, Stop) |+ (39, Stop) |+ (40, Stop)
      |+ (41, Stop) |+ (42, Stop) |+ (43, Stop) |+ (44, Stop)
      |+ (45, Stop) |+ (46, Stop) |+ (47, Stop) |+ (48, Stop)
      |+ (49, Stop) |+ (50, Stop) |+ (51, Stop) |+ (52, Stop)
      |+ (53, Stop) |+ (54, Stop) |+ (55, Stop) |+ (56, Stop)
      |+ (57, Stop) |+ (58, Stop) |+ (59, Stop) |+ (60, Stop)
      |+ (61, Stop) |+ (62, Stop) |+ (63, Stop) |+ (64, Add)
Proof
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >> prefix_parse_let_tac >>
  prefix_parse_unfold_tac >> prefix_parse_reduce_tac >>
  REFL_TAC
QED

val prefix_parsed_tm = ``
  FEMPTY |+ (0, JumpDest) |+ (1, Push 1 [32w]) |+ (3, Push 0 [])
    |+ (4, Push 0 []) |+ (5, Add) |+ (6, Push 2 [0w;33w])
    |+ (9, Add) |+ (10, Push 0 [])
    |+ (11, Swap 0) |+ (12, Dup 1) |+ (13, Swap 2) |+ (14, Swap 1)
    |+ (15, CodeCopy) |+ (16, MLoad) |+ (17, Push 0 []) |+ (18, MStore)
    |+ (19, Push 0 []) |+ (20, Push 0 [])
    |+ (21, Dup 0) |+ (22, Push 2 [0w;33w]) |+ (25, Swap 0)
    |+ (26, CodeCopy) |+ (27, Push 0 []) |+ (28, Return)
    |+ (29, JumpDest) |+ (30, Push 0 []) |+ (31, Dup 0) |+ (32, Revert)
    |+ (33, Stop) |+ (34, Stop) |+ (35, Stop) |+ (36, Stop)
    |+ (37, Stop) |+ (38, Stop) |+ (39, Stop) |+ (40, Stop)
    |+ (41, Stop) |+ (42, Stop) |+ (43, Stop) |+ (44, Stop)
    |+ (45, Stop) |+ (46, Stop) |+ (47, Stop) |+ (48, Stop)
    |+ (49, Stop) |+ (50, Stop) |+ (51, Stop) |+ (52, Stop)
    |+ (53, Stop) |+ (54, Stop) |+ (55, Stop) |+ (56, Stop)
    |+ (57, Stop) |+ (58, Stop) |+ (59, Stop) |+ (60, Stop)
    |+ (61, Stop) |+ (62, Stop) |+ (63, Stop) |+ (64, Add)``;

Theorem deploy_prefix_negative_parsed:
  parse_code 0 FEMPTY (^prefix_deploy_bc_tm ++ ^prefix_args_tm) =
  ^prefix_parsed_tm
Proof
  rewrite_tac[deploy_prefix_parse_prefix, deploy_prefix_parse_middle,
              deploy_prefix_parse_end, deploy_prefix_parse_args]
QED

Theorem deploy_prefix_negative_first_step:
  FST (step ^prefix_es_tm) = INL ()
Proof
  simp[LET_THM, vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def, deploy_prefix_negative_parsed] >>
  EVAL_TAC
QED

val prefix_es1_tm = ``(^prefix_es_tm) with contexts :=
  MAP (\(ctxt,rb). (ctxt with <|pc := 1; gasUsed := 1|>,rb))
    (^prefix_es_tm).contexts``;

Theorem deploy_prefix_negative_step1:
  step ^prefix_es_tm = (INL (), ^prefix_es1_tm)
Proof
  simp[LET_THM, vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def, deploy_prefix_negative_parsed] >>
  EVAL_TAC
QED

Theorem deploy_prefix_negative_observe1:
  observe 1 ^prefix_es_tm (INL (), ^prefix_es1_tm)
    <|entries := []; readings := []; pending := NONE|> =
    <|entries := []; readings := []; pending := NONE|>
Proof
  simp[callTraceTheory.observe_def, callTraceTheory.observable_call_def,
       LET_THM, vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def, deploy_prefix_negative_parsed] >>
  EVAL_TAC
QED

Theorem deploy_prefix_negative_step1_continues:
  LENGTH (^prefix_es1_tm).contexts = 1
Proof
  simp[LET_THM]
QED

val prefix_es2_tm = ``(^prefix_es_tm) with contexts :=
  MAP (\(ctxt,rb). (ctxt with <|pc := 3; gasUsed := 4; stack := [32w]|>,rb))
    (^prefix_es_tm).contexts``;

Theorem deploy_prefix_negative_step2:
  step ^prefix_es1_tm = (INL (), ^prefix_es2_tm)
Proof
  simp[LET_THM, vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def, deploy_prefix_negative_parsed] >>
  EVAL_TAC >> simp[byteTheory.set_byte_bit_field_insert] >> EVAL_TAC
QED

fun prefix_stack_state_tm (pc, gas, stack) =
  ``(^prefix_es_tm) with contexts :=
    MAP (\(ctxt,rb). (ctxt with <|pc := ^pc; gasUsed := ^gas; stack := ^stack|>,rb))
      (^prefix_es_tm).contexts``;
val prefix_step_eval_tac =
  simp[LET_THM, vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def, deploy_prefix_negative_parsed] >>
  EVAL_TAC >> simp[byteTheory.set_byte_bit_field_insert] >> EVAL_TAC;

val prefix_es3_tm = prefix_stack_state_tm (``4:num``, ``6:num``, ``[0w;32w]:256 word list``);
val prefix_es4_tm = prefix_stack_state_tm (``5:num``, ``8:num``, ``[0w;0w;32w]:256 word list``);
val prefix_es5_tm = prefix_stack_state_tm (``6:num``, ``11:num``, ``[0w;32w]:256 word list``);
val prefix_es6_tm = prefix_stack_state_tm (``9:num``, ``14:num``, ``[33w;0w;32w]:256 word list``);
val prefix_es7_tm = prefix_stack_state_tm (``10:num``, ``17:num``, ``[33w;32w]:256 word list``);
val prefix_es8_tm = prefix_stack_state_tm (``11:num``, ``19:num``, ``[0w;33w;32w]:256 word list``);

Theorem deploy_prefix_negative_step3:
  step ^prefix_es2_tm = (INL (), ^prefix_es3_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step4:
  step ^prefix_es3_tm = (INL (), ^prefix_es4_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step5:
  step ^prefix_es4_tm = (INL (), ^prefix_es5_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step6:
  step ^prefix_es5_tm = (INL (), ^prefix_es6_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step7:
  step ^prefix_es6_tm = (INL (), ^prefix_es7_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step8:
  step ^prefix_es7_tm = (INL (), ^prefix_es8_tm)
Proof
  prefix_step_eval_tac
QED

val prefix_es9_tm = prefix_stack_state_tm (``12:num``, ``22:num``, ``[33w;0w;32w]:256 word list``);
val prefix_es10_tm = prefix_stack_state_tm (``13:num``, ``25:num``, ``[0w;33w;0w;32w]:256 word list``);
val prefix_es11_tm = prefix_stack_state_tm (``14:num``, ``28:num``, ``[32w;33w;0w;0w]:256 word list``);
val prefix_es12_tm = prefix_stack_state_tm (``15:num``, ``31:num``, ``[0w;33w;32w;0w]:256 word list``);

Theorem deploy_prefix_negative_step9:
  step ^prefix_es8_tm = (INL (), ^prefix_es9_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step10:
  step ^prefix_es9_tm = (INL (), ^prefix_es10_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step11:
  step ^prefix_es10_tm = (INL (), ^prefix_es11_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step12:
  step ^prefix_es11_tm = (INL (), ^prefix_es12_tm)
Proof
  prefix_step_eval_tac
QED

fun prefix_mem_state_tm (pc, gas, stack) =
  let val es = prefix_stack_state_tm (pc, gas, stack) in
    ``^es with contexts := MAP
      (\(ctxt,rb). (ctxt with memory := buffer_of_list ^prefix_args_tm,rb))
      (^es).contexts``
  end;
val prefix_es13_tm = prefix_mem_state_tm (``16:num``, ``40:num``, ``[0w]:256 word list``);

Theorem deploy_prefix_negative_step13:
  step ^prefix_es12_tm = (INL (), ^prefix_es13_tm)
Proof
  prefix_step_eval_tac
QED

val prefix_es14_tm = prefix_mem_state_tm (``17:num``, ``43:num``, ``[1w]:256 word list``);
val prefix_es15_tm = prefix_mem_state_tm (``18:num``, ``45:num``, ``[0w;1w]:256 word list``);
val prefix_es16_tm = prefix_mem_state_tm (``19:num``, ``48:num``, ``[]:256 word list``);
val prefix_es17_tm = prefix_mem_state_tm (``20:num``, ``50:num``, ``[0w]:256 word list``);
val prefix_es18_tm = prefix_mem_state_tm (``21:num``, ``52:num``, ``[0w;0w]:256 word list``);
val prefix_es19_tm = prefix_mem_state_tm (``22:num``, ``55:num``, ``[0w;0w;0w]:256 word list``);
val prefix_es20_tm = prefix_mem_state_tm (``25:num``, ``58:num``, ``[33w;0w;0w;0w]:256 word list``);
val prefix_es21_tm = prefix_mem_state_tm (``26:num``, ``61:num``, ``[0w;33w;0w;0w]:256 word list``);
val prefix_es22_tm = prefix_mem_state_tm (``27:num``, ``64:num``, ``[0w]:256 word list``);
val prefix_es23_tm = prefix_mem_state_tm (``28:num``, ``66:num``, ``[0w;0w]:256 word list``);

Theorem deploy_prefix_negative_step14:
  step ^prefix_es13_tm = (INL (), ^prefix_es14_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step15:
  step ^prefix_es14_tm = (INL (), ^prefix_es15_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step16:
  step ^prefix_es15_tm = (INL (), ^prefix_es16_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step17:
  step ^prefix_es16_tm = (INL (), ^prefix_es17_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step18:
  step ^prefix_es17_tm = (INL (), ^prefix_es18_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step19:
  step ^prefix_es18_tm = (INL (), ^prefix_es19_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step20:
  step ^prefix_es19_tm = (INL (), ^prefix_es20_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step21:
  step ^prefix_es20_tm = (INL (), ^prefix_es21_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step22:
  step ^prefix_es21_tm = (INL (), ^prefix_es22_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_step23:
  step ^prefix_es22_tm = (INL (), ^prefix_es23_tm)
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_negative_terminal:
  FST (step ^prefix_es23_tm) = INR NONE
Proof
  prefix_step_eval_tac
QED

Theorem deploy_prefix_observe_noncall[local]:
  ~observable_call (FST (HD es.contexts)) /\
  next_opcode (FST (HD es.contexts)) <> SOME Gas ==>
  observe d es (r,post) <|entries := []; readings := []; pending := NONE|> =
    <|entries := []; readings := []; pending := NONE|>
Proof
  simp[callTraceTheory.observe_def]
QED

Theorem deploy_prefix_noncall_opcode[local]:
  next_opcode c <> SOME Call /\ next_opcode c <> SOME StaticCall /\
  next_opcode c <> SOME Create /\ next_opcode c <> SOME Create2 ==>
  ~observable_call c
Proof
  simp[callTraceTheory.observable_call_def]
QED

Theorem deploy_prefix_negative_code_projection[local]:
  (^prefix_ctxt_tm).msgParams.code = ^prefix_deploy_bc_tm ++ ^prefix_args_tm
Proof
  simp[vfmContextTheory.initial_context_simp,
       vfmContextTheory.initial_msg_params_def]
QED

Theorem deploy_prefix_negative_parsed_projection[local]:
  (^prefix_ctxt_tm).msgParams.parsed = ^prefix_parsed_tm
Proof
  simp[deploy_prefix_negative_context_projections, deploy_prefix_negative_parsed]
QED

Theorem deploy_prefix_next_opcode_update[local]:
  next_opcode (c with <|pc := pc; stack := stk; gasUsed := gas; memory := mem|>) =
  if LENGTH c.msgParams.code <= pc then SOME Stop else FLOOKUP c.msgParams.parsed pc
Proof
  simp[callTraceTheory.next_opcode_def]
QED

Theorem deploy_prefix_negative_next_opcode[local]:
  next_opcode
    (^prefix_ctxt_tm with <|pc := pc; stack := stk; gasUsed := gas; memory := mem|>) =
  if 65 <= pc then SOME Stop else FLOOKUP ^prefix_parsed_tm pc
Proof
  pure_rewrite_tac[deploy_prefix_next_opcode_update,
       deploy_prefix_negative_code_projection, deploy_prefix_negative_parsed_projection] >>
  simp[]
QED

Theorem deploy_prefix_negative_context_observer:
  MEM pc [0;1;3;4;5;6;9;10;11;12;13;14;15;16;17;18;19;20;21;22;25;26;27;28] ==>
  ~observable_call
    (^prefix_ctxt_tm with <|pc := pc; stack := stk; gasUsed := gas; memory := mem|>) /\
  next_opcode
    (^prefix_ctxt_tm with <|pc := pc; stack := stk; gasUsed := gas; memory := mem|>) <> SOME Gas
Proof
  disch_tac >> conj_tac
  >- (irule deploy_prefix_noncall_opcode >>
      pure_rewrite_tac[deploy_prefix_negative_next_opcode] >>
      pop_assum mp_tac >> pure_rewrite_tac[listTheory.MEM] >>
      strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE])
  >> pure_rewrite_tac[deploy_prefix_negative_next_opcode] >>
  pop_assum mp_tac >> pure_rewrite_tac[listTheory.MEM] >>
  strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem deploy_prefix_observe_singleton[local]:
  ~observable_call c /\ next_opcode c <> SOME Gas ==>
  observe d (es with contexts := [(c,rb)]) (r,post)
    <|entries := []; readings := []; pending := NONE|> =
    <|entries := []; readings := []; pending := NONE|>
Proof
  strip_tac >> irule deploy_prefix_observe_noncall >> simp[]
QED

Theorem deploy_prefix_negative_observe_context:
  MEM pc [0;1;3;4;5;6;9;10;11;12;13;14;15;16;17;18;19;20;21;22;25;26;27;28] ==>
  observe d
    (es with contexts :=
      [(^prefix_ctxt_tm with <|pc := pc; stack := stk; gasUsed := gas; memory := mem|>, rb)])
    (r,post) <|entries := []; readings := []; pending := NONE|> =
    <|entries := []; readings := []; pending := NONE|>
Proof
  strip_tac >> irule deploy_prefix_observe_singleton >>
  irule deploy_prefix_negative_context_observer >> asm_rewrite_tac[]
QED

Theorem deploy_prefix_context_keep_memory[local]:
  c with <|pc := pc; stack := stk; gasUsed := gas; memory := c.memory|> =
  c with <|pc := pc; stack := stk; gasUsed := gas|>
Proof
  simp[vfmContextTheory.context_component_equality]
QED

Theorem deploy_prefix_negative_observe_stack:
  MEM pc [0;1;3;4;5;6;9;10;11;12;13;14;15;16;17;18;19;20;21;22;25;26;27;28] ==>
  observe d ^(prefix_stack_state_tm (``pc:num``, ``gas:num``, ``stk:256 word list``))
    (r,post) <|entries := []; readings := []; pending := NONE|> =
    <|entries := []; readings := []; pending := NONE|>
Proof
  strip_tac >> irule deploy_prefix_observe_noncall >>
  drule deploy_prefix_negative_context_observer >>
  disch_then (qspecl_then [`stk`, `(^prefix_ctxt_tm).memory`, `gas`] mp_tac) >>
  pure_rewrite_tac[deploy_prefix_context_keep_memory] >> simp[LET_THM]
QED

Theorem deploy_prefix_negative_observe_memory:
  MEM pc [0;1;3;4;5;6;9;10;11;12;13;14;15;16;17;18;19;20;21;22;25;26;27;28] ==>
  observe d ^(prefix_mem_state_tm (``pc:num``, ``gas:num``, ``stk:256 word list``))
    (r,post) <|entries := []; readings := []; pending := NONE|> =
    <|entries := []; readings := []; pending := NONE|>
Proof
  strip_tac >> irule deploy_prefix_observe_noncall >>
  drule deploy_prefix_negative_context_observer >>
  disch_then (qspecl_then [`stk`, `buffer_of_list ^prefix_args_tm`, `gas`] mp_tac) >>
  simp[LET_THM]
QED

Theorem deploy_prefix_negative_stack_depth:
  LENGTH (^(prefix_stack_state_tm (``pc:num``, ``gas:num``, ``stk:256 word list``))).contexts = 1
Proof
  simp[LET_THM]
QED

Theorem deploy_prefix_negative_memory_depth:
  LENGTH (^(prefix_mem_state_tm (``pc:num``, ``gas:num``, ``stk:256 word list``))).contexts = 1
Proof
  simp[LET_THM]
QED

Theorem deploy_prefix_negative_observe_es1:
  observe d ^prefix_es1_tm (r,post)
    <|entries := []; readings := []; pending := NONE|> =
    <|entries := []; readings := []; pending := NONE|>
Proof
  irule deploy_prefix_observe_noncall >> simp[LET_THM] >>
  simp[callTraceTheory.observable_call_def, callTraceTheory.next_opcode_def,
       vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def,
       SRULE [] deploy_prefix_negative_parsed, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem deploy_prefix_frame_exit[local]:
  FST result = INR NONE /\ observe d es result obs = obs ==>
  frame_obs_tr d obs es result = obs
Proof
  Cases_on `result` >> simp[Once callTraceTheory.frame_obs_tr_def, LET_THM] >>
  strip_tac >> gvs[]
QED

Theorem deploy_prefix_frame_advance[local]:
  LENGTH post.contexts = 1 /\ observe 1 es (INL (),post) obs = obs ==>
  frame_obs_tr 1 obs es (INL (),post) = frame_obs_tr 1 obs post (step post)
Proof
  strip_tac >> `post.contexts <> []` by (strip_tac >> gvs[]) >>
  simp[Once callTraceTheory.frame_obs_tr_def, LET_THM] >>
  gvs[callTraceTheory.observe_def]
QED

Theorem deploy_prefix_negative_frame_terminal:
  frame_obs_tr 1 <|entries := []; readings := []; pending := NONE|>
    ^prefix_es23_tm (step ^prefix_es23_tm) =
    <|entries := []; readings := []; pending := NONE|>
Proof
  irule deploy_prefix_frame_exit >>
  rewrite_tac[deploy_prefix_negative_terminal] >>
  Cases_on `step ^prefix_es23_tm` >>
  irule deploy_prefix_negative_observe_memory >> simp[]
QED


fun prefix_frame_advance_tac (step_th, depth_th, observe_th) =
  pure_rewrite_tac[step_th] >>
  dep_rewrite.DEP_REWRITE_TAC[deploy_prefix_frame_advance] >>
  conj_tac >- (conj_tac >- (irule depth_th) >> irule observe_th >> simp[]);

Theorem deploy_prefix_negative_frame_empty:
  frame_obs_tr 1 <|entries := []; readings := []; pending := NONE|>
    ^prefix_es_tm (step ^prefix_es_tm) =
    <|entries := []; readings := []; pending := NONE|>
Proof
  prefix_frame_advance_tac (deploy_prefix_negative_step1,
    deploy_prefix_negative_step1_continues, deploy_prefix_negative_observe1) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step2,
    deploy_prefix_negative_stack_depth, deploy_prefix_negative_observe_es1) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step3,
    deploy_prefix_negative_stack_depth, deploy_prefix_negative_observe_stack) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step4,
    deploy_prefix_negative_stack_depth, deploy_prefix_negative_observe_stack) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step5,
    deploy_prefix_negative_stack_depth, deploy_prefix_negative_observe_stack) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step6,
    deploy_prefix_negative_stack_depth, deploy_prefix_negative_observe_stack) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step7,
    deploy_prefix_negative_stack_depth, deploy_prefix_negative_observe_stack) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step8,
    deploy_prefix_negative_stack_depth, deploy_prefix_negative_observe_stack) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step9,
    deploy_prefix_negative_stack_depth, deploy_prefix_negative_observe_stack) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step10,
    deploy_prefix_negative_stack_depth, deploy_prefix_negative_observe_stack) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step11,
    deploy_prefix_negative_stack_depth, deploy_prefix_negative_observe_stack) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step12,
    deploy_prefix_negative_stack_depth, deploy_prefix_negative_observe_stack) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step13,
    deploy_prefix_negative_memory_depth, deploy_prefix_negative_observe_stack) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step14,
    deploy_prefix_negative_memory_depth, deploy_prefix_negative_observe_memory) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step15,
    deploy_prefix_negative_memory_depth, deploy_prefix_negative_observe_memory) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step16,
    deploy_prefix_negative_memory_depth, deploy_prefix_negative_observe_memory) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step17,
    deploy_prefix_negative_memory_depth, deploy_prefix_negative_observe_memory) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step18,
    deploy_prefix_negative_memory_depth, deploy_prefix_negative_observe_memory) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step19,
    deploy_prefix_negative_memory_depth, deploy_prefix_negative_observe_memory) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step20,
    deploy_prefix_negative_memory_depth, deploy_prefix_negative_observe_memory) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step21,
    deploy_prefix_negative_memory_depth, deploy_prefix_negative_observe_memory) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step22,
    deploy_prefix_negative_memory_depth, deploy_prefix_negative_observe_memory) >>
  prefix_frame_advance_tac (deploy_prefix_negative_step23,
    deploy_prefix_negative_memory_depth, deploy_prefix_negative_observe_memory) >>
  ACCEPT_TAC deploy_prefix_negative_frame_terminal
QED

Theorem deploy_prefix_negative_call_trace:
  call_trace ^prefix_es_tm = []
Proof
  `LENGTH (^prefix_es_tm).contexts = 1` by simp[LET_THM] >>
  pure_rewrite_tac[callTraceTheory.call_trace_def,
                   callTraceTheory.frame_obs_def] >>
  asm_rewrite_tac[deploy_prefix_negative_frame_empty] >> simp[]
QED

Theorem deploy_prefix_negative_wf_state:
  wf_state ^prefix_es_tm
Proof
  simp[vfmExecutionPropTheory.wf_state_def, LET_THM,
       vfmContextTheory.initial_context_simp,
       venomExecSemanticsTheory.make_rollback_def,
       initial_machine_state_def, empty_call_txn_def,
       vfmExecutionPropTheory.all_accounts_def,
       vfmExecutionPropTheory.stack_room_ok_def,
       vfmExecutionPropTheory.gas_stack_ok_def,
       vfmExecutionPropTheory.outputTo_consistent_stack_def] >>
  simp[vfmExecutionPropTheory.wf_accounts_def,
       vfmExecutionPropTheory.outputTo_consistent_ctx_def,
       vfmContextTheory.initial_context_simp,
       vfmContextTheory.initial_msg_params_def] >>
  EVAL_TAC >> simp[]
QED

Theorem deploy_prefix_negative_state_rel:
  deploy_state_rel ^prefix_tops_tm ^prefix_deploy_bc_tm
    initial_machine_state ^prefix_tx_tm ^prefix_es_tm
Proof
  rewrite_tac[e2eDeployDefsTheory.deploy_state_rel_def] >>
  qexistsl_tac [`^prefix_ctxt_tm`,
    `make_rollback initial_machine_state.accounts initial_machine_state.tStorage
       (^prefix_tx_tm).sender (^prefix_tx_tm).target`, `^prefix_args_tm`] >>
  simp[deploy_prefix_negative_wf_state, deploy_prefix_negative_call_trace,
       deploy_prefix_negative_args_encoded, LET_THM,
       vfmContextTheory.initial_context_simp,
       vfmContextTheory.initial_msg_params_def] >>
  EVAL_TAC >> simp[]
QED

val prefix_vs_tm = ``deploy_entry_state ^prefix_prog_tm ^prefix_context_plan_tm
  ^prefix_tops_tm ^prefix_es_tm``;

Theorem deploy_prefix_safe_step_no_abort:
  !inst s fuel ctx a ss.
    MEM inst.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN] ==>
    step_inst fuel ctx inst s <> Abort a ss
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  simp[Once venomExecSemanticsTheory.step_inst_def] >>
  pure_once_rewrite_tac[venomExecSemanticsTheory.step_inst_base_def] >>
  asm_rewrite_tac[] >>
  simp[venomExecSemanticsTheory.exec_alloca_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomExecSemanticsTheory.exec_read1_def,
       venomExecSemanticsTheory.exec_write2_def, LET_THM] >>
  simp[AllCaseEqs()]
QED

Theorem deploy_prefix_safe_exec_no_abort:
  !bb s fuel ctx a ss.
    EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
      bb.bb_instructions ==> exec_block fuel ctx bb s <> Abort a ss
Proof
  rpt gen_tac >> qid_spec_tac `s` >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> disch_tac >> disch_tac >>
  simp[Once venomExecSemanticsTheory.exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `MEM inst bb.bb_instructions /\ s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[venomInstTheory.get_instruction_def] >> simp[listTheory.EL_MEM]) >>
  `MEM inst.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN]` by
    (qpat_x_assum `EVERY _ _` mp_tac >>
     rewrite_tac[listTheory.EVERY_MEM] >>
     disch_then (qspec_then `inst` mp_tac) >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[]
  >- (Cases_on `is_terminator inst.inst_opcode` >- (Cases_on `v'.vs_halted` >> simp[]) >>
      simp[] >> first_x_assum irule >> simp[])
  >> qpat_x_assum `!y. _` kall_tac >>
  drule_all deploy_prefix_safe_step_no_abort >> metis_tac[]
QED

Theorem deploy_prefix_safe_block_no_abort:
  !bb s fuel ctx a ss.
    EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
      bb.bb_instructions ==> run_block fuel ctx bb s <> Abort a ss
Proof
  rpt gen_tac >> disch_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs >>
  simp[venomExecSemanticsTheory.run_block_def] >>
  irule deploy_prefix_safe_exec_no_abort >> simp[]
QED

Theorem deploy_prefix_lookup_block_mem[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >> simp[venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
  rw[] >> disj2_tac >> first_x_assum irule >>
  fs[venomInstTheory.lookup_block_def] >> metis_tac[]
QED

Theorem deploy_prefix_safe_blocks_no_abort:
  !fuel fn s ctx a ss.
    EVERY (\bb. EVERY (\i.
      MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
      bb.bb_instructions) fn.fn_blocks ==>
    run_blocks fuel ctx fn s <> Abort a ss
Proof
  Induct_on `fuel` >- simp[Once venomExecSemanticsTheory.run_blocks_def] >>
  rpt gen_tac >> disch_tac >>
  simp[venomExecSemanticsTheory.run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >- simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[deploy_prefix_lookup_block_mem] >>
  `EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
    bb.bb_instructions` by
    (qpat_x_assum `EVERY _ _` mp_tac >> rewrite_tac[listTheory.EVERY_MEM] >>
     disch_then (qspec_then `bb` mp_tac) >> simp[]) >>
  Cases_on `run_block fuel ctx bb s` >> simp[]
  >- (Cases_on `v.vs_halted` >> simp[] >> first_x_assum irule >> simp[])
  >> drule_all deploy_prefix_safe_block_no_abort >> metis_tac[]
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
