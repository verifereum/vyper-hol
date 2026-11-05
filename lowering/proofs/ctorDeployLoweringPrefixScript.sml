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
