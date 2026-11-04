(* Shape-only checkpoint for a separately named corrected reset candidate. *)
Theory lowerDloadCorrectedProbe
Ancestors
  lowerDloadProgramProbe o1PassContract lowerDloadDefs venomInst
  venomFnScheduleRunner fcgDefs unitShapeDefs venomState unitTransformDefs
  finite_map vfmState ptrDiscipline contextCodegenRel venomExecSemantics

val _ = temp_overload_on ("corrected_helper",
  ``mk_raw_function "f" [<|bb_label := "f"; bb_instructions := [
    mk_inst 0 ALLOCA [Lit 32w] ["p"];
    mk_inst 1 MSTORE [Var "p"; Lit 1w] [];
    mk_inst 2 RET [Lit 0w] []] |>]``);
val _ = temp_overload_on ("corrected_entry",
  ``mk_raw_function "entry" [<|bb_label := "entry"; bb_instructions := [
    mk_inst 3 INVOKE [Label "f"] [];
    mk_inst 4 DLOAD [Lit 0w] ["d"];
    mk_inst 5 ALLOCA [Lit 32w] ["q"];
    mk_inst 6 MLOAD [Var "q"] ["v"];
    mk_inst 7 SSTORE [Lit 0w; Var "v"] [];
    mk_inst 8 CALL [Lit 0w; Lit 256w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] ["ok"];
    mk_inst 9 ASSERT [Var "ok"] [];
    mk_inst 10 SLOAD [Lit 0w] ["w"];
    mk_inst 11 SSTORE [Lit 1w; Var "w"] [];
    mk_inst 12 STOP [] []] |>]``);
val _ = temp_overload_on ("corrected_context",
  ``mk_venom_context [corrected_entry; corrected_helper] (SOME "entry")``);

Theorem corrected_no_opaque_seeds:
  !fn origin. MEM fn [corrected_entry; corrected_helper] /\
    MEM origin [GAS; RETPC_PARAM] ==>
    !x. ~copy_phi_var origin fn x
Proof
  rpt gen_tac >> strip_tac >> irule copy_phi_var_no_seed >>
  gvs[] >> EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem corrected_opaque:
  !fn. MEM fn [corrected_entry; corrected_helper] ==> opaque_use_ok fn
Proof
  rpt strip_tac >> simp[opaque_use_ok_def, gas_var_def, retpc_var_def] >>
  metis_tac[corrected_no_opaque_seeds, listTheory.MEM]
QED

Theorem corrected_invoke_syntax:
  !fn. MEM fn [corrected_entry; corrected_helper] ==>
    fn_invoke_ok ["entry"; "f"] fn /\ fn_label_refs_ok fn
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[fn_invoke_ok_def, fn_label_refs_ok_def, fn_insts_def,
       mk_raw_function_def, fn_insts_blocks_def, mk_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem corrected_shape:
  o1_ctx_shape corrected_context
Proof
  `opaque_use_ok corrected_entry /\ opaque_use_ok corrected_helper` by
    metis_tac[corrected_opaque, listTheory.MEM] >>
  `fn_invoke_ok ["entry"; "f"] corrected_entry /\
   fn_invoke_ok ["entry"; "f"] corrected_helper /\
   fn_label_refs_ok corrected_entry /\ fn_label_refs_ok corrected_helper` by
    metis_tac[corrected_invoke_syntax, listTheory.MEM] >>
  `ctx_fn_names corrected_context = ["entry"; "f"]` by EVAL_TAC >>
  gvs[mk_venom_context_def] >>
  simp[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def] >>
  rpt conj_tac >> EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem corrected_callee_order:
  callee_first ["f"; "entry"] corrected_context.ctx_functions
Proof
  simp[callee_first_def, mk_venom_context_def] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- (`fn_invoke_targets corrected_entry = ["f"]` by
        (rewrite_tac[fn_invoke_targets_def, fcg_scan_function_def, fn_insts_def,
                     mk_raw_function_def, fn_insts_blocks_def] >>
         EVAL_TAC >> rewrite_tac[get_invoke_targets_def] >> EVAL_TAC) >>
      gvs[] >> EVAL_TAC) >>
  gvs[probe_helper_targets]
QED

val _ = temp_overload_on ("corrected_vs",
  ``(init_venom_state "entry") with
     <|vs_accounts := K empty_account_state;
       vs_outcomes := [<| co_success := T; co_returnData := [];
         co_accounts := K empty_account_state;
         co_tStorage := K (K (0w:bytes32)); co_logs := []; co_toDelete := [] |>];
       vs_labels := FEMPTY |+ ("code_end",0w)|>``);

Theorem corrected_initial:
  o1_initial_state_ok corrected_vs /\
  corrected_vs.vs_fmp = corrected_vs.vs_initial_fmp /\
  corrected_vs.vs_alloca_next = 0 /\
  corrected_vs.vs_memory = [] /\ corrected_vs.vs_allocas = FEMPTY /\
  corrected_vs.vs_vars = FEMPTY /\
  corrected_vs.vs_code = [] /\ corrected_vs.vs_data_section = [] /\
  ~corrected_vs.vs_call_ctx.cc_static
Proof
  EVAL_TAC
QED

Theorem corrected_code_layout:
  code_layout_valid corrected_vs
Proof
  simp[code_layout_valid_def, init_venom_state_def] >> EVAL_TAC
QED

Theorem corrected_run_state:
  o1_run_state_ok corrected_vs
Proof
  simp[o1_run_state_ok_def, corrected_initial, corrected_code_layout]
QED

Theorem corrected_entry_reachable:
  frame_reachable corrected_vs corrected_context [] [] FEMPTY entry_taint
    corrected_entry (mk_inst 3 INVOKE [Label "f"] []) corrected_vs
Proof
  irule frame_reachable_entry >>
  conj_tac >- (qexists_tac `"entry"` >> EVAL_TAC) >>
  conj_tac >-
    simp[active_inst_def, mk_raw_function_def, init_venom_state_def, mk_inst_def] >>
  qexists_tac `"entry"` >>
  simp[fn_entry_label_def, entry_block_def, mk_raw_function_def,
       enters_block_def, init_venom_state_def, lookup_block_def,
       listTheory.FIND_thm, eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

val _ = temp_overload_on ("corrected_h0",
  ``corrected_vs with vs_current_bb := "f"``);
val _ = temp_overload_on ("corrected_stack",
  ``[<|cf_fn := corrected_entry;
       cf_inst := mk_inst 3 INVOKE [Label "f"] [];
       cf_state := corrected_vs; cf_params := [];
       cf_prov := FEMPTY; cf_tvar := entry_taint.t_var|>]``);

Theorem corrected_helper_entry:
  frame_reachable corrected_vs corrected_context corrected_stack
    (MAP (op_prov FEMPTY) []) FEMPTY
    (entry_taint with t_var := FEMPTY) corrected_helper
    (mk_inst 0 ALLOCA [Lit 32w] ["p"]) corrected_h0
Proof
  irule frame_reachable_call >>
  simp[corrected_entry_reachable, active_inst_def, mk_raw_function_def,
       init_venom_state_def, mk_inst_def, decode_invoke_def] >>
  conj_tac >- EVAL_TAC >>
  simp[eval_operands_def, setup_callee_def, mk_raw_function_def,
       enters_block_def, lookup_block_def, listTheory.FIND_thm,
       eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

val _ = temp_overload_on ("corrected_ha",
  ``update_var "p" 0w (corrected_h0 with
      <|vs_allocas := FEMPTY |+ (0,(0,32)); vs_alloca_next := 32|>)``);
val _ = temp_overload_on ("corrected_h1",
  ``corrected_ha with vs_inst_idx := SUC corrected_h0.vs_inst_idx``);

Theorem corrected_helper_alloca:
  !fuel. step_inst fuel corrected_context (mk_inst 0 ALLOCA [Lit 32w] ["p"])
     corrected_h0 = OK corrected_ha
Proof
  gen_tac >> simp[Once step_inst_def, mk_inst_def] >>
  simp[step_inst_base_def, mk_inst_def, eval_operand_def] >>
  simp[exec_alloca_def, init_venom_state_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem corrected_helper_store_reachable:
  frame_reachable corrected_vs corrected_context corrected_stack
    (MAP (op_prov FEMPTY) [])
    (step_prov (MAP (op_prov FEMPTY) []) FEMPTY (mk_inst 0 ALLOCA [Lit 32w] ["p"]) corrected_ha)
    (step_taint (mk_inst 0 ALLOCA [Lit 32w] ["p"]) corrected_h0 corrected_ha
      (entry_taint with t_var := FEMPTY)) corrected_helper
    (mk_inst 1 MSTORE [Var "p"; Lit 1w] []) corrected_h1
Proof
  irule frame_reachable_next >>
  simp[corrected_helper_entry, corrected_helper_alloca, mk_inst_def,
       is_terminator_def, active_inst_def, mk_raw_function_def,
       init_venom_state_def, update_var_def]
QED

val _ = temp_overload_on ("corrected_hs", ``mstore 0 1w corrected_h1``);
val _ = temp_overload_on ("corrected_h2",
  ``corrected_hs with vs_inst_idx := SUC corrected_h1.vs_inst_idx``);
val _ = temp_overload_on ("corrected_G1",
  ``step_prov (MAP (op_prov FEMPTY) []) FEMPTY
      (mk_inst 0 ALLOCA [Lit 32w] ["p"]) corrected_ha``);
val _ = temp_overload_on ("corrected_t1",
  ``step_taint (mk_inst 0 ALLOCA [Lit 32w] ["p"]) corrected_h0 corrected_ha
      (entry_taint with t_var := FEMPTY)``);

Theorem corrected_helper_store:
  !fuel. step_inst fuel corrected_context (mk_inst 1 MSTORE [Var "p"; Lit 1w] [])
    corrected_h1 = OK corrected_hs
Proof
  gen_tac >> simp[Once step_inst_def, mk_inst_def] >>
  simp[step_inst_base_def, mk_inst_def, exec_write2_def, eval_operands_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem corrected_helper_ret_reachable:
  frame_reachable corrected_vs corrected_context corrected_stack
    (MAP (op_prov FEMPTY) [])
    (step_prov (MAP (op_prov FEMPTY) []) corrected_G1
      (mk_inst 1 MSTORE [Var "p"; Lit 1w] []) corrected_hs)
    (step_taint (mk_inst 1 MSTORE [Var "p"; Lit 1w] []) corrected_h1
      corrected_hs corrected_t1) corrected_helper (mk_inst 2 RET [Lit 0w] []) corrected_h2
Proof
  irule frame_reachable_next >>
  simp[corrected_helper_store_reachable, corrected_helper_store, mk_inst_def,
       is_terminator_def, active_inst_def, mk_raw_function_def,
       init_venom_state_def, update_var_def, mstore_def]
QED

Theorem corrected_helper_ret:
  !fuel. step_inst fuel corrected_context (mk_inst 2 RET [Lit 0w] []) corrected_h2 =
    IntRet <|iret_values := []; iret_adopt_fmp := NONE|> corrected_h2
Proof
  gen_tac >> simp[Once step_inst_def, mk_inst_def] >>
  simp[step_inst_base_def, mk_inst_def, eval_operands_def, eval_operand_def]
QED

val _ = temp_overload_on ("corrected_c0",
  ``merge_callee_state corrected_vs corrected_h2``);
val _ = temp_overload_on ("corrected_c1",
  ``corrected_c0 with vs_inst_idx := SUC corrected_vs.vs_inst_idx``);
val _ = temp_overload_on ("corrected_t2",
  ``step_taint (mk_inst 1 MSTORE [Var "p"; Lit 1w] []) corrected_h1
      corrected_hs corrected_t1``);

