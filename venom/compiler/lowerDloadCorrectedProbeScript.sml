(* Shape-only checkpoint for a separately named corrected reset candidate. *)
Theory lowerDloadCorrectedProbe
Ancestors
  lowerDloadProgramProbe o1PassContract lowerDloadDefs venomInst
  venomFnScheduleRunner fcgDefs unitShapeDefs venomState unitTransformDefs
  finite_map vfmState ptrDiscipline contextCodegenRel venomExecSemantics venomMemProps valueEncodingProofs
  lowerDloadResetProbe venomCallOracleDefs extCallOracle codegenRel

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


Theorem probe_frame_return[local]:
  frame_reachable vs0 ctx
    (<|cf_fn := caller; cf_inst := cin; cf_state := cs; cf_params := CPG;
       cf_prov := CG; cf_tvar := CT|> :: stk) PG G tn fn ri s /\
  active_inst fn ri s /\ step_inst fuel ctx ri s = IntRet ret se /\
  bind_outputs cin.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state cs se)) = SOME sr /\
  active_inst caller ni (sr with vs_inst_idx := SUC cs.vs_inst_idx) ==>
  frame_reachable vs0 ctx stk CPG
    (DRESTRICT CG (COMPL (set cin.inst_outputs)))
    (tn with t_var := DRESTRICT CT (COMPL (set cin.inst_outputs)))
    caller ni (sr with vs_inst_idx := SUC cs.vs_inst_idx)
Proof
  rpt strip_tac >>
  drule frame_reachable_ret >> simp[] >> disch_then irule >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem corrected_caller_dload_reachable:
  frame_reachable corrected_vs corrected_context [] []
    (DRESTRICT FEMPTY (COMPL (set (mk_inst 3 INVOKE [Label "f"] []).inst_outputs)))
    (corrected_t2 with t_var := DRESTRICT entry_taint.t_var
      (COMPL (set (mk_inst 3 INVOKE [Label "f"] []).inst_outputs)))
    corrected_entry (mk_inst 4 DLOAD [Lit 0w] ["d"]) corrected_c1
Proof
  assume_tac corrected_helper_ret_reachable >>
  drule probe_frame_return >>
  simp[corrected_helper_ret, bind_outputs_def, adopt_return_fmp_def, mk_inst_def] >>
  disch_then irule >>
  simp[active_inst_def, mk_raw_function_def, init_venom_state_def,
       merge_callee_state_def, mstore_def, update_var_def, mk_inst_def]
QED

Theorem corrected_return_projections:
  corrected_c1.vs_alloca_next = 0 /\ corrected_c1.vs_allocas = FEMPTY /\
  mload 0 corrected_c1 = 1w
Proof
  conj_tac >- simp[merge_callee_state_def, init_venom_state_def] >>
  conj_tac >- simp[merge_callee_state_def, init_venom_state_def] >>
  `mload 0 corrected_c1 = mload 0 corrected_hs` by
    simp[mload_def, merge_callee_state_def] >>
  simp[mload_mstore_same]
QED

val _ = temp_overload_on ("corrected_cd", ``update_var "d" 0w corrected_c1``);
val _ = temp_overload_on ("corrected_c2",
  ``corrected_cd with vs_inst_idx := SUC corrected_c1.vs_inst_idx``);
val _ = temp_overload_on ("corrected_ct",
  ``corrected_t2 with t_var := DRESTRICT entry_taint.t_var
      (COMPL (set (mk_inst 3 INVOKE [Label "f"] []).inst_outputs))``);
val _ = temp_overload_on ("corrected_CG",
  ``DRESTRICT FEMPTY (COMPL (set (mk_inst 3 INVOKE [Label "f"] []).inst_outputs))``);

Theorem corrected_caller_dload:
  !fuel. step_inst fuel corrected_context (mk_inst 4 DLOAD [Lit 0w] ["d"])
    corrected_c1 = OK corrected_cd
Proof
  `corrected_c1.vs_data_section = []` by
    simp[merge_callee_state_def, init_venom_state_def] >>
  qmatch_goalsub_abbrev_tac `step_inst _ _ _ st` >>
  `st.vs_data_section = []` by simp[Abbr `st`] >>
  gen_tac >> simp[Once step_inst_def, mk_inst_def] >>
  simp[step_inst_base_def, mk_inst_def, exec_read1_def, eval_operand_def] >>
  simp[listTheory.TAKE_LENGTH_TOO_LONG, word_of_bytes_replicate_zero]
QED

Theorem corrected_caller_alloca_reachable:
  frame_reachable corrected_vs corrected_context [] []
    (step_prov [] corrected_CG (mk_inst 4 DLOAD [Lit 0w] ["d"]) corrected_cd)
    (step_taint (mk_inst 4 DLOAD [Lit 0w] ["d"]) corrected_c1 corrected_cd corrected_ct)
    corrected_entry (mk_inst 5 ALLOCA [Lit 32w] ["q"]) corrected_c2
Proof
  irule frame_reachable_next >>
  simp[corrected_caller_dload_reachable, corrected_caller_dload, mk_inst_def,
       is_terminator_def] >>
  conj_tac >- (EVAL_TAC >> simp[]) >> EVAL_TAC >> simp[]
QED

val _ = temp_overload_on ("corrected_cqa",
  ``update_var "q" 0w (corrected_c2 with
    <|vs_allocas := FEMPTY |+ (5,(0,32)); vs_alloca_next := 32|>)``);
val _ = temp_overload_on ("corrected_c3",
  ``corrected_cqa with vs_inst_idx := SUC corrected_c2.vs_inst_idx``);

Theorem corrected_caller_alloca:
  !fuel. step_inst fuel corrected_context (mk_inst 5 ALLOCA [Lit 32w] ["q"])
    corrected_c2 = OK corrected_cqa
Proof
  `corrected_c2.vs_allocas = FEMPTY /\ corrected_c2.vs_alloca_next = 0` by
    simp[merge_callee_state_def, init_venom_state_def, update_var_def] >>
  qmatch_goalsub_abbrev_tac `step_inst _ _ _ st` >>
  `st.vs_allocas = FEMPTY /\ st.vs_alloca_next = 0` by simp[Abbr `st`] >>
  gen_tac >> simp[Once step_inst_def, mk_inst_def] >>
  simp[step_inst_base_def, mk_inst_def, eval_operand_def] >>
  simp[exec_alloca_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

val _ = temp_overload_on ("corrected_CG2",
  ``step_prov [] corrected_CG (mk_inst 4 DLOAD [Lit 0w] ["d"]) corrected_cd``);
val _ = temp_overload_on ("corrected_ct2",
  ``step_taint (mk_inst 4 DLOAD [Lit 0w] ["d"]) corrected_c1 corrected_cd corrected_ct``);

Theorem corrected_caller_mload_reachable:
  frame_reachable corrected_vs corrected_context [] []
    (step_prov [] corrected_CG2 (mk_inst 5 ALLOCA [Lit 32w] ["q"]) corrected_cqa)
    (step_taint (mk_inst 5 ALLOCA [Lit 32w] ["q"]) corrected_c2 corrected_cqa corrected_ct2)
    corrected_entry (mk_inst 6 MLOAD [Var "q"] ["v"]) corrected_c3
Proof
  irule frame_reachable_next >>
  simp[corrected_caller_alloca_reachable, corrected_caller_alloca, mk_inst_def,
       is_terminator_def] >>
  conj_tac >- (EVAL_TAC >> simp[]) >> EVAL_TAC >> simp[]
QED

Theorem corrected_q_memory:
  lookup_var "q" corrected_c3 = SOME 0w /\ mload 0 corrected_c3 = 1w
Proof
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `mload 0 corrected_c3 = mload 0 corrected_c1` by simp[mload_def, update_var_def] >>
  simp[corrected_return_projections]
QED

val _ = temp_overload_on ("corrected_cv", ``update_var "v" 1w corrected_c3``);
val _ = temp_overload_on ("corrected_c4",
  ``corrected_cv with vs_inst_idx := SUC corrected_c3.vs_inst_idx``);

Theorem corrected_caller_mload:
  !fuel. step_inst fuel corrected_context (mk_inst 6 MLOAD [Var "q"] ["v"])
    corrected_c3 = OK corrected_cv
Proof
  mp_tac corrected_q_memory >> strip_tac >>
  qmatch_goalsub_abbrev_tac `step_inst _ _ _ st` >>
  `lookup_var "q" st = SOME 0w /\ mload 0 st = 1w` by simp[Abbr `st`] >>
  gen_tac >> simp[Once step_inst_def, mk_inst_def] >>
  simp[step_inst_base_def, mk_inst_def, exec_read1_def, eval_operand_def]
QED

val _ = temp_overload_on ("corrected_CG3",
  ``step_prov [] corrected_CG2 (mk_inst 5 ALLOCA [Lit 32w] ["q"]) corrected_cqa``);
val _ = temp_overload_on ("corrected_ct3",
  ``step_taint (mk_inst 5 ALLOCA [Lit 32w] ["q"]) corrected_c2 corrected_cqa corrected_ct2``);

Theorem corrected_caller_sstore_reachable:
  frame_reachable corrected_vs corrected_context [] []
    (step_prov [] corrected_CG3 (mk_inst 6 MLOAD [Var "q"] ["v"]) corrected_cv)
    (step_taint (mk_inst 6 MLOAD [Var "q"] ["v"]) corrected_c3 corrected_cv corrected_ct3)
    corrected_entry (mk_inst 7 SSTORE [Lit 0w; Var "v"] []) corrected_c4
Proof
  irule frame_reachable_next >>
  simp[corrected_caller_mload_reachable, corrected_caller_mload, mk_inst_def,
       is_terminator_def] >>
  conj_tac >- (EVAL_TAC >> simp[]) >> EVAL_TAC >> simp[]
QED

val _ = temp_overload_on ("corrected_cs", ``sstore 0w 1w corrected_c4``);
val _ = temp_overload_on ("corrected_c5",
  ``corrected_cs with vs_inst_idx := SUC corrected_c4.vs_inst_idx``);

Theorem corrected_caller_sstore:
  !fuel. step_inst fuel corrected_context (mk_inst 7 SSTORE [Lit 0w; Var "v"] [])
    corrected_c4 = OK corrected_cs
Proof
  `lookup_var "v" corrected_c4 = SOME 1w` by
    simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac `step_inst _ _ _ st` >>
  `lookup_var "v" st = SOME 1w` by simp[Abbr `st`] >>
  gen_tac >> simp[Once step_inst_def, mk_inst_def] >>
  simp[step_inst_base_def, mk_inst_def, exec_write2_def, eval_operand_def]
QED

val _ = temp_overload_on ("corrected_CG4",
  ``step_prov [] corrected_CG3 (mk_inst 6 MLOAD [Var "q"] ["v"]) corrected_cv``);
val _ = temp_overload_on ("corrected_ct4",
  ``step_taint (mk_inst 6 MLOAD [Var "q"] ["v"]) corrected_c3 corrected_cv corrected_ct3``);

Theorem corrected_caller_call_reachable:
  frame_reachable corrected_vs corrected_context [] []
    (step_prov [] corrected_CG4 (mk_inst 7 SSTORE [Lit 0w; Var "v"] []) corrected_cs)
    (step_taint (mk_inst 7 SSTORE [Lit 0w; Var "v"] []) corrected_c4 corrected_cs corrected_ct4)
    corrected_entry
    (mk_inst 8 CALL [Lit 0w; Lit 256w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] ["ok"])
    corrected_c5
Proof
  irule frame_reachable_next >>
  simp[corrected_caller_sstore_reachable, corrected_caller_sstore, mk_inst_def,
       is_terminator_def] >>
  conj_tac >- (EVAL_TAC >> simp[]) >> EVAL_TAC >> simp[]
QED

val _ = temp_overload_on ("corrected_outcome",
  ``<|co_success := T; co_returnData := []; co_accounts := K empty_account_state;
      co_tStorage := K (K (0w:bytes32)); co_logs := []; co_toDelete := []|>``);
val _ = temp_overload_on ("corrected_call_inst",
  ``mk_inst 8 CALL [Lit 0w; Lit 256w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] ["ok"]``);
val _ = temp_overload_on ("corrected_call_post",
  ``update_var "ok" 1w (SND (consume_call_outcome
      (venom_call_request corrected_c5 256w 0w 0w 0w F) 0 0 corrected_c5))``);

Theorem corrected_before_call:
  ~corrected_c5.vs_call_ctx.cc_static /\
  corrected_c5.vs_outcomes = [corrected_outcome] /\
  sload 0w corrected_c5 = 1w
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem corrected_call_step:
  !fuel. step_inst fuel corrected_context corrected_call_inst corrected_c5 = OK corrected_call_post
Proof
  mp_tac corrected_before_call >> strip_tac >>
  qmatch_goalsub_abbrev_tac `step_inst _ _ _ st` >>
  `~st.vs_call_ctx.cc_static /\ st.vs_outcomes = [corrected_outcome]` by simp[Abbr `st`] >>
  gen_tac >>
  simp[Once step_inst_def, step_inst_base_def, mk_inst_def,
       eval_operand_def, exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  simp[consume_call_outcome_def, reset_probe_ordinary, take_outcome_def,
       adopt_outcome_def, venom_call_request_def]
QED

Theorem corrected_caller_new_site:
  new_site_bytes corrected_c2 corrected_cqa = {i | i < 32}
Proof
  `corrected_c2.vs_allocas = FEMPTY /\ corrected_c2.vs_fmp = 0w /\
   corrected_cqa.vs_allocas = FEMPTY |+ (5,(0,32)) /\ corrected_cqa.vs_fmp = 0w` by
    (rpt conj_tac >> EVAL_TAC) >>
  qmatch_goalsub_abbrev_tac `new_site_bytes s t` >>
  `s.vs_allocas = FEMPTY /\ s.vs_fmp = 0w /\
   t.vs_allocas = FEMPTY |+ (5,(0,32)) /\ t.vs_fmp = 0w` by simp[Abbr `s`, Abbr `t`] >>
  simp[new_site_bytes_def, FLOOKUP_UPDATE, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED


Theorem corrected_helper_new_site[local]:
  new_site_bytes corrected_h0 corrected_ha = {i | i < 32}
Proof
  `corrected_h0.vs_allocas = FEMPTY /\ corrected_h0.vs_fmp = 0w /\
   corrected_ha.vs_allocas = FEMPTY |+ (0,(0,32)) /\ corrected_ha.vs_fmp = 0w` by
    (rpt conj_tac >> EVAL_TAC) >>
  qmatch_goalsub_abbrev_tac `new_site_bytes s t` >>
  `s.vs_allocas = FEMPTY /\ s.vs_fmp = 0w /\
   t.vs_allocas = FEMPTY |+ (0,(0,32)) /\ t.vs_fmp = 0w` by simp[Abbr `s`, Abbr `t`] >>
  simp[new_site_bytes_def, FLOOKUP_UPDATE, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem probe_alloca_writes[local]:
  range_bytes (step_writes (mk_inst aid ALLOCA [Lit sz] [out]) s t) = {} /\
  written_taint tn (mk_inst aid ALLOCA [Lit sz] [out]) s = {}
Proof
  simp[step_writes_def, source_memory_write_ranges_def, mk_inst_def,
       range_bytes_def, written_taint_def]
QED

Theorem corrected_helper_alloca_taint:
  corrected_t1.t_mem = {i | i < 32}
Proof
  simp[Once step_taint_def, mem_taint_def, corrected_helper_new_site,
       probe_alloca_writes, entry_taint_def]
QED

Theorem corrected_helper_store_new_site[local]:
  new_site_bytes corrected_h1 corrected_hs = {}
Proof
  qmatch_goalsub_abbrev_tac `new_site_bytes s t` >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp` by
    simp[Abbr `t`, Abbr `s`, mstore_def] >>
  simp[new_site_bytes_def, pred_setTheory.EXTENSION] >>
  rpt gen_tac >> Cases_on `aid IN FDOM s.vs_allocas` >> simp[FLOOKUP_DEF]
QED

Theorem corrected_helper_store_writes[local]:
  range_bytes (step_writes (mk_inst 1 MSTORE [Var "p"; Lit 1w] []) corrected_h1 corrected_hs) =
    {i | i < 32} /\
  written_taint corrected_t1 (mk_inst 1 MSTORE [Var "p"; Lit 1w] []) corrected_h1 = {}
Proof
  `eval_operand (Var "p") corrected_h1 = SOME 0w` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac `step_writes _ s t` >>
  `eval_operand (Var "p") s = SOME 0w` by simp[Abbr `s`] >>
  simp[step_writes_def, source_memory_write_ranges_def, mk_inst_def,
       fixed_source_write_range_def, eval_operand_def,
       range_bytes_def, written_taint_def, op_taint_def] >>
  simp[pred_setTheory.EXTENSION]
QED

Theorem corrected_helper_store_taint:
  corrected_t2.t_mem = {}
Proof
  simp[Once step_taint_def, Once mem_taint_def, corrected_helper_store_new_site,
       corrected_helper_store_writes, corrected_helper_alloca_taint]
QED

Theorem corrected_dload_new_site[local]:
  new_site_bytes corrected_c1 corrected_cd = {}
Proof
  qmatch_goalsub_abbrev_tac `new_site_bytes s t` >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp` by
    simp[Abbr `t`, update_var_def] >>
  simp[new_site_bytes_def, pred_setTheory.EXTENSION] >>
  rpt gen_tac >> Cases_on `aid IN FDOM s.vs_allocas` >> simp[FLOOKUP_DEF]
QED

Theorem corrected_dload_writes[local]:
  range_bytes (step_writes (mk_inst 4 DLOAD [Lit 0w] ["d"]) corrected_c1 corrected_cd) = {} /\
  written_taint corrected_ct (mk_inst 4 DLOAD [Lit 0w] ["d"]) corrected_c1 = {}
Proof
  simp[step_writes_def, source_memory_write_ranges_def, mk_inst_def,
       range_bytes_def, written_taint_def]
QED

Theorem corrected_dload_taint:
  corrected_ct2.t_mem = {}
Proof
  simp[Once step_taint_def, Once mem_taint_def, corrected_dload_new_site,
       corrected_dload_writes, corrected_helper_store_taint]
QED

Theorem corrected_caller_alloca_taint:
  corrected_ct3.t_mem = {i | i < 32}
Proof
  simp[Once step_taint_def, Once mem_taint_def, corrected_caller_new_site,
       probe_alloca_writes, corrected_dload_taint]
QED

Theorem corrected_mload_out_taint[local]:
  out_taint corrected_ct3 (mk_inst 6 MLOAD [Var "q"] ["v"]) corrected_c3 = {k | k < 32}
Proof
  `eval_operand (Var "q") corrected_c3 = SOME 0w` by
    simp[eval_operand_def, corrected_q_memory] >>
  qmatch_goalsub_abbrev_tac `out_taint tn inst s` >>
  `eval_operand (Var "q") s = SOME 0w` by simp[Abbr `s`] >>
  `tn.t_mem = {i | i < 32}` by simp[Abbr `tn`, corrected_caller_alloca_taint] >>
  simp[out_taint_def, Abbr `inst`, mk_inst_def, mem_word_taint_def]
QED

Theorem corrected_mload_var_taint:
  FLOOKUP corrected_ct4.t_var "v" = SOME {k | k < 32}
Proof
  simp[Once step_taint_def, corrected_mload_out_taint, set_var_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem corrected_pre_sstore_storage_taint:
  corrected_ct4.t_stor = {}
Proof
  simp[Once step_taint_def, adopt_reset_def, store_taint_def, mk_inst_def] >>
  simp[Once step_taint_def, adopt_reset_def, store_taint_def, mk_inst_def] >>
  simp[Once step_taint_def, adopt_reset_def, store_taint_def, mk_inst_def] >>
  simp[Once step_taint_def, adopt_reset_def, store_taint_def, mk_inst_def] >>
  simp[Once step_taint_def, adopt_reset_def, store_taint_def, mk_inst_def] >>
  simp[entry_taint_def]
QED

val _ = temp_overload_on ("corrected_ct5",
  ``step_taint (mk_inst 7 SSTORE [Lit 0w; Var "v"] []) corrected_c4 corrected_cs corrected_ct4``);

Theorem corrected_pre_call_storage_taint:
  corrected_ct5.t_stor = {(key,k) | key = (0w:bytes32) /\ k < 32}
Proof
  qmatch_goalsub_abbrev_tac `step_taint inst s t tn` >>
  `FLOOKUP tn.t_var "v" = SOME {k | k < 32} /\ tn.t_stor = {}` by
    simp[Abbr `tn`, corrected_mload_var_taint, corrected_pre_sstore_storage_taint] >>
  simp[Once step_taint_def, adopt_reset_def, Abbr `inst`, mk_inst_def, store_taint_def,
       eval_operand_def, op_taint_def, key_update_def, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem corrected_post_call_accounts:
  corrected_call_post.vs_accounts = K empty_account_state
Proof
  `~corrected_c5.vs_call_ctx.cc_static /\
   corrected_c5.vs_outcomes = [corrected_outcome]` by simp[corrected_before_call] >>
  qmatch_goalsub_abbrev_tac `consume_call_outcome _ _ _ st` >>
  `~st.vs_call_ctx.cc_static /\ st.vs_outcomes = [corrected_outcome]` by simp[Abbr `st`] >>
  simp[update_var_def, consume_call_outcome_def, reset_probe_ordinary,
       take_outcome_def, Excl "consume_call_outcome_eq"] >>
  simp[adopt_outcome_def, venom_call_request_def]
QED

Theorem corrected_call_changes_accounts:
  corrected_call_post.vs_accounts <> corrected_c5.vs_accounts
Proof
  strip_tac >>
  `corrected_c5.vs_accounts = K empty_account_state` by
    (mp_tac corrected_post_call_accounts >> asm_rewrite_tac[]) >>
  `sload 0w corrected_c5 = 0w` by
    (simp[sload_def, contract_storage_def] >> EVAL_TAC) >>
  mp_tac corrected_before_call >> simp[]
QED

Theorem corrected_post_call_storage_taint:
  (step_taint corrected_call_inst corrected_c5 corrected_call_post corrected_ct5).t_stor = {}
Proof
  qmatch_goalsub_abbrev_tac `step_taint inst s t tn` >>
  `t.vs_accounts <> s.vs_accounts` by
    simp[Abbr `t`, Abbr `s`, corrected_call_changes_accounts] >>
  simp[Once step_taint_def, adopt_reset_def, Abbr `inst`, mk_inst_def]
QED

(* Constant dead masks for the corrected candidate: every byte of key 0. *)
val _ = temp_overload_on ("corrected_D",
  ``<|d_stor := (\a st. {(key,k) | key = (0w:bytes32) /\ k < 32});
      d_trans := (\a st. {}); d_imm := (\im. {}); d_ret := (\ret. {})|>``);

Theorem corrected_dead_wf:
  dead_wf corrected_D
Proof
  simp[dead_wf_def]
QED

Theorem corrected_source_structure:
  reserved_intervals_wf corrected_context.ctx_global_reserved /\
  EVERY (\fn. fn.fn_eom = NONE) corrected_context.ctx_functions /\
  ~ctx_has_dalloca corrected_context /\
  fixed_region_reserved 0 corrected_context /\
  fmp_free_ctx corrected_context
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- simp[fixed_region_reserved_def] >>
  EVAL_TAC
QED

Theorem corrected_call_storage_contained:
  corrected_ct5.t_stor SUBSET
    corrected_D.d_stor corrected_c5.vs_call_ctx.cc_address
      (corrected_c5.vs_accounts corrected_c5.vs_call_ctx.cc_address).storage
Proof
  simp[corrected_pre_call_storage_taint]
QED

Theorem corrected_call_access:
  !lo G fn s. access_ok lo G fn corrected_call_inst s
Proof
  simp[access_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, memory_range_of_operands_def,
       mk_inst_def, eval_operand_def]
QED

Theorem corrected_call_taint_ok:
  !fn tn s. taint_ok fn tn corrected_call_inst s
Proof
  simp[taint_ok_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, mk_inst_def, eval_operand_def,
       op_taint_def] >> rpt gen_tac >> Cases_on `op` >> simp[]
QED


Theorem corrected_call_control:
  corrected_call_post.vs_current_bb = corrected_c5.vs_current_bb /\
  corrected_call_post.vs_inst_idx = corrected_c5.vs_inst_idx /\
  corrected_call_post.vs_halted = corrected_c5.vs_halted
Proof
  qspec_then `0` assume_tac corrected_call_step >>
  drule venomInstPropsTheory.step_ext_call_preserves >>
  impl_tac >- simp[venomInstTheory.is_ext_call_op_def, mk_inst_def] >>
  disch_then strip_assume_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

val _ = temp_overload_on ("corrected_CG5",
  ``step_prov [] corrected_CG4 (mk_inst 7 SSTORE [Lit 0w; Var "v"] []) corrected_cs``);
val _ = temp_overload_on ("corrected_c6",
  ``corrected_call_post with vs_inst_idx := SUC corrected_c5.vs_inst_idx``);
val _ = temp_overload_on ("corrected_CG6",
  ``step_prov [] corrected_CG5 corrected_call_inst corrected_call_post``);
val _ = temp_overload_on ("corrected_ct6",
  ``step_taint corrected_call_inst corrected_c5 corrected_call_post corrected_ct5``);

Theorem corrected_assert_active:
  active_inst corrected_entry (mk_inst 9 ASSERT [Var "ok"] []) corrected_c6
Proof
  qmatch_goalsub_abbrev_tac `active_inst _ _ (s with vs_inst_idx := n)` >>
  `s.vs_current_bb = "entry"` by
    (simp_tac pure_ss [Abbr `s`, corrected_call_control] >> EVAL_TAC) >>
  `n = 6` by (simp_tac pure_ss [Abbr `n`] >> EVAL_TAC) >>
  simp[active_inst_def, mk_raw_function_def]
QED

Theorem corrected_caller_assert_reachable:
  frame_reachable corrected_vs corrected_context [] [] corrected_CG6 corrected_ct6
    corrected_entry (mk_inst 9 ASSERT [Var "ok"] []) corrected_c6
Proof
  irule frame_reachable_next >>
  conj_tac >- simp[mk_inst_def, is_terminator_def] >>
  conj_tac >- simp[mk_inst_def] >>
  conj_tac >- (qexists_tac `0` >> rewrite_tac[corrected_call_step]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- ACCEPT_TAC corrected_assert_active >>
  ACCEPT_TAC corrected_caller_call_reachable
QED
