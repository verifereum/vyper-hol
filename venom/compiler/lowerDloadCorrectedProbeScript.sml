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

