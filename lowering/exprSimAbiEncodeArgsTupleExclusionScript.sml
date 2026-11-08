Theory exprSimAbiEncodeArgsTupleExclusion
Ancestors
  exprSimAbiEncodeArgsTupleWitness exprSimAbiEncodeArgsCountedLabels
  gasOutcome gasSummary gasExemptCert fragGasPath venomExecProofs
  exprSimAbiEncodeArgsTupleTarget exprSimAbiEncodeArgsTupleProbe
  abiEncodeArgsSim exprSimWordArgs loweringPosts

Theorem tuple_exprs_evaluation:
  eval_exprs tuple_witness_cx [tuple_call] es =
    (INL [ArrayV (TupleV [BytesV [170w]; BytesV [187w]])],es)
Proof
  simp[exprSimWordArgsTheory.eval_exprs_cons_action,
    exprSimAbiEncodeArgsTupleSourceTheory.tuple_call_evaluation, tuple_witness_context,
    vyperStateTheory.bind_def, vyperStateTheory.read_result_def,
    vyperStateTheory.return_def, exprSimWordArgsTheory.eval_exprs_nil]
QED

Theorem tuple_no_exempt:
  ~gas_exempt_cert F tops (tuple_witness_ctx,tuple_witness_fn)
    (ignore_bind (eval_exprs tuple_witness_cx [tuple_call]) (return ()))
    (tuple_witness_es,tuple_witness_s) marks (err,ee) (leaf,fin)
Proof
  strip_tac >> drule gas_exempt_cert_execution >>
  simp[tuple_exprs_evaluation, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.bind_def, vyperStateTheory.return_def]
QED

Definition tuple_exclusion_trace_def:
  (tuple_exclusion_trace 0 = tuple_witness_s) /\
  (tuple_exclusion_trace (SUC i) =
    case step_inst 1 tuple_witness_ctx
      (EL i (SND tuple_witness_compiled).cs_current_insts)
      (tuple_exclusion_trace i) of
      OK t => t with vs_inst_idx := SUC i
    | _ => tuple_exclusion_trace i)
End

Theorem tuple_exclusion_insts:
  (SND tuple_witness_compiled).cs_current_insts =
    [mk_inst 0 ALLOCA [Lit 128w] ["%0"];
     mk_inst 1 INVOKE [Label tuple_witness_name; Var "%0"] []]
Proof
  EVAL_TAC
QED

Theorem tuple_exclusion_trace_0:
  tuple_exclusion_trace 0 = tuple_witness_s
Proof
  simp[tuple_exclusion_trace_def]
QED

Theorem tuple_exclusion_trace_1:
  tuple_exclusion_trace 1 =
    tuple_witness_s with <|vs_vars := FEMPTY |+ ("%0",0w);
      vs_allocas := FEMPTY |+ (0,(0,128)); vs_alloca_next := 128;
      vs_inst_idx := 1|>
Proof
  CONV_TAC (LAND_CONV (RAND_CONV numLib.num_CONV)) >>
  once_rewrite_tac[tuple_exclusion_trace_def] >>
  simp[tuple_exclusion_trace_0, tuple_exclusion_insts,
    venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def,
    venomStateTheory.eval_operand_def, venomInstTheory.mk_inst_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem tuple_exclusion_trace_1_operand:
  eval_operand (Var "%0") (tuple_exclusion_trace 1) = SOME 0w
Proof
  simp[tuple_exclusion_trace_1, venomStateTheory.eval_operand_def,
    venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem tuple_exclusion_trace_2:
  tuple_exclusion_trace 2 =
    tuple_exclusion_trace 1 with
      <|vs_memory := (tuple_target_writes (0w:bytes32) (tuple_exclusion_trace 1)).vs_memory;
        vs_inst_idx := 2|>
Proof
  `step_inst 1 tuple_witness_ctx
     (mk_inst 1 INVOKE [Label tuple_witness_name; Var "%0"] [])
     (tuple_exclusion_trace 1) =
   OK (tuple_exclusion_trace 1 with vs_memory :=
     (tuple_target_writes (0w:bytes32) (tuple_exclusion_trace 1)).vs_memory)` by
    (irule (cj 1 tuple_target_invoke_in_context) >>
     simp[tuple_witness_lookup, tuple_exclusion_trace_1_operand]) >>
  CONV_TAC (LAND_CONV (RAND_CONV numLib.num_CONV)) >>
  once_rewrite_tac[tuple_exclusion_trace_def] >>
  simp[tuple_exclusion_insts]
QED

Theorem tuple_exclusion_trace_fields:
  !i. i <= 2 ==>
    (tuple_exclusion_trace i).vs_inst_idx = i /\
    (tuple_exclusion_trace i).vs_current_bb = "entry" /\
    ~(tuple_exclusion_trace i).vs_halted
Proof
  gen_tac >> disch_tac >>
  `i = 0 \/ i = 1 \/ i = 2` by decide_tac >> gvs[] >>
  simp[tuple_exclusion_trace_0, tuple_exclusion_trace_1,
    tuple_exclusion_trace_2, tuple_witness_s_def,
    venomStateTheory.init_venom_state_def]
QED

Theorem tuple_exclusion_step:
  !i. i < 2 ==>
    ?t. step_inst 1 tuple_witness_ctx
      (EL i (SND tuple_witness_compiled).cs_current_insts) (tuple_exclusion_trace i) = OK t /\
      tuple_exclusion_trace (SUC i) = t with vs_inst_idx := SUC i
Proof
  rpt strip_tac >>
  `i <= 2 /\ SUC i <= 2` by decide_tac >>
  `(tuple_exclusion_trace i).vs_inst_idx = i /\
   (tuple_exclusion_trace (SUC i)).vs_inst_idx = SUC i` by
    metis_tac[tuple_exclusion_trace_fields] >>
  `tuple_exclusion_trace (SUC i) =
    case step_inst 1 tuple_witness_ctx
      (EL i (SND tuple_witness_compiled).cs_current_insts) (tuple_exclusion_trace i) of
      OK t => t with vs_inst_idx := SUC i
    | _ => tuple_exclusion_trace i` by simp[Once tuple_exclusion_trace_def] >>
  Cases_on `step_inst 1 tuple_witness_ctx
      (EL i (SND tuple_witness_compiled).cs_current_insts) (tuple_exclusion_trace i)` >>
  gvs[] >> decide_tac
QED

Theorem tuple_step_ok_unique[local]:
  step_inst n ctx inst s = OK u /\ step_inst m ctx inst s = OK v ==> u = v
Proof
  rpt strip_tac >>
  `step_inst (n+m) ctx inst s = OK u` by
    (irule (cj 1 venomExecProofsTheory.fuel_mono) >> simp[] >>
     qexists_tac `n` >> simp[]) >>
  `step_inst (n+m) ctx inst s = OK v` by
    (irule (cj 1 venomExecProofsTheory.fuel_mono) >> simp[] >>
     qexists_tac `m` >> simp[]) >> gvs[]
QED

Theorem tuple_exclusion_step_any_fuel:
  i < 2 /\ step_inst fuel tuple_witness_ctx
    (EL i (SND tuple_witness_compiled).cs_current_insts) (tuple_exclusion_trace i) = OK t ==>
    (t with vs_inst_idx := SUC i) = tuple_exclusion_trace (SUC i)
Proof
  rpt strip_tac >> drule tuple_exclusion_step >> strip_tac >>
  `t = t'` by metis_tac[tuple_step_ok_unique] >> simp[]
QED

Theorem tuple_exclusion_nonterm:
  i < 2 ==> ~is_terminator
    (EL i (SND tuple_witness_compiled).cs_current_insts).inst_opcode
Proof
  strip_tac >> `i = 0 \/ i = 1` by decide_tac >> gvs[] >>
  simp[tuple_exclusion_insts, venomInstTheory.mk_inst_def,
    venomInstTheory.is_terminator_def]
QED

Theorem tuple_exclusion_lookup:
  lookup_block "entry" tuple_witness_fn.fn_blocks =
    SOME <|bb_label := "entry";
      bb_instructions := (SND tuple_witness_compiled).cs_current_insts|>
Proof
  simp[tuple_witness_fn_def, venomInstTheory.mk_raw_function_def,
    venomInstTheory.lookup_block_def, listTheory.FIND_thm]
QED

Theorem tuple_exclusion_instruction:
  get_instruction <|bb_label := "entry";
    bb_instructions := (SND tuple_witness_compiled).cs_current_insts|> i =
    if i < 2 then SOME (EL i (SND tuple_witness_compiled).cs_current_insts) else NONE
Proof
  simp[venomInstTheory.get_instruction_def, tuple_exclusion_insts]
QED

Theorem tuple_exclusion_edge_classify:
  i <= 2 /\ gas_path_edge tuple_witness_ctx tuple_witness_fn
    (tuple_exclusion_trace i) n (OK t) ==>
    i < 2 /\ t = tuple_exclusion_trace (SUC i)
Proof
  rpt strip_tac >> drule tuple_exclusion_trace_fields >> strip_tac >>
  gvs[gas_path_edge_def, tuple_exclusion_lookup, tuple_exclusion_instruction,
      fragExecTheory.exit_result_def] >>
  Cases_on `i < 2` >> gvs[] >> gvs[tuple_exclusion_nonterm]
  >- (irule tuple_exclusion_step_any_fuel >> simp[] >>
      qexists_tac `fuel` >> simp[]) >>
  qpat_x_assum `OK _ = _` (assume_tac o SYM) >>
  gvs[fragExecTheory.exit_result_def]
QED

Theorem tuple_exclusion_path_classify_aux[local]:
  !ctx fn s n r. gas_path ctx fn s n r ==>
    !i t. ctx = tuple_witness_ctx /\ fn = tuple_witness_fn /\
      s = tuple_exclusion_trace i /\ r = OK t /\ i <= 2 ==>
      ?j. j <= 2 /\ t = tuple_exclusion_trace j
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> gvs[] >>
      drule_all tuple_exclusion_edge_classify >> strip_tac >>
      first_x_assum irule >> simp[] >>
      qexists_tac `SUC i` >> simp[]) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

Theorem tuple_exclusion_path_endpoint:
  gas_path tuple_witness_ctx tuple_witness_fn tuple_witness_s n (OK t) /\
  t.vs_inst_idx = 2 ==> t = tuple_exclusion_trace 2
Proof
  rpt strip_tac >> drule tuple_exclusion_path_classify_aux >>
  disch_then (qspecl_then [`0`, `t`] mp_tac) >>
  simp[tuple_exclusion_trace_0] >> strip_tac >> gvs[] >>
  drule tuple_exclusion_trace_fields >> strip_tac >> gvs[]
QED

Theorem tuple_exclusion_terminal_memory:
  (tuple_exclusion_trace 2).vs_memory = tuple_memory /\
  eval_operand (Var "%0") (tuple_exclusion_trace 2) = SOME 0w
Proof
  simp[tuple_exclusion_trace_2, tuple_exclusion_trace_1,
    tuple_target_writes_def, tuple_witness_s_def,
    venomStateTheory.init_venom_state_def,
    exprSimAbiEncodeArgsTupleProbeTheory.tuple_memory_def] >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC
QED

Theorem tuple_exclusion_terminal_mismatch:
  ~expr_val_rel tuple_witness_cx tuple_wide
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]]))
    (Var "%0") (tuple_exclusion_trace 2)
Proof
  simp[loweringPostsTheory.expr_val_rel_def, tuple_exclusion_terminal_memory] >>
  qexists_tac `TupleTV [BaseTV (BytesT (Dynamic 64)); BaseTV (BytesT (Dynamic 64))]` >>
  simp[exprSimAbiEncodeArgsTupleProbeTheory.tuple_wide_def,
    exprSimAbiEncodeArgsTupleProbeTheory.tuple_memory_mismatch,
    compileEnvTheory.is_word_type_def] >> EVAL_TAC
QED

Theorem tuple_exclusion_compiled_endpoint:
  FST tuple_witness_compiled = [Var "%0"] /\
  LENGTH (SND tuple_witness_compiled).cs_current_insts = 2
Proof
  EVAL_TAC
QED

Theorem tuple_marked_result:
  gas_marked_exec F (tuple_witness_ctx,tuple_witness_fn)
    (eval_exprs tuple_witness_cx [tuple_call]) (tuple_witness_es,tuple_witness_s)
    marks res ee r ==>
  res = INL [ArrayV (TupleV [BytesV [170w]; BytesV [187w]])]
Proof
  simp[gas_marked_exec_def, tuple_exprs_evaluation] >>
  strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem tuple_exact_post_head[local]:
  abi_args_post tuple_witness_ctx tuple_witness_fn tuple_witness_ce tuple_witness_cx
    tuple_witness_es tuple_witness_sa (SND tuple_witness_compiled) tuple_witness_s ee
    [tuple_call] (FST tuple_witness_compiled)
    [ArrayV (TupleV [BytesV [170w]; BytesV [187w]])] t ==>
  expr_val_rel tuple_witness_cx tuple_wide
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) (Var "%0") t
Proof
  simp[abiEncodeArgsSimTheory.abi_args_post_def, tuple_exclusion_compiled_endpoint,
    exprSimAbiEncodeArgsTupleProbeTheory.tuple_call_def, vyperASTTheory.expr_type_def]
QED

Theorem tuple_exact_outcome_excluded:
  ~gas_outcome F (cx_tops tuple_witness_cx) (tuple_witness_ctx,tuple_witness_fn)
    (eval_exprs tuple_witness_cx [tuple_call]) (tuple_witness_es,tuple_witness_s)
    (\rr ee t. ?vs. rr = INL vs /\
      abi_args_post tuple_witness_ctx tuple_witness_fn tuple_witness_ce tuple_witness_cx
        tuple_witness_es tuple_witness_sa (SND tuple_witness_compiled) tuple_witness_s ee
        [tuple_call] (FST tuple_witness_compiled) vs t /\
      EVERY (abi_decoder_operand_live (SND tuple_witness_compiled).cs_next_var)
        (FST tuple_witness_compiled) /\
      t.vs_current_bb = (SND tuple_witness_compiled).cs_current_bb /\
      t.vs_inst_idx = LENGTH (SND tuple_witness_compiled).cs_current_insts)
    (\rr ee r. wb_args_exit rr r)
Proof
  strip_tac >>
  gvs[gas_outcome_def, tuple_no_exempt, gas_summary_at_def]
  >- (drule tuple_marked_result >> strip_tac >> gvs[] >>
      drule tuple_exact_post_head >> strip_tac >>
      qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
      drule fragGasModeTheory.gas_marked_path_exec >> strip_tac >>
      `t = tuple_exclusion_trace 2` by
        (irule tuple_exclusion_path_endpoint >>
         gvs[tuple_exclusion_compiled_endpoint] >> metis_tac[]) >>
      gvs[tuple_exclusion_terminal_mismatch]) >>
  drule tuple_marked_result >> strip_tac >>
  gvs[exprSimWordArgsTheory.wb_args_exit_def]
QED

(* Negation of the exact frozen universal implication, with every premise
   simultaneously realized by tuple_witness_all_premises. *)
Theorem compile_abi_encode_args_case_gas_sim_false:
  ~(!nocalls ctx func ce cx env ann ensure mid ty args es sa ops sb s0.
    exprs_case nocalls ctx func ce cx args /\
    expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
    (nocalls ==>
     int_calls_expr (TypeBuiltin ann (AbiEncode ensure mid) ty args) = []) /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\
    stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
      (\rr ee t. ?vs. rr = INL vs /\
         abi_args_post ctx func ce cx es sa sb s0 ee args ops vs t /\
         EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee r. wb_args_exit rr r))
Proof
  CONV_TAC (REDEPTH_CONV NOT_FORALL_CONV) >>
  pure_rewrite_tac[NOT_IMP] >>
  qexistsl_tac [`F`, `tuple_witness_ctx`, `tuple_witness_fn`, `tuple_witness_ce`,
    `tuple_witness_cx`, `tuple_witness_env`, `BaseT (BytesT (Dynamic 320))`,
    `T`, `NONE`, `TupleT [tuple_wide]`, `[tuple_call]`, `tuple_witness_es`,
    `tuple_witness_sa`, `FST tuple_witness_compiled`, `SND tuple_witness_compiled`,
    `tuple_witness_s`] >>
  simp[tuple_witness_all_premises, tuple_exact_outcome_excluded]
QED
