(* Exact pinned-Python bytecode parity for the scalar_literals_bytes fixture. *)

Theory evalCompilerBytecodeScalarLiteralsBytes
Ancestors evalCompilerBytecodeScalarLiteralsBytesPipeline evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20
val () = computeLib.upd_compset
  (computeLib.add_thms
    [word_of_bytes_be_bytes32_scalar_literals_bytes,
     word_of_bytes_bytes32_scalar_literals_bytes,
     w2n_scalar_literals_bytes_n2w,
     scalar_literals_bytes_n2w_eq_word,
     word_eq_scalar_literals_bytes_n2w,
     contextTheory.compile_copy_memory_def])

(* Stage the three analyses consumed again by stack planning.  Each theorem is
   kernel-produced from the checked pipeline result; no oracle data is used. *)
val scalar_literals_bytes_pipeline_value =
  rhs (concl scalar_literals_bytes_runtime_pipeline_eval)
val scalar_literals_bytes_rp_out = optionSyntax.dest_some scalar_literals_bytes_pipeline_value
val scalar_literals_bytes_rpolicy = #1 (pairSyntax.dest_pair scalar_literals_bytes_rp_out)
val scalar_literals_bytes_out = #2 (pairSyntax.dest_pair scalar_literals_bytes_rp_out)
val scalar_literals_bytes_unit_eval = EVAL ``(^scalar_literals_bytes_out).po_unit``
val scalar_literals_bytes_unit = rhs (concl scalar_literals_bytes_unit_eval)
val scalar_literals_bytes_out_final_assembly_eval =
  EVAL ``(^scalar_literals_bytes_out).po_final_assembly``
val scalar_literals_bytes_rpolicy_final_assembly_eval =
  EVAL ``(^scalar_literals_bytes_rpolicy).rpol_final_assembly``
val scalar_literals_bytes_fn = rhs (concl (EVAL
  ``HD (^scalar_literals_bytes_unit).cu_context.ctx_functions``))
fun scalar_literals_bytes_w2n_eval w =
  if same_const (#1 (strip_comb w)) ``set_byte`` then let
    val bytes_th = SIMP_CONV (srw_ss())
      [word_to_bytes_be_bytes32_genlist_scalar_literals_bytes,
       get_byte_set_byte_bytes32_scalar_literals_bytes,
       get_byte_set_byte_irrelevant_bytes32_scalar_literals_bytes]
      ``word_to_bytes_be ^w``
    val roundtrip = INST [``w:bytes32`` |-> w]
      word_of_bytes_be_word_to_bytes_be_scalar_literals_bytes
    val step1 = BETA_RULE (AP_TERM ``λx:bytes32. w2n x``
      (SYM roundtrip))
    val step2 = BETA_RULE (AP_TERM
      ``λbs. w2n (word_of_bytes_be bs : bytes32)`` bytes_th)
    val decoded = TRANS step1 step2
    val expose = SIMP_CONV bool_ss
      [word_of_bytes_be_bytes32_scalar_literals_bytes,
       w2n_scalar_literals_bytes_n2w] (rhs (concl decoded))
    val numeral = EVAL (rhs (concl expose))
  in
    TRANS decoded (TRANS expose numeral)
  end else
    EVAL ``w2n ^w``
fun scalar_literals_bytes_normalize_word w = let
  val w2n_th = scalar_literals_bytes_w2n_eval w
  val numeral = rhs (concl w2n_th)
  val normalized = ``scalar_literals_bytes_n2w ^numeral``
  val normalized_w2n_step = INST [``n:num`` |-> numeral]
    w2n_scalar_literals_bytes_n2w
  val normalized_w2n = TRANS normalized_w2n_step
    (EVAL (rhs (concl normalized_w2n_step)))
  val same_num = TRANS w2n_th (SYM normalized_w2n)
  val injective = ISPECL [w, normalized] wordsTheory.w2n_11
in
  EQ_MP injective same_num
end
val scalar_literals_bytes_literal_terms = find_terms
  (can (match_term ``Lit (set_byte a b w be : bytes32)``))
  scalar_literals_bytes_fn
val scalar_literals_bytes_literal_words =
  List.foldl (fn (lit,ws) => let val w = #2 (dest_comb lit) in
      if List.exists (aconv w) ws then ws else w::ws end)
    [] scalar_literals_bytes_literal_terms
val scalar_literals_bytes_word_normalizations =
  map scalar_literals_bytes_normalize_word scalar_literals_bytes_literal_words
val () = computeLib.upd_compset
  (computeLib.add_thms scalar_literals_bytes_word_normalizations)
val scalar_literals_bytes_liveness_eval = save_thm
  ("scalar_literals_bytes_liveness_eval", EVAL ``liveness_analyze ^scalar_literals_bytes_fn``)
val scalar_literals_bytes_dfg_eval = save_thm
  ("scalar_literals_bytes_dfg_eval", EVAL ``dfg_build_function ^scalar_literals_bytes_fn``)
val scalar_literals_bytes_cfg_eval = save_thm
  ("scalar_literals_bytes_cfg_eval", EVAL ``cfg_analyze ^scalar_literals_bytes_fn``)
val scalar_literals_bytes_liveness = rhs (concl scalar_literals_bytes_liveness_eval)
val scalar_literals_bytes_dfg = rhs (concl scalar_literals_bytes_dfg_eval)
val scalar_literals_bytes_cfg = rhs (concl scalar_literals_bytes_cfg_eval)
val scalar_literals_bytes_max_eom_eval = EVAL
  ``max_live_eom (^scalar_literals_bytes_unit).cu_context``
val scalar_literals_bytes_max_eom = optionSyntax.dest_some
  (rhs (concl scalar_literals_bytes_max_eom_eval))
val scalar_literals_bytes_generate_fn_plan = save_thm
  ("scalar_literals_bytes_generate_fn_plan", prove
    (``∀spill labels.
        generate_fn_plan ^scalar_literals_bytes_fn spill labels =
        generate_fn_plan_analyzed ^scalar_literals_bytes_liveness
          ^scalar_literals_bytes_dfg ^scalar_literals_bytes_cfg ^scalar_literals_bytes_fn
          spill labels``,
     simp[stackPlanGenTheory.generate_fn_plan_def,
          scalar_literals_bytes_liveness_eval,
          scalar_literals_bytes_dfg_eval, scalar_literals_bytes_cfg_eval]))
val () = computeLib.upd_compset (computeLib.add_thms
  [scalar_literals_bytes_liveness_eval, scalar_literals_bytes_dfg_eval,
   scalar_literals_bytes_cfg_eval, scalar_literals_bytes_generate_fn_plan])
val scalar_literals_bytes_analyzed_plan_eval = save_thm
  ("scalar_literals_bytes_analyzed_plan_eval", EVAL
    ``generate_fn_plan_analyzed ^scalar_literals_bytes_liveness
       ^scalar_literals_bytes_dfg ^scalar_literals_bytes_cfg ^scalar_literals_bytes_fn
       ^scalar_literals_bytes_max_eom 0``)
val scalar_literals_bytes_plan = rhs (concl scalar_literals_bytes_analyzed_plan_eval)
val scalar_literals_bytes_concrete_fn_plan = save_thm
  ("scalar_literals_bytes_concrete_fn_plan", prove
    (``generate_fn_plan ^scalar_literals_bytes_fn ^scalar_literals_bytes_max_eom 0 =
        ^scalar_literals_bytes_plan``,
     simp[scalar_literals_bytes_generate_fn_plan,
          scalar_literals_bytes_analyzed_plan_eval]))
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``generate_fn_plan``)
    |> computeLib.add_thms [scalar_literals_bytes_concrete_fn_plan])
val scalar_literals_bytes_plan_value = optionSyntax.dest_some scalar_literals_bytes_plan
val scalar_literals_bytes_plan_pair = pairSyntax.dest_pair scalar_literals_bytes_plan_value
val scalar_literals_bytes_plan_ops = #1 scalar_literals_bytes_plan_pair
val scalar_literals_bytes_plan_state = #2 scalar_literals_bytes_plan_pair
val scalar_literals_bytes_spill_end_eval = EVAL
  ``(^scalar_literals_bytes_plan_state).ps_alloc.sa_next_offset``
val scalar_literals_bytes_spill_end = rhs (concl scalar_literals_bytes_spill_end_eval)
val scalar_literals_bytes_spill_safe_eval = EVAL
  ``spill_plan_in_region ^scalar_literals_bytes_max_eom
      ^scalar_literals_bytes_spill_end ^scalar_literals_bytes_plan_ops``
val scalar_literals_bytes_context_plan_step1 = SIMP_CONV (srw_ss())
  [stackPlanGenTheory.generate_context_plan_def,
   stackPlanGenTheory.generate_context_plan_with_def,
   scalar_literals_bytes_max_eom_eval,
   stackPlanGenTheory.generate_context_regions_def,
   stackPlanGenTheory.finish_context_plan_def]
  ``generate_context_plan (^scalar_literals_bytes_unit).cu_context``
val scalar_literals_bytes_context_plan_step2 =
  EVAL (rhs (concl scalar_literals_bytes_context_plan_step1))
val scalar_literals_bytes_actual_plan_call = find_term
  (can (match_term ``generate_fn_plan f spill labels``))
  (rhs (concl scalar_literals_bytes_context_plan_step2))
val scalar_literals_bytes_actual_plan_args = #2 (strip_comb scalar_literals_bytes_actual_plan_call)
val scalar_literals_bytes_actual_fn = hd scalar_literals_bytes_actual_plan_args
val scalar_literals_bytes_actual_liveness_eval =
  EVAL ``liveness_analyze ^scalar_literals_bytes_actual_fn``
val scalar_literals_bytes_actual_dfg_eval =
  EVAL ``dfg_build_function ^scalar_literals_bytes_actual_fn``
val scalar_literals_bytes_actual_cfg_eval =
  EVAL ``cfg_analyze ^scalar_literals_bytes_actual_fn``
val scalar_literals_bytes_actual_liveness =
  rhs (concl scalar_literals_bytes_actual_liveness_eval)
val scalar_literals_bytes_actual_dfg = rhs (concl scalar_literals_bytes_actual_dfg_eval)
val scalar_literals_bytes_actual_cfg = rhs (concl scalar_literals_bytes_actual_cfg_eval)
val scalar_literals_bytes_actual_plan_eval = EVAL
  ``generate_fn_plan_analyzed ^scalar_literals_bytes_actual_liveness
      ^scalar_literals_bytes_actual_dfg ^scalar_literals_bytes_actual_cfg
      ^scalar_literals_bytes_actual_fn ^scalar_literals_bytes_max_eom 0``
val scalar_literals_bytes_actual_plan = rhs (concl scalar_literals_bytes_actual_plan_eval)
val scalar_literals_bytes_actual_generate_step1 =
  REWR_CONV stackPlanGenTheory.generate_fn_plan_def
    ``generate_fn_plan ^scalar_literals_bytes_actual_fn
        ^scalar_literals_bytes_max_eom 0``
val scalar_literals_bytes_actual_generate_step2 = PURE_REWRITE_CONV
  [scalar_literals_bytes_actual_liveness_eval,
   scalar_literals_bytes_actual_dfg_eval,
   scalar_literals_bytes_actual_cfg_eval]
  (rhs (concl scalar_literals_bytes_actual_generate_step1))
val scalar_literals_bytes_actual_generate_step3 =
  REWR_CONV scalar_literals_bytes_actual_plan_eval
    (rhs (concl scalar_literals_bytes_actual_generate_step2))
val scalar_literals_bytes_actual_generate_fn_plan =
  TRANS scalar_literals_bytes_actual_generate_step1
    (TRANS scalar_literals_bytes_actual_generate_step2
      scalar_literals_bytes_actual_generate_step3)
val scalar_literals_bytes_context_plan_step3 = PURE_REWRITE_CONV
  [scalar_literals_bytes_actual_generate_fn_plan]
  (rhs (concl scalar_literals_bytes_context_plan_step2))
val scalar_literals_bytes_context_plan_eval =
  TRANS scalar_literals_bytes_context_plan_step1
    (TRANS scalar_literals_bytes_context_plan_step2
      (TRANS scalar_literals_bytes_context_plan_step3
        (EVAL (rhs (concl scalar_literals_bytes_context_plan_step3)))))
val scalar_literals_bytes_context_plan = optionSyntax.dest_some
  (rhs (concl scalar_literals_bytes_context_plan_eval))
val scalar_literals_bytes_plan = scalar_literals_bytes_actual_plan
val scalar_literals_bytes_plan_value = optionSyntax.dest_some scalar_literals_bytes_plan
val scalar_literals_bytes_plan_pair = pairSyntax.dest_pair scalar_literals_bytes_plan_value
val scalar_literals_bytes_plan_ops = #1 scalar_literals_bytes_plan_pair
val scalar_literals_bytes_ops = #1 (listSyntax.dest_list scalar_literals_bytes_plan_ops)
val scalar_literals_bytes_sopush = #1 (dest_comb
  ``SOPush (Lit (0w : bytes32))``)
val scalar_literals_bytes_lit = #1 (dest_comb ``Lit (0w : bytes32)``)
fun scalar_literals_bytes_dest_push_word tm =
  case total dest_comb tm of
    SOME (c,arg) =>
      if same_const c scalar_literals_bytes_sopush then
        (case total dest_comb arg of
           SOME (lc,w) => if same_const lc scalar_literals_bytes_lit then SOME w
                          else NONE
         | NONE => NONE)
      else NONE
  | NONE => NONE
fun scalar_literals_bytes_insert_word (w,ws) =
  if List.exists (aconv w) ws then ws else w :: ws
val scalar_literals_bytes_push_words =
  List.foldl scalar_literals_bytes_insert_word []
    (List.mapPartial scalar_literals_bytes_dest_push_word scalar_literals_bytes_ops)
val scalar_literals_bytes_w2n_evals =
  map scalar_literals_bytes_w2n_eval scalar_literals_bytes_push_words
fun scalar_literals_bytes_encode_eval w2n_th = let
  val step = BETA_RULE (AP_TERM
    ``λn. encode_num_bytes_fuel 32 n`` w2n_th)
  val concrete = EVAL (rhs (concl step))
in
  TRANS step concrete
end
val scalar_literals_bytes_encode_evals =
  map scalar_literals_bytes_encode_eval scalar_literals_bytes_w2n_evals
val scalar_literals_bytes_all_plan_ops_eval = EVAL
  ``context_plan_ops ^scalar_literals_bytes_context_plan``
val scalar_literals_bytes_all_plan_ops =
  rhs (concl scalar_literals_bytes_all_plan_ops_eval)
val scalar_literals_bytes_initial_fmp_eval = EVAL
  ``(^scalar_literals_bytes_context_plan).cp_initial_fmp``
val scalar_literals_bytes_initial_fmp =
  rhs (concl scalar_literals_bytes_initial_fmp_eval)
val (scalar_literals_bytes_plan_op_terms, _) =
  listSyntax.dest_list scalar_literals_bytes_all_plan_ops
fun scalar_literals_bytes_exec_op_eval sop = let
  val step = FIRST_CONV
    (map REWR_CONV (CONJUNCTS planExecTheory.exec_stack_op_def))
    ``exec_stack_op ^scalar_literals_bytes_initial_fmp ^sop``
  val encoded = QCONV
    (PURE_REWRITE_CONV scalar_literals_bytes_encode_evals)
    (rhs (concl step))
  val reduced = EVAL (rhs (concl encoded))
in
  TRANS step (TRANS encoded reduced)
end
val scalar_literals_bytes_exec_op_evals =
  map scalar_literals_bytes_exec_op_eval scalar_literals_bytes_plan_op_terms
val scalar_literals_bytes_execute_step = PURE_REWRITE_CONV
  ([planExecTheory.execute_plan_def, listTheory.MAP, listTheory.FLAT] @
   scalar_literals_bytes_exec_op_evals)
  ``execute_plan ^scalar_literals_bytes_initial_fmp ^scalar_literals_bytes_all_plan_ops``
val scalar_literals_bytes_execute_eval = TRANS scalar_literals_bytes_execute_step
  (EVAL (rhs (concl scalar_literals_bytes_execute_step)))
val scalar_literals_bytes_execute_context_step = SIMP_CONV pure_ss
  [scalar_literals_bytes_initial_fmp_eval, scalar_literals_bytes_all_plan_ops_eval]
  ``execute_plan (^scalar_literals_bytes_context_plan).cp_initial_fmp
      (context_plan_ops ^scalar_literals_bytes_context_plan)``
val scalar_literals_bytes_execute_context_eval =
  TRANS scalar_literals_bytes_execute_context_step scalar_literals_bytes_execute_eval
val scalar_literals_bytes_execute_asm =
  rhs (concl scalar_literals_bytes_execute_eval)
val scalar_literals_bytes_data_asm_eval = EVAL
  ``data_segment_asm (^scalar_literals_bytes_unit).cu_data_segment``
val scalar_literals_bytes_raw_asm_eval = EVAL
  ``^scalar_literals_bytes_execute_asm ++
    data_segment_asm (^scalar_literals_bytes_unit).cu_data_segment ++
    [AsmDataHeader "code_end"]``
val scalar_literals_bytes_raw_asm = rhs (concl scalar_literals_bytes_raw_asm_eval)
val scalar_literals_bytes_target_wf_eval = EVAL
  ``target_capabilities_wf (^scalar_literals_bytes_rpolicy).rpol_target``
val scalar_literals_bytes_context_safe_eval = EVAL
  ``context_target_safe (^scalar_literals_bytes_rpolicy).rpol_target
      (^scalar_literals_bytes_unit).cu_context``
val scalar_literals_bytes_assembly_safe_eval = EVAL
  ``assembly_target_safe (^scalar_literals_bytes_rpolicy).rpol_target
      ^scalar_literals_bytes_raw_asm``
val scalar_literals_bytes_codegen_step1 = SIMP_CONV pure_ss
  [codegenTheory.codegen_assembly_def,
   scalar_literals_bytes_target_wf_eval,
   scalar_literals_bytes_context_safe_eval,
   scalar_literals_bytes_context_plan_eval,
   optionTheory.option_case_compute,
   optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
   LET_THM, NOT_CLAUSES, COND_CLAUSES]
  ``codegen_assembly ^scalar_literals_bytes_rpolicy ^scalar_literals_bytes_unit``
val scalar_literals_bytes_codegen_step2 = SIMP_CONV pure_ss
  [scalar_literals_bytes_execute_context_eval,
   scalar_literals_bytes_data_asm_eval,
   scalar_literals_bytes_raw_asm_eval,
   scalar_literals_bytes_assembly_safe_eval]
  (rhs (concl scalar_literals_bytes_codegen_step1))
val scalar_literals_bytes_codegen_assembly_eval =
  TRANS scalar_literals_bytes_codegen_step1 scalar_literals_bytes_codegen_step2
val scalar_literals_bytes_runtime_accessors =
  CONJUNCTS venomCompilerTypesTheory.pipeline_output_accessors @
  CONJUNCTS venomCompilerTypesTheory.resolved_compiler_policy_accessors
Theorem scalar_literals_bytes_runtime_matches_python_oracle:
  scalar_literals_bytes_runtime_compile scalar_literals_bytes_program =
    SOME (SND ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literals_bytes.hex"))
Proof
  simp_tac pure_ss
    ([scalar_literals_bytes_runtime_compile_def,
      scalar_literals_bytes_runtime_pipeline_eval,
      optionTheory.option_case_compute,
      optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
      pairTheory.pair_case_thm, LET_THM, COND_CLAUSES,
      REFL_CLAUSE, NOT_CLAUSES,
      scalar_literals_bytes_unit_eval,
      scalar_literals_bytes_out_final_assembly_eval,
      scalar_literals_bytes_rpolicy_final_assembly_eval] @
     scalar_literals_bytes_runtime_accessors) >>
  PURE_REWRITE_TAC [codegenTheory.finalize_codegen_identity] >>
  PURE_REWRITE_TAC [scalar_literals_bytes_codegen_assembly_eval] >>
  EVAL_TAC
QED

Theorem scalar_literals_bytes_deploy_matches_python_oracle:
  scalar_literals_bytes_deploy_compile scalar_literals_bytes_program
    (SND ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literals_bytes.hex")) =
    SOME (FST ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literals_bytes.hex"))
Proof
  EVAL_TAC
QED

Theorem scalar_literals_bytes_compile_staged:
  compile_vyper (K SOME) (o1_policy all_capabilities) tops =
    case scalar_literals_bytes_runtime_compile tops of
      NONE => NONE
    | SOME runtime =>
        OPTION_MAP (λdeploy. (deploy,runtime))
          (scalar_literals_bytes_deploy_compile tops runtime)
Proof
  simp[compile_vyper_def, compile_vyper_with_def,
       scalar_literals_bytes_runtime_compile_def,
       scalar_literals_bytes_runtime_pipeline_def,
       scalar_literals_bytes_deploy_compile_def,
       checked_unit_pipeline_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem scalar_literals_bytes_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_literals_bytes_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literals_bytes.hex")
Proof
  PURE_REWRITE_TAC [scalar_literals_bytes_compile_staged] >>
  PURE_REWRITE_TAC [scalar_literals_bytes_runtime_matches_python_oracle] >>
  simp_tac pure_ss
    [optionTheory.option_case_compute,
     optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
     optionTheory.OPTION_MAP_DEF, LET_THM, COND_CLAUSES,
     scalar_literals_bytes_deploy_matches_python_oracle] >>
  EVAL_TAC
QED
