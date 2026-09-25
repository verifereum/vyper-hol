(* Exact pinned-Python bytecode parity for the mixed-event-types fixture. *)

Theory evalCompilerBytecodeAbiEvents
Ancestors evalCompilerBytecodeAbiEventsPipeline evalCompilerBytecodeAbiEventsLowering evalCompilerSubsetAbiEvents compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20
val () = computeLib.upd_compset
  (computeLib.add_thms
    [word_of_bytes_be_bytes32_mixed_event_types,
     word_of_bytes_bytes32_mixed_event_types,
     w2n_mixed_event_types_n2w,
     contextTheory.compile_copy_memory_def])

(* Stage the three analyses consumed again by stack planning.  Each theorem is
   kernel-produced from the checked pipeline result; no oracle data is used. *)
val mixed_event_types_pipeline_value =
  rhs (concl mixed_event_types_runtime_pipeline_eval)
val mixed_event_types_rp_out = optionSyntax.dest_some mixed_event_types_pipeline_value
val mixed_event_types_rpolicy = #1 (pairSyntax.dest_pair mixed_event_types_rp_out)
val mixed_event_types_out = #2 (pairSyntax.dest_pair mixed_event_types_rp_out)
val mixed_event_types_unit_eval = EVAL ``(^mixed_event_types_out).po_unit``
val mixed_event_types_unit = rhs (concl mixed_event_types_unit_eval)
val mixed_event_types_out_final_assembly_eval =
  EVAL ``(^mixed_event_types_out).po_final_assembly``
val mixed_event_types_rpolicy_final_assembly_eval =
  EVAL ``(^mixed_event_types_rpolicy).rpol_final_assembly``
val mixed_event_types_fn = rhs (concl (EVAL
  ``HD (^mixed_event_types_unit).cu_context.ctx_functions``))
val mixed_event_types_liveness_eval = save_thm
  ("mixed_event_types_liveness_eval", EVAL ``liveness_analyze ^mixed_event_types_fn``)
val mixed_event_types_dfg_eval = save_thm
  ("mixed_event_types_dfg_eval", EVAL ``dfg_build_function ^mixed_event_types_fn``)
val mixed_event_types_cfg_eval = save_thm
  ("mixed_event_types_cfg_eval", EVAL ``cfg_analyze ^mixed_event_types_fn``)
val mixed_event_types_liveness = rhs (concl mixed_event_types_liveness_eval)
val mixed_event_types_dfg = rhs (concl mixed_event_types_dfg_eval)
val mixed_event_types_cfg = rhs (concl mixed_event_types_cfg_eval)
val mixed_event_types_max_eom_eval = EVAL
  ``max_live_eom (^mixed_event_types_unit).cu_context``
val mixed_event_types_max_eom = optionSyntax.dest_some
  (rhs (concl mixed_event_types_max_eom_eval))
val mixed_event_types_generate_fn_plan = save_thm
  ("mixed_event_types_generate_fn_plan", prove
    (``∀spill labels.
        generate_fn_plan ^mixed_event_types_fn spill labels =
        generate_fn_plan_analyzed ^mixed_event_types_liveness
          ^mixed_event_types_dfg ^mixed_event_types_cfg ^mixed_event_types_fn
          spill labels``,
     simp[stackPlanGenTheory.generate_fn_plan_def,
          mixed_event_types_liveness_eval,
          mixed_event_types_dfg_eval, mixed_event_types_cfg_eval]))
val () = computeLib.upd_compset (computeLib.add_thms
  [mixed_event_types_liveness_eval, mixed_event_types_dfg_eval,
   mixed_event_types_cfg_eval, mixed_event_types_generate_fn_plan])
val mixed_event_types_analyzed_plan_eval = save_thm
  ("mixed_event_types_analyzed_plan_eval", EVAL
    ``generate_fn_plan_analyzed ^mixed_event_types_liveness
       ^mixed_event_types_dfg ^mixed_event_types_cfg ^mixed_event_types_fn
       ^mixed_event_types_max_eom 0``)
val mixed_event_types_plan = rhs (concl mixed_event_types_analyzed_plan_eval)
val mixed_event_types_concrete_fn_plan = save_thm
  ("mixed_event_types_concrete_fn_plan", prove
    (``generate_fn_plan ^mixed_event_types_fn ^mixed_event_types_max_eom 0 =
        ^mixed_event_types_plan``,
     simp[mixed_event_types_generate_fn_plan,
          mixed_event_types_analyzed_plan_eval]))
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``generate_fn_plan``)
    |> computeLib.add_thms [mixed_event_types_concrete_fn_plan])
val mixed_event_types_plan_value = optionSyntax.dest_some mixed_event_types_plan
val mixed_event_types_plan_pair = pairSyntax.dest_pair mixed_event_types_plan_value
val mixed_event_types_plan_ops = #1 mixed_event_types_plan_pair
val mixed_event_types_plan_state = #2 mixed_event_types_plan_pair
val mixed_event_types_spill_end_eval = EVAL
  ``(^mixed_event_types_plan_state).ps_alloc.sa_next_offset``
val mixed_event_types_spill_end = rhs (concl mixed_event_types_spill_end_eval)
val mixed_event_types_spill_safe_eval = EVAL
  ``spill_plan_in_region ^mixed_event_types_max_eom
      ^mixed_event_types_spill_end ^mixed_event_types_plan_ops``
val mixed_event_types_context_plan_step1 = SIMP_CONV (srw_ss())
  [stackPlanGenTheory.generate_context_plan_def,
   stackPlanGenTheory.generate_context_plan_with_def,
   mixed_event_types_max_eom_eval,
   stackPlanGenTheory.generate_context_regions_def,
   stackPlanGenTheory.finish_context_plan_def]
  ``generate_context_plan (^mixed_event_types_unit).cu_context``
val mixed_event_types_context_plan_step2 =
  EVAL (rhs (concl mixed_event_types_context_plan_step1))
val mixed_event_types_actual_plan_call = find_term
  (can (match_term ``generate_fn_plan f spill labels``))
  (rhs (concl mixed_event_types_context_plan_step2))
val mixed_event_types_actual_plan_args = #2 (strip_comb mixed_event_types_actual_plan_call)
val mixed_event_types_actual_fn = hd mixed_event_types_actual_plan_args
val mixed_event_types_actual_liveness_eval =
  EVAL ``liveness_analyze ^mixed_event_types_actual_fn``
val mixed_event_types_actual_dfg_eval =
  EVAL ``dfg_build_function ^mixed_event_types_actual_fn``
val mixed_event_types_actual_cfg_eval =
  EVAL ``cfg_analyze ^mixed_event_types_actual_fn``
val mixed_event_types_actual_liveness =
  rhs (concl mixed_event_types_actual_liveness_eval)
val mixed_event_types_actual_dfg = rhs (concl mixed_event_types_actual_dfg_eval)
val mixed_event_types_actual_cfg = rhs (concl mixed_event_types_actual_cfg_eval)
val mixed_event_types_actual_plan_eval = EVAL
  ``generate_fn_plan_analyzed ^mixed_event_types_actual_liveness
      ^mixed_event_types_actual_dfg ^mixed_event_types_actual_cfg
      ^mixed_event_types_actual_fn ^mixed_event_types_max_eom 0``
val mixed_event_types_actual_plan = rhs (concl mixed_event_types_actual_plan_eval)
val mixed_event_types_actual_generate_step1 =
  REWR_CONV stackPlanGenTheory.generate_fn_plan_def
    ``generate_fn_plan ^mixed_event_types_actual_fn
        ^mixed_event_types_max_eom 0``
val mixed_event_types_actual_generate_step2 = PURE_REWRITE_CONV
  [mixed_event_types_actual_liveness_eval,
   mixed_event_types_actual_dfg_eval,
   mixed_event_types_actual_cfg_eval]
  (rhs (concl mixed_event_types_actual_generate_step1))
val mixed_event_types_actual_generate_step3 =
  REWR_CONV mixed_event_types_actual_plan_eval
    (rhs (concl mixed_event_types_actual_generate_step2))
val mixed_event_types_actual_generate_fn_plan =
  TRANS mixed_event_types_actual_generate_step1
    (TRANS mixed_event_types_actual_generate_step2
      mixed_event_types_actual_generate_step3)
val mixed_event_types_context_plan_step3 = PURE_REWRITE_CONV
  [mixed_event_types_actual_generate_fn_plan]
  (rhs (concl mixed_event_types_context_plan_step2))
val mixed_event_types_context_plan_eval =
  TRANS mixed_event_types_context_plan_step1
    (TRANS mixed_event_types_context_plan_step2
      (TRANS mixed_event_types_context_plan_step3
        (EVAL (rhs (concl mixed_event_types_context_plan_step3)))))
val mixed_event_types_context_plan = optionSyntax.dest_some
  (rhs (concl mixed_event_types_context_plan_eval))
val mixed_event_types_plan = mixed_event_types_actual_plan
val mixed_event_types_plan_value = optionSyntax.dest_some mixed_event_types_plan
val mixed_event_types_plan_pair = pairSyntax.dest_pair mixed_event_types_plan_value
val mixed_event_types_plan_ops = #1 mixed_event_types_plan_pair
val mixed_event_types_ops = #1 (listSyntax.dest_list mixed_event_types_plan_ops)
val mixed_event_types_sopush = #1 (dest_comb
  ``SOPush (Lit (0w : bytes32))``)
val mixed_event_types_lit = #1 (dest_comb ``Lit (0w : bytes32)``)
fun mixed_event_types_dest_push_word tm =
  case total dest_comb tm of
    SOME (c,arg) =>
      if same_const c mixed_event_types_sopush then
        (case total dest_comb arg of
           SOME (lc,w) => if same_const lc mixed_event_types_lit then SOME w
                          else NONE
         | NONE => NONE)
      else NONE
  | NONE => NONE
fun mixed_event_types_insert_word (w,ws) =
  if List.exists (aconv w) ws then ws else w :: ws
val mixed_event_types_push_words =
  List.foldl mixed_event_types_insert_word []
    (List.mapPartial mixed_event_types_dest_push_word mixed_event_types_ops)
fun mixed_event_types_w2n_eval w =
  if same_const (#1 (strip_comb w)) ``set_byte`` then let
    val bytes_th = SIMP_CONV (srw_ss())
      [word_to_bytes_be_bytes32_genlist_mixed_event_types,
       get_byte_set_byte_bytes32_mixed_event_types,
       get_byte_set_byte_irrelevant_bytes32_mixed_event_types]
      ``word_to_bytes_be ^w``
    val roundtrip = INST [``w:bytes32`` |-> w]
      word_of_bytes_be_word_to_bytes_be_mixed_event_types
    val step1 = BETA_RULE (AP_TERM ``λx:bytes32. w2n x``
      (SYM roundtrip))
    val step2 = BETA_RULE (AP_TERM
      ``λbs. w2n (word_of_bytes_be bs : bytes32)`` bytes_th)
    val decoded = TRANS step1 step2
    val expose = SIMP_CONV bool_ss
      [word_of_bytes_be_bytes32_mixed_event_types,
       w2n_mixed_event_types_n2w] (rhs (concl decoded))
    val numeral = EVAL (rhs (concl expose))
  in
    TRANS decoded (TRANS expose numeral)
  end else
    EVAL ``w2n ^w``
val mixed_event_types_w2n_evals =
  map mixed_event_types_w2n_eval mixed_event_types_push_words
fun mixed_event_types_encode_eval w2n_th = let
  val step = BETA_RULE (AP_TERM
    ``λn. encode_num_bytes_fuel 32 n`` w2n_th)
  val concrete = EVAL (rhs (concl step))
in
  TRANS step concrete
end
val mixed_event_types_encode_evals =
  map mixed_event_types_encode_eval mixed_event_types_w2n_evals
val mixed_event_types_all_plan_ops_eval = EVAL
  ``context_plan_ops ^mixed_event_types_context_plan``
val mixed_event_types_all_plan_ops =
  rhs (concl mixed_event_types_all_plan_ops_eval)
val mixed_event_types_initial_fmp_eval = EVAL
  ``(^mixed_event_types_context_plan).cp_initial_fmp``
val mixed_event_types_initial_fmp =
  rhs (concl mixed_event_types_initial_fmp_eval)
val (mixed_event_types_plan_op_terms, _) =
  listSyntax.dest_list mixed_event_types_all_plan_ops
fun mixed_event_types_exec_op_eval sop = let
  val step = FIRST_CONV
    (map REWR_CONV (CONJUNCTS planExecTheory.exec_stack_op_def))
    ``exec_stack_op ^mixed_event_types_initial_fmp ^sop``
  val encoded = QCONV
    (PURE_REWRITE_CONV mixed_event_types_encode_evals)
    (rhs (concl step))
  val reduced = EVAL (rhs (concl encoded))
in
  TRANS step (TRANS encoded reduced)
end
val mixed_event_types_exec_op_evals =
  map mixed_event_types_exec_op_eval mixed_event_types_plan_op_terms
val mixed_event_types_execute_step = PURE_REWRITE_CONV
  ([planExecTheory.execute_plan_def, listTheory.MAP, listTheory.FLAT] @
   mixed_event_types_exec_op_evals)
  ``execute_plan ^mixed_event_types_initial_fmp ^mixed_event_types_all_plan_ops``
val mixed_event_types_execute_eval = TRANS mixed_event_types_execute_step
  (EVAL (rhs (concl mixed_event_types_execute_step)))
val mixed_event_types_execute_context_step = SIMP_CONV pure_ss
  [mixed_event_types_initial_fmp_eval, mixed_event_types_all_plan_ops_eval]
  ``execute_plan (^mixed_event_types_context_plan).cp_initial_fmp
      (context_plan_ops ^mixed_event_types_context_plan)``
val mixed_event_types_execute_context_eval =
  TRANS mixed_event_types_execute_context_step mixed_event_types_execute_eval
val mixed_event_types_execute_asm =
  rhs (concl mixed_event_types_execute_eval)
val mixed_event_types_data_asm_eval = EVAL
  ``data_segment_asm (^mixed_event_types_unit).cu_data_segment``
val mixed_event_types_raw_asm_eval = EVAL
  ``^mixed_event_types_execute_asm ++
    data_segment_asm (^mixed_event_types_unit).cu_data_segment ++
    [AsmDataHeader "code_end"]``
val mixed_event_types_raw_asm = rhs (concl mixed_event_types_raw_asm_eval)
val mixed_event_types_target_wf_eval = EVAL
  ``target_capabilities_wf (^mixed_event_types_rpolicy).rpol_target``
val mixed_event_types_context_safe_eval = EVAL
  ``context_target_safe (^mixed_event_types_rpolicy).rpol_target
      (^mixed_event_types_unit).cu_context``
val mixed_event_types_assembly_safe_eval = EVAL
  ``assembly_target_safe (^mixed_event_types_rpolicy).rpol_target
      ^mixed_event_types_raw_asm``
val mixed_event_types_codegen_step1 = SIMP_CONV pure_ss
  [codegenTheory.codegen_assembly_def,
   mixed_event_types_target_wf_eval,
   mixed_event_types_context_safe_eval,
   mixed_event_types_context_plan_eval,
   optionTheory.option_case_compute,
   optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
   LET_THM, NOT_CLAUSES, COND_CLAUSES]
  ``codegen_assembly ^mixed_event_types_rpolicy ^mixed_event_types_unit``
val mixed_event_types_codegen_step2 = SIMP_CONV pure_ss
  [mixed_event_types_execute_context_eval,
   mixed_event_types_data_asm_eval,
   mixed_event_types_raw_asm_eval,
   mixed_event_types_assembly_safe_eval]
  (rhs (concl mixed_event_types_codegen_step1))
val mixed_event_types_codegen_assembly_eval =
  TRANS mixed_event_types_codegen_step1 mixed_event_types_codegen_step2
val mixed_event_types_runtime_accessors =
  CONJUNCTS venomCompilerTypesTheory.pipeline_output_accessors @
  CONJUNCTS venomCompilerTypesTheory.resolved_compiler_policy_accessors
Theorem mixed_event_types_runtime_matches_python_oracle:
  mixed_event_types_runtime_compile task090_mixed_event_types_program =
    SOME (SND ^(evalCompilerBytecodeLib.read_hex_bytes "mixed_event_types.hex"))
Proof
  simp_tac pure_ss
    ([mixed_event_types_runtime_compile_def,
      mixed_event_types_runtime_pipeline_eval,
      optionTheory.option_case_compute,
      optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
      pairTheory.pair_case_thm, LET_THM, COND_CLAUSES,
      REFL_CLAUSE, NOT_CLAUSES,
      mixed_event_types_unit_eval,
      mixed_event_types_out_final_assembly_eval,
      mixed_event_types_rpolicy_final_assembly_eval] @
     mixed_event_types_runtime_accessors) >>
  PURE_REWRITE_TAC [codegenTheory.finalize_codegen_identity] >>
  PURE_REWRITE_TAC [mixed_event_types_codegen_assembly_eval] >>
  EVAL_TAC
QED

Theorem mixed_event_types_deploy_matches_python_oracle:
  mixed_event_types_deploy_compile task090_mixed_event_types_program
    (SND ^(evalCompilerBytecodeLib.read_hex_bytes "mixed_event_types.hex")) =
    SOME (FST ^(evalCompilerBytecodeLib.read_hex_bytes "mixed_event_types.hex"))
Proof
  EVAL_TAC
QED

Theorem mixed_event_types_compile_staged:
  compile_vyper (K SOME) (o1_policy all_capabilities) tops =
    case mixed_event_types_runtime_compile tops of
      NONE => NONE
    | SOME runtime =>
        OPTION_MAP (λdeploy. (deploy,runtime))
          (mixed_event_types_deploy_compile tops runtime)
Proof
  simp[compile_vyper_def, compile_vyper_with_def,
       mixed_event_types_runtime_compile_def,
       mixed_event_types_runtime_pipeline_def,
       mixed_event_types_deploy_compile_def,
       checked_unit_pipeline_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem mixed_event_types_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    task090_mixed_event_types_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "mixed_event_types.hex")
Proof
  PURE_REWRITE_TAC [mixed_event_types_compile_staged] >>
  PURE_REWRITE_TAC [mixed_event_types_runtime_matches_python_oracle] >>
  simp_tac pure_ss
    [optionTheory.option_case_compute,
     optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
     optionTheory.OPTION_MAP_DEF, LET_THM, COND_CLAUSES,
     mixed_event_types_deploy_matches_python_oracle] >>
  EVAL_TAC
QED
