(* Exact pinned-Python bytecode parity for the external-dynamic fixture. *)

Theory evalCompilerBytecodeAbiExternalDynamic
Ancestors evalCompilerBytecodeAbiExternalDynamicPipeline evalCompilerSubsetAbiExternal compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20
val () = computeLib.upd_compset
  (computeLib.add_thms
    [word_of_bytes_be_bytes32_external_dynamic,
     word_of_bytes_bytes32_external_dynamic,
     w2n_external_dynamic_n2w,
     contextTheory.compile_copy_memory_def])

(* Stage the three analyses consumed again by stack planning.  Each theorem is
   kernel-produced from the checked pipeline result; no oracle data is used. *)
val external_dynamic_pipeline_value =
  rhs (concl external_dynamic_runtime_pipeline_eval)
val external_dynamic_rp_out = optionSyntax.dest_some external_dynamic_pipeline_value
val external_dynamic_rpolicy = #1 (pairSyntax.dest_pair external_dynamic_rp_out)
val external_dynamic_out = #2 (pairSyntax.dest_pair external_dynamic_rp_out)
val external_dynamic_unit_eval = EVAL ``(^external_dynamic_out).po_unit``
val external_dynamic_unit = rhs (concl external_dynamic_unit_eval)
val external_dynamic_out_final_assembly_eval =
  EVAL ``(^external_dynamic_out).po_final_assembly``
val external_dynamic_rpolicy_final_assembly_eval =
  EVAL ``(^external_dynamic_rpolicy).rpol_final_assembly``
val external_dynamic_fn = rhs (concl (EVAL
  ``HD (^external_dynamic_unit).cu_context.ctx_functions``))
val external_dynamic_liveness_eval = save_thm
  ("external_dynamic_liveness_eval", EVAL ``liveness_analyze ^external_dynamic_fn``)
val external_dynamic_dfg_eval = save_thm
  ("external_dynamic_dfg_eval", EVAL ``dfg_build_function ^external_dynamic_fn``)
val external_dynamic_cfg_eval = save_thm
  ("external_dynamic_cfg_eval", EVAL ``cfg_analyze ^external_dynamic_fn``)
val external_dynamic_liveness = rhs (concl external_dynamic_liveness_eval)
val external_dynamic_dfg = rhs (concl external_dynamic_dfg_eval)
val external_dynamic_cfg = rhs (concl external_dynamic_cfg_eval)
val external_dynamic_max_eom_eval = EVAL
  ``max_live_eom (^external_dynamic_unit).cu_context``
val external_dynamic_max_eom = optionSyntax.dest_some
  (rhs (concl external_dynamic_max_eom_eval))
val external_dynamic_generate_fn_plan = save_thm
  ("external_dynamic_generate_fn_plan", prove
    (``∀spill labels.
        generate_fn_plan ^external_dynamic_fn spill labels =
        generate_fn_plan_analyzed ^external_dynamic_liveness
          ^external_dynamic_dfg ^external_dynamic_cfg ^external_dynamic_fn
          spill labels``,
     simp[stackPlanGenTheory.generate_fn_plan_def,
          external_dynamic_liveness_eval,
          external_dynamic_dfg_eval, external_dynamic_cfg_eval]))
val () = computeLib.upd_compset (computeLib.add_thms
  [external_dynamic_liveness_eval, external_dynamic_dfg_eval,
   external_dynamic_cfg_eval, external_dynamic_generate_fn_plan])
val external_dynamic_analyzed_plan_eval = save_thm
  ("external_dynamic_analyzed_plan_eval", EVAL
    ``generate_fn_plan_analyzed ^external_dynamic_liveness
       ^external_dynamic_dfg ^external_dynamic_cfg ^external_dynamic_fn
       ^external_dynamic_max_eom 0``)
val external_dynamic_plan = rhs (concl external_dynamic_analyzed_plan_eval)
val external_dynamic_concrete_fn_plan = save_thm
  ("external_dynamic_concrete_fn_plan", prove
    (``generate_fn_plan ^external_dynamic_fn ^external_dynamic_max_eom 0 =
        ^external_dynamic_plan``,
     simp[external_dynamic_generate_fn_plan,
          external_dynamic_analyzed_plan_eval]))
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``generate_fn_plan``)
    |> computeLib.add_thms [external_dynamic_concrete_fn_plan])
val external_dynamic_plan_value = optionSyntax.dest_some external_dynamic_plan
val external_dynamic_plan_pair = pairSyntax.dest_pair external_dynamic_plan_value
val external_dynamic_plan_ops = #1 external_dynamic_plan_pair
val external_dynamic_plan_state = #2 external_dynamic_plan_pair
val external_dynamic_spill_end_eval = EVAL
  ``(^external_dynamic_plan_state).ps_alloc.sa_next_offset``
val external_dynamic_spill_end = rhs (concl external_dynamic_spill_end_eval)
val external_dynamic_spill_safe_eval = EVAL
  ``spill_plan_in_region ^external_dynamic_max_eom
      ^external_dynamic_spill_end ^external_dynamic_plan_ops``
val external_dynamic_context_plan_step1 = SIMP_CONV (srw_ss())
  [stackPlanGenTheory.generate_context_plan_def,
   stackPlanGenTheory.generate_context_plan_with_def,
   external_dynamic_max_eom_eval,
   stackPlanGenTheory.generate_context_regions_def,
   stackPlanGenTheory.finish_context_plan_def]
  ``generate_context_plan (^external_dynamic_unit).cu_context``
val external_dynamic_context_plan_step2 =
  EVAL (rhs (concl external_dynamic_context_plan_step1))
val external_dynamic_actual_plan_call = find_term
  (can (match_term ``generate_fn_plan f spill labels``))
  (rhs (concl external_dynamic_context_plan_step2))
val external_dynamic_actual_plan_args = #2 (strip_comb external_dynamic_actual_plan_call)
val external_dynamic_actual_fn = hd external_dynamic_actual_plan_args
val external_dynamic_actual_liveness_eval =
  EVAL ``liveness_analyze ^external_dynamic_actual_fn``
val external_dynamic_actual_dfg_eval =
  EVAL ``dfg_build_function ^external_dynamic_actual_fn``
val external_dynamic_actual_cfg_eval =
  EVAL ``cfg_analyze ^external_dynamic_actual_fn``
val external_dynamic_actual_liveness =
  rhs (concl external_dynamic_actual_liveness_eval)
val external_dynamic_actual_dfg = rhs (concl external_dynamic_actual_dfg_eval)
val external_dynamic_actual_cfg = rhs (concl external_dynamic_actual_cfg_eval)
val external_dynamic_actual_plan_eval = EVAL
  ``generate_fn_plan_analyzed ^external_dynamic_actual_liveness
      ^external_dynamic_actual_dfg ^external_dynamic_actual_cfg
      ^external_dynamic_actual_fn ^external_dynamic_max_eom 0``
val external_dynamic_actual_plan = rhs (concl external_dynamic_actual_plan_eval)
val external_dynamic_actual_generate_step1 =
  REWR_CONV stackPlanGenTheory.generate_fn_plan_def
    ``generate_fn_plan ^external_dynamic_actual_fn
        ^external_dynamic_max_eom 0``
val external_dynamic_actual_generate_step2 = PURE_REWRITE_CONV
  [external_dynamic_actual_liveness_eval,
   external_dynamic_actual_dfg_eval,
   external_dynamic_actual_cfg_eval]
  (rhs (concl external_dynamic_actual_generate_step1))
val external_dynamic_actual_generate_step3 =
  REWR_CONV external_dynamic_actual_plan_eval
    (rhs (concl external_dynamic_actual_generate_step2))
val external_dynamic_actual_generate_fn_plan =
  TRANS external_dynamic_actual_generate_step1
    (TRANS external_dynamic_actual_generate_step2
      external_dynamic_actual_generate_step3)
val external_dynamic_context_plan_step3 = PURE_REWRITE_CONV
  [external_dynamic_actual_generate_fn_plan]
  (rhs (concl external_dynamic_context_plan_step2))
val external_dynamic_context_plan_eval =
  TRANS external_dynamic_context_plan_step1
    (TRANS external_dynamic_context_plan_step2
      (TRANS external_dynamic_context_plan_step3
        (EVAL (rhs (concl external_dynamic_context_plan_step3)))))
val external_dynamic_context_plan = optionSyntax.dest_some
  (rhs (concl external_dynamic_context_plan_eval))
val external_dynamic_plan = external_dynamic_actual_plan
val external_dynamic_plan_value = optionSyntax.dest_some external_dynamic_plan
val external_dynamic_plan_pair = pairSyntax.dest_pair external_dynamic_plan_value
val external_dynamic_plan_ops = #1 external_dynamic_plan_pair
val external_dynamic_ops = #1 (listSyntax.dest_list external_dynamic_plan_ops)
val external_dynamic_sopush = #1 (dest_comb
  ``SOPush (Lit (0w : bytes32))``)
val external_dynamic_lit = #1 (dest_comb ``Lit (0w : bytes32)``)
fun external_dynamic_dest_push_word tm =
  case total dest_comb tm of
    SOME (c,arg) =>
      if same_const c external_dynamic_sopush then
        (case total dest_comb arg of
           SOME (lc,w) => if same_const lc external_dynamic_lit then SOME w
                          else NONE
         | NONE => NONE)
      else NONE
  | NONE => NONE
fun external_dynamic_insert_word (w,ws) =
  if List.exists (aconv w) ws then ws else w :: ws
val external_dynamic_push_words =
  List.foldl external_dynamic_insert_word []
    (List.mapPartial external_dynamic_dest_push_word external_dynamic_ops)
fun external_dynamic_w2n_eval w =
  if same_const (#1 (strip_comb w)) ``set_byte`` then let
    val bytes_th = SIMP_CONV (srw_ss())
      [word_to_bytes_be_bytes32_genlist_external_dynamic,
       get_byte_set_byte_bytes32_external_dynamic,
       get_byte_set_byte_irrelevant_bytes32_external_dynamic]
      ``word_to_bytes_be ^w``
    val roundtrip = INST [``w:bytes32`` |-> w]
      word_of_bytes_be_word_to_bytes_be_external_dynamic
    val step1 = BETA_RULE (AP_TERM ``λx:bytes32. w2n x``
      (SYM roundtrip))
    val step2 = BETA_RULE (AP_TERM
      ``λbs. w2n (word_of_bytes_be bs : bytes32)`` bytes_th)
    val decoded = TRANS step1 step2
    val expose = SIMP_CONV bool_ss
      [word_of_bytes_be_bytes32_external_dynamic,
       w2n_external_dynamic_n2w] (rhs (concl decoded))
    val numeral = EVAL (rhs (concl expose))
  in
    TRANS decoded (TRANS expose numeral)
  end else
    EVAL ``w2n ^w``
val external_dynamic_w2n_evals =
  map external_dynamic_w2n_eval external_dynamic_push_words
fun external_dynamic_encode_eval w2n_th = let
  val step = BETA_RULE (AP_TERM
    ``λn. encode_num_bytes_fuel 32 n`` w2n_th)
  val concrete = EVAL (rhs (concl step))
in
  TRANS step concrete
end
val external_dynamic_encode_evals =
  map external_dynamic_encode_eval external_dynamic_w2n_evals
val external_dynamic_all_plan_ops_eval = EVAL
  ``context_plan_ops ^external_dynamic_context_plan``
val external_dynamic_all_plan_ops =
  rhs (concl external_dynamic_all_plan_ops_eval)
val external_dynamic_initial_fmp_eval = EVAL
  ``(^external_dynamic_context_plan).cp_initial_fmp``
val external_dynamic_initial_fmp =
  rhs (concl external_dynamic_initial_fmp_eval)
val (external_dynamic_plan_op_terms, _) =
  listSyntax.dest_list external_dynamic_all_plan_ops
fun external_dynamic_exec_op_eval sop = let
  val step = FIRST_CONV
    (map REWR_CONV (CONJUNCTS planExecTheory.exec_stack_op_def))
    ``exec_stack_op ^external_dynamic_initial_fmp ^sop``
  val encoded = QCONV
    (PURE_REWRITE_CONV external_dynamic_encode_evals)
    (rhs (concl step))
  val reduced = EVAL (rhs (concl encoded))
in
  TRANS step (TRANS encoded reduced)
end
val external_dynamic_exec_op_evals =
  map external_dynamic_exec_op_eval external_dynamic_plan_op_terms
val external_dynamic_execute_step = PURE_REWRITE_CONV
  ([planExecTheory.execute_plan_def, listTheory.MAP, listTheory.FLAT] @
   external_dynamic_exec_op_evals)
  ``execute_plan ^external_dynamic_initial_fmp ^external_dynamic_all_plan_ops``
val external_dynamic_execute_eval = TRANS external_dynamic_execute_step
  (EVAL (rhs (concl external_dynamic_execute_step)))
val external_dynamic_execute_context_step = SIMP_CONV pure_ss
  [external_dynamic_initial_fmp_eval, external_dynamic_all_plan_ops_eval]
  ``execute_plan (^external_dynamic_context_plan).cp_initial_fmp
      (context_plan_ops ^external_dynamic_context_plan)``
val external_dynamic_execute_context_eval =
  TRANS external_dynamic_execute_context_step external_dynamic_execute_eval
val external_dynamic_execute_asm =
  rhs (concl external_dynamic_execute_eval)
val external_dynamic_data_asm_eval = EVAL
  ``data_segment_asm (^external_dynamic_unit).cu_data_segment``
val external_dynamic_raw_asm_eval = EVAL
  ``^external_dynamic_execute_asm ++
    data_segment_asm (^external_dynamic_unit).cu_data_segment ++
    [AsmDataHeader "code_end"]``
val external_dynamic_raw_asm = rhs (concl external_dynamic_raw_asm_eval)
val external_dynamic_target_wf_eval = EVAL
  ``target_capabilities_wf (^external_dynamic_rpolicy).rpol_target``
val external_dynamic_context_safe_eval = EVAL
  ``context_target_safe (^external_dynamic_rpolicy).rpol_target
      (^external_dynamic_unit).cu_context``
val external_dynamic_assembly_safe_eval = EVAL
  ``assembly_target_safe (^external_dynamic_rpolicy).rpol_target
      ^external_dynamic_raw_asm``
val external_dynamic_codegen_step1 = SIMP_CONV pure_ss
  [codegenTheory.codegen_assembly_def,
   external_dynamic_target_wf_eval,
   external_dynamic_context_safe_eval,
   external_dynamic_context_plan_eval,
   optionTheory.option_case_compute,
   optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
   LET_THM, NOT_CLAUSES, COND_CLAUSES]
  ``codegen_assembly ^external_dynamic_rpolicy ^external_dynamic_unit``
val external_dynamic_codegen_step2 = SIMP_CONV pure_ss
  [external_dynamic_execute_context_eval,
   external_dynamic_data_asm_eval,
   external_dynamic_raw_asm_eval,
   external_dynamic_assembly_safe_eval]
  (rhs (concl external_dynamic_codegen_step1))
val external_dynamic_codegen_assembly_eval =
  TRANS external_dynamic_codegen_step1 external_dynamic_codegen_step2
val external_dynamic_runtime_accessors =
  CONJUNCTS venomCompilerTypesTheory.pipeline_output_accessors @
  CONJUNCTS venomCompilerTypesTheory.resolved_compiler_policy_accessors
Theorem external_dynamic_runtime_matches_python_oracle:
  external_dynamic_runtime_compile task090_external_dynamic_program =
    SOME (SND ^(evalCompilerBytecodeLib.read_hex_bytes "external_dynamic.hex"))
Proof
  simp_tac pure_ss
    ([external_dynamic_runtime_compile_def,
      external_dynamic_runtime_pipeline_eval,
      optionTheory.option_case_compute,
      optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
      pairTheory.pair_case_thm, LET_THM, COND_CLAUSES,
      REFL_CLAUSE, NOT_CLAUSES,
      external_dynamic_unit_eval,
      external_dynamic_out_final_assembly_eval,
      external_dynamic_rpolicy_final_assembly_eval] @
     external_dynamic_runtime_accessors) >>
  PURE_REWRITE_TAC [codegenTheory.finalize_codegen_identity] >>
  PURE_REWRITE_TAC [external_dynamic_codegen_assembly_eval] >>
  EVAL_TAC
QED

Theorem external_dynamic_deploy_matches_python_oracle:
  external_dynamic_deploy_compile task090_external_dynamic_program
    (SND ^(evalCompilerBytecodeLib.read_hex_bytes "external_dynamic.hex")) =
    SOME (FST ^(evalCompilerBytecodeLib.read_hex_bytes "external_dynamic.hex"))
Proof
  EVAL_TAC
QED

Theorem external_dynamic_compile_staged:
  compile_vyper (K SOME) (o1_policy all_capabilities) tops =
    case external_dynamic_runtime_compile tops of
      NONE => NONE
    | SOME runtime =>
        OPTION_MAP (λdeploy. (deploy,runtime))
          (external_dynamic_deploy_compile tops runtime)
Proof
  simp[compile_vyper_def, compile_vyper_with_def,
       external_dynamic_runtime_compile_def,
       external_dynamic_runtime_pipeline_def,
       external_dynamic_deploy_compile_def,
       checked_unit_pipeline_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem external_dynamic_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    task090_external_dynamic_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "external_dynamic.hex")
Proof
  PURE_REWRITE_TAC [external_dynamic_compile_staged] >>
  PURE_REWRITE_TAC [external_dynamic_runtime_matches_python_oracle] >>
  simp_tac pure_ss
    [optionTheory.option_case_compute,
     optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
     optionTheory.OPTION_MAP_DEF, LET_THM, COND_CLAUSES,
     external_dynamic_deploy_matches_python_oracle] >>
  EVAL_TAC
QED
