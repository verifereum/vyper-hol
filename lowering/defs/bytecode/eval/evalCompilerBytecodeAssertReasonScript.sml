(* Exact pinned-Python bytecode parity for the reasoned-assert fixture. *)

Theory evalCompilerBytecodeAssertReason
Ancestors evalCompilerSubsetControlDeploy compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../python-o1-no-asm-opt/assert_reason.hex"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

val () = computeLib.upd_compset
  (computeLib.add_thms [contextTheory.compile_copy_memory_def])

Definition assert_reason_runtime_pipeline_def:
  assert_reason_runtime_pipeline tops =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME unit =>
            OPTION_MAP (λout. (rpolicy,out))
              (run_venom_pipeline (K T) (K T) (K T)
                 rpolicy o1_pipeline_spec unit)
End

Definition assert_reason_runtime_compile_def:
  assert_reason_runtime_compile tops =
    case assert_reason_runtime_pipeline tops of
      NONE => NONE
    | SOME (rpolicy,out) =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen (K SOME) rpolicy out.po_unit
End

Definition assert_reason_deploy_compile_def:
  assert_reason_deploy_compile tops runtime =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_deploy_unit tops rpolicy runtime of
          NONE => NONE
        | SOME unit =>
            checked_unit_pipeline
              (λrp u. run_venom_pipeline (K T) (K T) (K T)
                 rp o1_pipeline_spec u)
              (K SOME) rpolicy unit
End

val assert_reason_runtime_pipeline_eval =
  save_thm ("assert_reason_runtime_pipeline_eval",
    EVAL ``assert_reason_runtime_pipeline assert_reason_program``)

(* Stage the three analyses consumed again by stack planning.  Each theorem is
   kernel-produced from the checked pipeline result; no oracle data is used. *)
val assert_reason_pipeline_value =
  rhs (concl assert_reason_runtime_pipeline_eval)
val assert_reason_rp_out = optionSyntax.dest_some assert_reason_pipeline_value
val assert_reason_rpolicy = #1 (pairSyntax.dest_pair assert_reason_rp_out)
val assert_reason_out = #2 (pairSyntax.dest_pair assert_reason_rp_out)
val assert_reason_unit_eval = EVAL ``(^assert_reason_out).po_unit``
val assert_reason_unit = rhs (concl assert_reason_unit_eval)
val assert_reason_out_final_assembly_eval =
  EVAL ``(^assert_reason_out).po_final_assembly``
val assert_reason_rpolicy_final_assembly_eval =
  EVAL ``(^assert_reason_rpolicy).rpol_final_assembly``
val assert_reason_fn = rhs (concl (EVAL
  ``HD (^assert_reason_unit).cu_context.ctx_functions``))
val assert_reason_liveness_eval = save_thm
  ("assert_reason_liveness_eval", EVAL ``liveness_analyze ^assert_reason_fn``)
val assert_reason_dfg_eval = save_thm
  ("assert_reason_dfg_eval", EVAL ``dfg_build_function ^assert_reason_fn``)
val assert_reason_cfg_eval = save_thm
  ("assert_reason_cfg_eval", EVAL ``cfg_analyze ^assert_reason_fn``)
val assert_reason_liveness = rhs (concl assert_reason_liveness_eval)
val assert_reason_dfg = rhs (concl assert_reason_dfg_eval)
val assert_reason_cfg = rhs (concl assert_reason_cfg_eval)
val assert_reason_generate_fn_plan = save_thm
  ("assert_reason_generate_fn_plan", prove
    (``∀spill labels.
        generate_fn_plan ^assert_reason_fn spill labels =
        generate_fn_plan_analyzed ^assert_reason_liveness
          ^assert_reason_dfg ^assert_reason_cfg ^assert_reason_fn
          spill labels``,
     simp[stackPlanGenTheory.generate_fn_plan_def,
          assert_reason_liveness_eval,
          assert_reason_dfg_eval, assert_reason_cfg_eval]))
val () = computeLib.upd_compset (computeLib.add_thms
  [assert_reason_liveness_eval, assert_reason_dfg_eval,
   assert_reason_cfg_eval, assert_reason_generate_fn_plan])
val assert_reason_analyzed_plan_eval = save_thm
  ("assert_reason_analyzed_plan_eval", EVAL
    ``generate_fn_plan_analyzed ^assert_reason_liveness
       ^assert_reason_dfg ^assert_reason_cfg ^assert_reason_fn 256 0``)
val assert_reason_plan = rhs (concl assert_reason_analyzed_plan_eval)
val assert_reason_concrete_fn_plan = save_thm
  ("assert_reason_concrete_fn_plan", prove
    (``generate_fn_plan ^assert_reason_fn 256 0 = ^assert_reason_plan``,
     simp[assert_reason_generate_fn_plan,
          assert_reason_analyzed_plan_eval]))
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``generate_fn_plan``)
    |> computeLib.add_thms [assert_reason_concrete_fn_plan])
val assert_reason_context_plan_eval = SIMP_CONV (srw_ss())
  [stackPlanGenTheory.generate_context_plan_def,
   stackPlanGenTheory.generate_context_plan_with_def,
   stackPlanGenTheory.max_live_eom_def,
   stackPlanGenTheory.collect_fn_eoms_def,
   stackPlanGenTheory.generate_context_regions_def,
   stackPlanGenTheory.finish_context_plan_def,
   assert_reason_concrete_fn_plan]
  ``generate_context_plan (^assert_reason_unit).cu_context``
val assert_reason_context_plan_eval = TRANS assert_reason_context_plan_eval
  (EVAL (rhs (concl assert_reason_context_plan_eval)))
val assert_reason_context_plan = optionSyntax.dest_some
  (rhs (concl assert_reason_context_plan_eval))
val assert_reason_plan_value = optionSyntax.dest_some assert_reason_plan
val assert_reason_plan_ops = #1 (pairSyntax.dest_pair assert_reason_plan_value)
val assert_reason_ops = #1 (listSyntax.dest_list assert_reason_plan_ops)
val assert_reason_sopush = #1 (dest_comb
  ``SOPush (Lit (0w : bytes32))``)
val assert_reason_lit = #1 (dest_comb ``Lit (0w : bytes32)``)
fun assert_reason_dest_push_word tm =
  case total dest_comb tm of
    SOME (c,arg) =>
      if same_const c assert_reason_sopush then
        (case total dest_comb arg of
           SOME (lc,w) => if same_const lc assert_reason_lit then SOME w
                          else NONE
         | NONE => NONE)
      else NONE
  | NONE => NONE
fun assert_reason_insert_word (w,ws) =
  if List.exists (aconv w) ws then ws else w :: ws
val assert_reason_push_words =
  List.foldl assert_reason_insert_word []
    (List.mapPartial assert_reason_dest_push_word assert_reason_ops)
fun assert_reason_w2n_eval w = EVAL ``w2n ^w``
val assert_reason_w2n_evals =
  map assert_reason_w2n_eval assert_reason_push_words
fun assert_reason_encode_eval w2n_th = let
  val step = BETA_RULE (AP_TERM
    ``λn. encode_num_bytes_fuel 32 n`` w2n_th)
  val concrete = EVAL (rhs (concl step))
in
  TRANS step concrete
end
val assert_reason_encode_evals =
  map assert_reason_encode_eval assert_reason_w2n_evals
val assert_reason_all_plan_ops_eval = EVAL
  ``context_plan_ops ^assert_reason_context_plan``
val assert_reason_all_plan_ops =
  rhs (concl assert_reason_all_plan_ops_eval)
val assert_reason_initial_fmp_eval = EVAL
  ``(^assert_reason_context_plan).cp_initial_fmp``
val assert_reason_initial_fmp =
  rhs (concl assert_reason_initial_fmp_eval)
val (assert_reason_plan_op_terms, _) =
  listSyntax.dest_list assert_reason_all_plan_ops
fun assert_reason_exec_op_eval sop = let
  val step = FIRST_CONV
    (map REWR_CONV (CONJUNCTS planExecTheory.exec_stack_op_def))
    ``exec_stack_op ^assert_reason_initial_fmp ^sop``
  val encoded = QCONV
    (PURE_REWRITE_CONV assert_reason_encode_evals)
    (rhs (concl step))
  val reduced = EVAL (rhs (concl encoded))
in
  TRANS step (TRANS encoded reduced)
end
val assert_reason_exec_op_evals =
  map assert_reason_exec_op_eval assert_reason_plan_op_terms
val assert_reason_execute_step = PURE_REWRITE_CONV
  ([planExecTheory.execute_plan_def, listTheory.MAP, listTheory.FLAT] @
   assert_reason_exec_op_evals)
  ``execute_plan ^assert_reason_initial_fmp ^assert_reason_all_plan_ops``
val assert_reason_execute_eval = TRANS assert_reason_execute_step
  (EVAL (rhs (concl assert_reason_execute_step)))
val assert_reason_execute_context_step = SIMP_CONV pure_ss
  [assert_reason_initial_fmp_eval, assert_reason_all_plan_ops_eval]
  ``execute_plan (^assert_reason_context_plan).cp_initial_fmp
      (context_plan_ops ^assert_reason_context_plan)``
val assert_reason_execute_context_eval =
  TRANS assert_reason_execute_context_step assert_reason_execute_eval
val assert_reason_execute_asm =
  rhs (concl assert_reason_execute_eval)
val assert_reason_data_asm_eval = EVAL
  ``data_segment_asm (^assert_reason_unit).cu_data_segment``
val assert_reason_raw_asm_eval = EVAL
  ``^assert_reason_execute_asm ++
    data_segment_asm (^assert_reason_unit).cu_data_segment ++
    [AsmDataHeader "code_end"]``
val assert_reason_raw_asm = rhs (concl assert_reason_raw_asm_eval)
val assert_reason_target_wf_eval = EVAL
  ``target_capabilities_wf (^assert_reason_rpolicy).rpol_target``
val assert_reason_context_safe_eval = EVAL
  ``context_target_safe (^assert_reason_rpolicy).rpol_target
      (^assert_reason_unit).cu_context``
val assert_reason_assembly_safe_eval = EVAL
  ``assembly_target_safe (^assert_reason_rpolicy).rpol_target
      ^assert_reason_raw_asm``
val assert_reason_codegen_step1 = SIMP_CONV pure_ss
  [codegenTheory.codegen_assembly_def,
   assert_reason_target_wf_eval,
   assert_reason_context_safe_eval,
   assert_reason_context_plan_eval,
   optionTheory.option_case_compute,
   optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
   LET_THM, NOT_CLAUSES, COND_CLAUSES]
  ``codegen_assembly ^assert_reason_rpolicy ^assert_reason_unit``
val assert_reason_codegen_step2 = SIMP_CONV pure_ss
  [assert_reason_execute_context_eval,
   assert_reason_data_asm_eval,
   assert_reason_raw_asm_eval,
   assert_reason_assembly_safe_eval]
  (rhs (concl assert_reason_codegen_step1))
val assert_reason_codegen_assembly_eval =
  TRANS assert_reason_codegen_step1 assert_reason_codegen_step2
val assert_reason_runtime_accessors =
  CONJUNCTS venomCompilerTypesTheory.pipeline_output_accessors @
  CONJUNCTS venomCompilerTypesTheory.resolved_compiler_policy_accessors
val assert_reason_raw_asm_expanded_eval = CONV_RULE
  (Conv.LAND_CONV (PURE_REWRITE_CONV [assert_reason_data_asm_eval]))
  assert_reason_raw_asm_eval
Theorem assert_reason_runtime_matches_python_oracle:
  assert_reason_runtime_compile assert_reason_program =
    SOME (SND ^(evalCompilerBytecodeLib.read_hex_bytes "assert_reason.hex"))
Proof
  simp_tac pure_ss
    ([assert_reason_runtime_compile_def,
      assert_reason_runtime_pipeline_eval,
      optionTheory.option_case_compute,
      optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
      pairTheory.pair_case_thm, LET_THM, COND_CLAUSES,
      REFL_CLAUSE, NOT_CLAUSES,
      assert_reason_unit_eval,
      assert_reason_out_final_assembly_eval,
      assert_reason_rpolicy_final_assembly_eval] @
     assert_reason_runtime_accessors) >>
  PURE_REWRITE_TAC [codegenTheory.finalize_codegen_identity] >>
  PURE_REWRITE_TAC [assert_reason_codegen_assembly_eval] >>
  PURE_REWRITE_TAC [assert_reason_raw_asm_expanded_eval,
    assert_reason_assembly_safe_eval, pairTheory.SND] >>
  EVAL_TAC
QED

Theorem assert_reason_deploy_matches_python_oracle:
  assert_reason_deploy_compile assert_reason_program
    (SND ^(evalCompilerBytecodeLib.read_hex_bytes "assert_reason.hex")) =
    SOME (FST ^(evalCompilerBytecodeLib.read_hex_bytes "assert_reason.hex"))
Proof
  EVAL_TAC
QED

Theorem assert_reason_compile_staged:
  compile_vyper (K SOME) (o1_policy all_capabilities) tops =
    case assert_reason_runtime_compile tops of
      NONE => NONE
    | SOME runtime =>
        OPTION_MAP (λdeploy. (deploy,runtime))
          (assert_reason_deploy_compile tops runtime)
Proof
  simp[compile_vyper_def, compile_vyper_with_def,
       assert_reason_runtime_compile_def,
       assert_reason_runtime_pipeline_def,
       assert_reason_deploy_compile_def,
       checked_unit_pipeline_def] >>
  rpt (CASE_TAC >> gvs[])
QED

val () = evalCompilerBytecodeLib.add_staged_compile_eval
  ([assert_reason_runtime_compile_def,
    assert_reason_runtime_pipeline_eval,
    optionTheory.option_case_compute,
    optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
    pairTheory.pair_case_thm, LET_THM, COND_CLAUSES,
    REFL_CLAUSE, NOT_CLAUSES,
    assert_reason_unit_eval,
    assert_reason_out_final_assembly_eval,
    assert_reason_rpolicy_final_assembly_eval] @ assert_reason_runtime_accessors)
  [codegenTheory.finalize_codegen_identity, assert_reason_codegen_assembly_eval]
  [assert_reason_compile_staged]
  ``assert_reason_runtime_compile assert_reason_program``
  ``compile_vyper (K SOME) (o1_policy all_capabilities) assert_reason_program``

Theorem assert_reason_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    assert_reason_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "assert_reason.hex")
Proof
  EVAL_TAC
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("ASSERT_REASON_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "reasoned assertion has kernel assumptions or admission tags"
end) [("assert_reason_runtime_matches_python_oracle",assert_reason_runtime_matches_python_oracle),
       ("assert_reason_deploy_matches_python_oracle",assert_reason_deploy_matches_python_oracle),
       ("assert_reason_compile_staged",assert_reason_compile_staged),
       ("assert_reason_matches_python_oracle",assert_reason_matches_python_oracle)]
