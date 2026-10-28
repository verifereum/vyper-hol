(* TOP-LEVEL: cache_compile derives a closed compiler equation without oracle bytes.
   Helper: checked_eval saves kernel-checked equations for compiler boundaries. *)
structure compilerClosedFixtureEvalLib =
struct
  open HolKernel boolLib bossLib

  fun check_closed theorem = let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
  in if null (Thm.hyp theorem) andalso null axioms andalso
        List.all (fn oracle => oracle = "DISK_THM") oracles then theorem
     else raise Fail "closed compiler fixture has kernel assumptions or admission tags"
  end

  fun cache_compile prefix program = let
    fun save suffix theorem = save_thm (prefix ^ suffix,check_closed theorem)
    fun checked_eval suffix term = let
      val theorem = save suffix (computeLib.EVAL_CONV term)
      val () = print ("COMPILE_FIXTURE_STAGE " ^ prefix ^ suffix ^ " checked\n")
    in theorem end
    fun value theorem = rhs (concl theorem)
    fun some_value theorem = optionSyntax.dest_some (value theorem)
    val policy_eval = checked_eval "_policy_eval"
      ``resolve_o1_policy (o1_policy all_capabilities)``
    val policy = some_value policy_eval
    val lower_runtime_eval = checked_eval "_lower_runtime_eval"
      ``lower_vyper_runtime_unit ^program ^policy``
    val runtime_unit = some_value lower_runtime_eval
    val runtime_pipeline_eval = checked_eval "_runtime_pipeline_eval"
      ``run_venom_pipeline (K T) (K T) (K T)
          ^policy o1_pipeline_spec ^runtime_unit``
    val runtime_out = some_value runtime_pipeline_eval
    val final_runtime_unit = value (computeLib.EVAL_CONV ``(^runtime_out).po_unit``)
    val finalize_runtime_eval = checked_eval "_finalize_runtime_eval"
      ``finalize_codegen (K SOME) ^policy ^final_runtime_unit``
    val runtime_bytes = some_value finalize_runtime_eval
    val lower_deploy_eval = checked_eval "_lower_deploy_eval"
      ``lower_vyper_deploy_unit ^program ^policy ^runtime_bytes``
    val deploy_unit = some_value lower_deploy_eval
    val deploy_pipeline_eval = checked_eval "_deploy_pipeline_eval"
      ``run_venom_pipeline (K T) (K T) (K T)
          ^policy o1_pipeline_spec ^deploy_unit``
    val deploy_out = some_value deploy_pipeline_eval
    val final_deploy_unit = value (computeLib.EVAL_CONV ``(^deploy_out).po_unit``)
    val finalize_deploy_eval = checked_eval "_finalize_deploy_eval"
      ``finalize_codegen (K SOME) ^policy ^final_deploy_unit``
    val compile_step = simpLib.SIMP_CONV pureSimps.pure_ss
      [compileVyperTheory.compile_vyper_def,
       compileVyperTheory.compile_vyper_with_def,
       compileVyperTheory.checked_unit_pipeline_def,
       optionTheory.option_case_def, boolTheory.COND_CLAUSES,
       policy_eval,lower_runtime_eval,runtime_pipeline_eval,finalize_runtime_eval,
       lower_deploy_eval,deploy_pipeline_eval,finalize_deploy_eval,
       boolTheory.LET_THM,pairTheory.FST,pairTheory.SND,
       pairTheory.UNCURRY_DEF,pairTheory.pair_case_def]
      ``compile_vyper (K SOME) (o1_policy all_capabilities) ^program``
    val compile_eval = save "_compile_eval"
      (TRANS compile_step (computeLib.EVAL_CONV (value compile_step)))
    val _ = some_value compile_eval
  in evalCompilerBytecodeLib.add_compile_eval compile_eval end
end
