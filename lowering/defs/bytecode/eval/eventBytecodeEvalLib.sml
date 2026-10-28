(* Stage checked compiler evaluation independently of the expected bytecode.
   Every registered equality is kernel-derived; oracle bytes are used only in
   the final parity claims. No compiler guard is removed or assumed. *)
structure eventBytecodeEvalLib = struct

open HolKernel

fun compile_stages stem program = let
  val _ = computeLib.upd_compset intReduce.add_int_compset
  val _ = computeLib.upd_compset
    (computeLib.add_thms [contextTheory.compile_copy_memory_def])
  (* Stop at each real dispatcher call. Prove that call separately, rewrite
     its result, then resume the checked driver with all guards intact. *)
  fun pipeline_eval label tm = let
    val dispatcher = prim_mk_const
      {Thy = "venomPassDispatcher", Name = "execute_configured_fn_pass"}
    fun pending term = let val (head,args) = strip_comb term in
      same_const head dispatcher andalso length args = 5 andalso null (free_vars term)
    end handle HOL_ERR _ => false
    fun advance n previous = let
      val reduced = TRANS previous
        (computeLib.RESTR_EVAL_CONV [dispatcher] (boolSyntax.rhs (concl previous)))
      val value = boolSyntax.rhs (concl reduced)
    in
      if optionSyntax.is_some value orelse optionSyntax.is_none value then reduced
      else case total (find_term pending) value of
        NONE => raise Fail ("event pipeline has an unexpected residual: " ^ label)
      | SOME call => let
          val started = Time.now ()
          val name = stem ^ "_" ^ label ^ "_pass_" ^ Int.toString n
          val _ = print ("EVENT dispatcher certificate " ^ name ^ "\n")
          val step = save_thm (name, bossLib.EVAL call)
          val rewritten = Rewrite.PURE_REWRITE_CONV [step] value
          val _ = print ("EVENT dispatcher elapsed " ^
            Time.toString (Time.- (Time.now (), started)) ^ "s\n")
        in
          if aconv value (boolSyntax.rhs (concl rewritten)) then
            raise Fail "event dispatcher certificate did not rewrite its call"
          else advance (n + 1) (TRANS reduced rewritten)
        end
    end
  in advance 0 (REFL tm) end
  fun stage label tm = let
    val started = Time.now ()
    val _ = print ("EVENT compiler stage " ^ stem ^ " " ^ label ^ "\n")
    val th = save_thm (stem ^ "_" ^ label,
      if String.isSuffix "_pipeline_eval" label then pipeline_eval label tm
      else bossLib.EVAL tm)
    val _ = if null (hyp th) andalso
        List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
      then () else raise Fail ("event compiler certificate: " ^ label)
    val _ = evalCompilerBytecodeLib.add_compile_eval th
    val _ = print ("EVENT compiler stage elapsed " ^
      Time.toString (Time.- (Time.now (), started)) ^ "s\n")
  in boolSyntax.rhs (concl th) end
  val policy = optionSyntax.dest_some (stage "policy_eval"
    ``resolve_o1_policy (o1_policy all_capabilities)``)
  fun finish phase unit = let
    val out = optionSyntax.dest_some (stage (phase ^ "_pipeline_eval")
      ``run_venom_pipeline (K T) (K T) (K T) ^policy o1_pipeline_spec ^unit``)
    val out_unit = boolSyntax.rhs (concl (bossLib.EVAL ``(^out).po_unit``))
    val result = stage (phase ^ "_codegen_eval")
      ``finalize_codegen (K SOME) ^policy ^out_unit``
  in
    if optionSyntax.is_some result then optionSyntax.dest_some result
    else let
      val plan = stage (phase ^ "_plan_diagnostic")
        ``generate_context_plan (^out_unit).cu_context``
      val _ = print ("EVENT codegen plan: " ^
        (if optionSyntax.is_some plan then "SOME\n"
         else if optionSyntax.is_none plan then "NONE\n" else "RESIDUAL\n"))
      val _ = if optionSyntax.is_none plan then () else let
        val cp = optionSyntax.dest_some plan
        val unsafe = stage (phase ^ "_unsafe_assembly_diagnostic")
          ``FILTER (\inst. ~asm_inst_target_safe (^policy).rpol_target inst)
            (execute_plan (^cp).cp_initial_fmp (context_plan_ops ^cp) ++
             data_segment_asm (^out_unit).cu_data_segment ++ [AsmDataHeader "code_end"])``
      in print ("EVENT unsafe assembly: " ^ Parse.term_to_string unsafe ^ "\n") end
    in raise Fail (stem ^ " " ^ phase ^
      (if optionSyntax.is_none result then ": checked code generation returned NONE"
       else ": code generation evaluation left a residual term")) end
  end
  val runtime_unit = optionSyntax.dest_some (stage "runtime_lower_eval"
    ``lower_vyper_runtime_unit ^program ^policy``)
  val runtime = finish "runtime" runtime_unit
  val deploy_unit = optionSyntax.dest_some (stage "deploy_lower_eval"
    ``lower_vyper_deploy_unit ^program ^policy ^runtime``)
  val _ = finish "deploy" deploy_unit
in () end

end
