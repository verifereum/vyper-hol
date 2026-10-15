(* Opt-in kernel-evaluator microbenchmark on actual raw fixture contexts.
   Reports five-run means for the original four conjuncts, the added budget,
   and the exact strengthened guard. Every guard result must evaluate to T. *)
Theory evalCompilerAllocationBudgetCost
Ancestors
  evalCompilerBytecodeScalarConvertDecimal
  evalCompilerBytecodeScalarConvertIntToDecimal
  evalCompilerBytecodeScalarWeiModular
  evalCompilerBytecodeAbiInternalTupleLowering
  vyperCompiler
Libs computeLib wordsLib finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset
fun raw_context th = #1 (pairSyntax.dest_pair
  (optionSyntax.dest_some (rhs (concl th))))
fun timed_eval is_guard label tm =
  let
    val begin = Time.now ()
    val results = List.tabulate (5, fn _ => EVAL tm)
    val elapsed = Time.toReal (Time.- (Time.now (), begin)) / 5.0
    val value = rhs (concl (hd results))
    val () = if not is_guard orelse aconv value ``T`` then ()
             else raise Fail ("guard did not evaluate to T: " ^ label)
  in
    print (label ^ " mean_seconds=" ^ Real.toString elapsed ^
      " result=" ^ term_to_string value ^ "\n")
  end
fun measure name ctx =
  (timed_eval false (name ^ " insts")
     ``LENGTH (FLAT (MAP fn_insts (^ctx).ctx_functions))``;
   timed_eval true (name ^ " old_guard")
     ``ALL_DISTINCT (ctx_fn_names ^ctx) /\
       wf_invoke_targets_check ^ctx /\ ctx_inst_ids_distinct ^ctx /\
       forced_alloc_inputs_check ^ctx``;
   timed_eval true (name ^ " added_budget") ``unit_alloca_budget ^ctx < dimword (:256)``;
   timed_eval false (name ^ " budget_value") ``unit_alloca_budget ^ctx``;
   timed_eval true (name ^ " exact_new_guard") ``lowering_context_ok ^ctx``)
val () = measure "scalar_convert_decimal/runtime" (raw_context
  scalar_convert_decimal_extract_context_eval)
val () = measure "scalar_convert_int_to_decimal/runtime" (raw_context
  scalar_convert_int_to_decimal_extract_context_eval)
val () = measure "scalar_modular/runtime" (raw_context
  scalar_modular_extract_context_eval)
val () = measure "internal_tuple_call/runtime" (raw_context
  internal_tuple_call_extract_context_eval)
val deploy_unit = optionSyntax.dest_some (rhs (concl scalar_modular_lower_deploy_eval))
val deploy_context = rhs (concl (EVAL ``(^deploy_unit).cu_context``))
val () = measure "scalar_modular/deploy" deploy_context
