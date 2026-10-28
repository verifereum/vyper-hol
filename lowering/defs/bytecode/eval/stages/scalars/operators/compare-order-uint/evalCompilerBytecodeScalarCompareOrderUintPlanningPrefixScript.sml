(* TOP-LEVEL: original compiler stages and computed result; no oracle bytes. *)
Theory evalCompilerBytecodeScalarCompareOrderUintPlanningPrefix
Ancestors
  evalCompilerBytecodeScalarCompareOrderUintReadiness
  evalCompilerBytecodeScalarCompareOrderUintPipeline
  evalCompilerBytecodeScalarCompareOrderUintDft
  evalCompilerBytecodeScalarCompareOrderUintPrefix
  evalCompilerBytecodeScalarCompareOrderUintSsa
  evalCompilerBytecodeScalarCompareOrderUintMemory
  evalCompilerBytecodeScalarCompareOrderUintLowering
  evalCompilerSubsetScalars evalCompilerBytecodeStages venomSupplyEval
  venomMemLivenessEval compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerPackagingEvalLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20
val () = compilerPackagingEvalLib.configure ()
val () = evalCompilerBytecodeLib.configure_pass_stages ()
val scalar_compare_order_uint_stage_goals = strip_conj (rhs (concl
  (SPEC ``scalar_compare_order_uint_program`` parity_stages_def)))
val () = if length scalar_compare_order_uint_stage_goals = 31 then ()
  else raise Fail "expected all31 original compiler stages"

val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeScalarCompareOrderUintLowering"
val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeScalarCompareOrderUintMemory"
val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeScalarCompareOrderUintSsa"
val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeScalarCompareOrderUintPrefix"
val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeScalarCompareOrderUintDft"
val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeScalarCompareOrderUintPipeline"
val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeScalarCompareOrderUintReadiness"

Theorem scalar_compare_order_uint_stage_19:
  ^(List.nth (scalar_compare_order_uint_stage_goals,19))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_compare_order_uint_stage_20:
  ^(List.nth (scalar_compare_order_uint_stage_goals,20))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_compare_order_uint_stage_21:
  ^(List.nth (scalar_compare_order_uint_stage_goals,21))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("SCALAR_COMPARE_ORDER_UINT_PLANNING_PREFIX_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "unsigned-order planning prefix has kernel assumptions or admission tags"
end) [("scalar_compare_order_uint_stage_19",scalar_compare_order_uint_stage_19),
       ("scalar_compare_order_uint_stage_20",scalar_compare_order_uint_stage_20),
       ("scalar_compare_order_uint_stage_21",scalar_compare_order_uint_stage_21)]
val () = evalCompilerBytecodeLib.pending_stage_values :=
  List.filter (fn (named,equation) => Option.isSome named orelse
    optionSyntax.is_some (rhs (concl equation)))
    (!evalCompilerBytecodeLib.pending_stage_values)
val () = evalCompilerBytecodeLib.publish_stage_values ()
val () = evalCompilerBytecodeLib.compiler_certificates := []
